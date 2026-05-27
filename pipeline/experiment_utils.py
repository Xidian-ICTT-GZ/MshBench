from __future__ import annotations

import hashlib
import json
import re
import time
from pathlib import Path
from typing import Dict, List, Tuple

import requests

from .llm_spec_config import ModelConfig

MAX_LLM_HTTP_RETRIES = 3


def is_spec_line(line: str, in_block: bool) -> Tuple[bool, bool]:
    stripped = line.lstrip()
    if in_block:
        if "@*/" in line:
            return True, False
        return True, True

    if stripped.startswith("//@"):
        return True, False
    if "/*@" in line:
        return True, "@*/" not in line
    return False, False


def split_spec_and_code(text: str) -> Tuple[List[str], List[str]]:
    spec_lines: List[str] = []
    code_lines: List[str] = []
    in_block = False
    for line in text.splitlines(keepends=True):
        is_spec, in_block = is_spec_line(line, in_block)
        if is_spec:
            spec_lines.append(line)
        else:
            code_lines.append(line)
    return spec_lines, code_lines


def recompose_candidate_with_source(source_code: str, candidate_text: str) -> str:
    # If model produced no candidate text, fall back to the original source (no-spec)
    if not candidate_text.strip():
        # Ensure source ends with a newline
        return source_code if source_code.endswith("\n") else source_code + "\n"

    src_non_spec = split_spec_and_code(source_code)[1]
    src_idx = 0
    in_block = False
    out: List[str] = []

    for line in candidate_text.splitlines(keepends=True):
        is_spec, in_block = is_spec_line(line, in_block)
        if is_spec:
            if src_idx >= len(src_non_spec):
                continue
            out.append(line)
            continue

        if src_idx < len(src_non_spec):
            out.append(src_non_spec[src_idx])
            src_idx += 1

    while src_idx < len(src_non_spec):
        out.append(src_non_spec[src_idx])
        src_idx += 1

    merged = "".join(out)
    if not merged.endswith("\n"):
        merged += "\n"
    return merged


def clean_llm_output(text: str) -> str:
    text = re.sub(r"```[a-zA-Z0-9_+-]*\n?", "", text)
    text = text.replace("```", "")
    return text.strip() + "\n"


def count_contracts_and_true_contracts(text: str) -> Tuple[int, int]:
    contracts = re.findall(r"^[ \t]*//@[ \t]*(requires|ensures)[ \t]+[^\n;]+;", text, flags=re.MULTILINE)
    true_contracts = re.findall(
        r"^[ \t]*//@[ \t]*(requires|ensures)[ \t]+true[ \t]*;",
        text,
        flags=re.MULTILINE | re.IGNORECASE,
    )
    return len(contracts), len(true_contracts)


def has_structured_spec_markers(text: str) -> bool:
    patterns = [
        r"^[ \t]*/\*@",
        r"^[ \t]*//@[ \t]*(invariant|inv)[ \t]+",
        r"^[ \t]*//@[ \t]*(open|close|assert|lemma|pred|predicate)[ \t]+",
    ]
    return any(re.search(p, text, flags=re.MULTILINE | re.IGNORECASE) for p in patterns)


def candidate_quality_issue(source_code: str, candidate_text: str, language: str = "all") -> str | None:
    if not candidate_text.strip():
        return "empty output"

    contract_total, true_total = count_contracts_and_true_contracts(candidate_text)
    true_ratio = true_total / contract_total if contract_total > 0 else 0.0

    if language.lower() == "java":
        if contract_total >= 2 and true_ratio >= 0.5:
            return "java: too many trivial true contracts (>=50%)"
        if contract_total >= 3 and not has_structured_spec_markers(candidate_text):
            return "java: lacks structured spec markers"
        if contract_total > 0 and true_total >= contract_total:
            return "java: all contracts are trivial true"
        if contract_total >= 4 and true_ratio >= 0.8:
            return "most contracts are trivial true (>80%)"
        if contract_total >= 4 and true_total == contract_total and not has_structured_spec_markers(candidate_text):
            return "all contracts are trivial true without structured specs"

    return None


def build_recovery_suffix(source_code: str, reason: str) -> str:
    return (
        "\n\n[Recovery Mode: strict output constraints]"
        "\nThe previous output was rejected."
        f"\nReject reason: {reason}"
        "\nYou MUST output one complete source file (no markdown)."
        "\nYou MUST preserve all non-spec code byte-for-byte."
        "\nYou MUST NOT output empty content."
        "\nYou MUST include at least one structured spec marker (predicate/invariant/open/close/assert) when applicable."
        "\nIf unsure, keep original code and add conservative but non-trivial contracts."
        "\n\n[Original Source: must preserve non-spec code exactly]"
        "\n<<<SOURCE\n"
        + source_code
        + "\nSOURCE>>>\n"
    )


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def prompt_variant(model: ModelConfig, prompt: str, candidate_index: int) -> str:
    if model.sampling_mode == "prompt_perturbation":
        return prompt + f"\n\nIndependent candidate index: {candidate_index}.\n"
    return prompt


def decoding_settings_text(model: ModelConfig, candidate_index: int) -> str:
    return json.dumps(
        {
            "model": model.model_name,
            "temperature": model.temperature,
            "top_p": model.top_p,
            "max_tokens": model.max_tokens,
            "seed": model.seed,
            "sampling_mode": model.sampling_mode,
            "candidate_index": candidate_index,
        },
        sort_keys=True,
    )


def api_settings(model: ModelConfig, env: Dict[str, str]) -> Tuple[str, str]:
    url = env.get(model.api_url_env, env.get("OPENAI_API_URL", env.get("API_URL", "")))
    key = env.get(model.api_key_env, env.get("OPENAI_API_KEY", env.get("API_KEY", "")))
    if not url or not key:
        raise RuntimeError("Missing API URL or API key environment variables.")
    return url, key


def call_llm(url: str, key: str, model: ModelConfig, prompt: str, candidate_index: int, timeout_sec: int) -> Tuple[str, Dict[str, int]]:
    payload: Dict[str, object] = {
        "model": model.model_name,
        "messages": [{"role": "user", "content": prompt}],
        "temperature": model.temperature,
        "top_p": model.top_p,
        "max_tokens": model.max_tokens,
        "presence_penalty": model.presence_penalty,
        "frequency_penalty": model.frequency_penalty,
    }
    if model.seed is not None:
        payload["seed"] = int(model.seed) + candidate_index

    last_error: Exception | None = None
    for attempt in range(1, MAX_LLM_HTTP_RETRIES + 1):
        try:
            resp = requests.post(
                url,
                headers={"Authorization": f"Bearer {key}", "Content-Type": "application/json"},
                json=payload,
                timeout=timeout_sec,
            )
            resp.raise_for_status()
            data = resp.json()
            # Support multiple response shapes safely
            content = ""
            try:
                content = data["choices"][0]["message"].get("content", "")
            except Exception:
                try:
                    content = data["choices"][0].get("text", "")
                except Exception:
                    content = ""

            usage = data.get("usage") or {}

            # Treat empty or whitespace-only content as a transient failure to retry
            if not content or not str(content).strip():
                raise ValueError("Empty content from LLM")

            return str(content), {
                "prompt_tokens": int(usage.get("prompt_tokens", 0)),
                "completion_tokens": int(usage.get("completion_tokens", 0)),
                "total_tokens": int(usage.get("total_tokens", 0)),
            }
        except (requests.RequestException, KeyError, ValueError, IndexError, TypeError) as exc:
            last_error = exc
            if attempt >= MAX_LLM_HTTP_RETRIES:
                break
            backoff_sec = min(8, 2 ** (attempt - 1))
            time.sleep(backoff_sec)

    # After retries, do not raise; return a visible placeholder so output files are not empty
    msg = f"<LLM_ERROR_OR_EMPTY after {MAX_LLM_HTTP_RETRIES} attempts: {last_error}>"
    return msg, {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0}


def run_verifast(path: Path, language: str, args_by_lang: Dict[str, List[str]], timeout_sec: int) -> Dict[str, object]:
    cmd = ["verifast", *args_by_lang.get(language, []), str(path)]
    import subprocess

    proc = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout_sec,
        cwd=str(path.parent),
    )
    stdout = (proc.stdout or b"").decode("utf-8", errors="ignore").strip()
    stderr = (proc.stderr or b"").decode("utf-8", errors="ignore").strip()
    output = "\n".join([s for s in [stdout, stderr] if s])

    if language == "java":
        verified = "0 errors found" in stdout or "0 errors found" in stderr
    else:
        verified = proc.returncode == 0

    return {
        "verified": verified,
        "stdout": stdout,
        "stderr": stderr,
        "command": cmd,
        "output": output,
        "returncode": proc.returncode,
    }


def parse_verifast_output(text: str) -> Dict[str, bool]:
    lower = text.lower()
    parse_error_markers = ["parse error", "syntax error", "unexpected token", "unexpected end of file"]
    type_error_markers = ["type error", "cannot unify", "mismatch", "unknown identifier", "not in scope"]
    parse_ok = not any(marker in lower for marker in parse_error_markers)
    type_ok = parse_ok and not any(marker in lower for marker in type_error_markers)
    return {"parse_ok": parse_ok, "type_ok": type_ok}


def save_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def save_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")


def now_timestamp(prefix: str = "output") -> str:
    return time.strftime(f"{prefix}_%Y%m%d_%H%M%S")
