from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import requests

MAX_CANDIDATE_RETRIES = 3
MAX_FALLBACK_RETRIES = 2
MAX_LLM_HTTP_RETRIES = 3

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))
    from pipeline.llm_spec_config import BenchmarkRecord, ExperimentConfig, ModelConfig, infer_language, load_config, load_manifest  # type: ignore
    from pipeline.llm_spec_prompts import build_prompt, build_repair_prompt  # type: ignore
else:
    from .llm_spec_config import BenchmarkRecord, ExperimentConfig, ModelConfig, infer_language, load_config, load_manifest
    from .llm_spec_prompts import build_prompt, build_repair_prompt


def load_dotenv(path: Path) -> Dict[str, str]:
    values: Dict[str, str] = {}
    if not path.exists():
        return values
    for raw in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        value = value.strip()
        if len(value) >= 2 and value[0] == value[-1] and value[0] in {'"', "'"}:
            value = value[1:-1]
        values[key.strip()] = value
    return values


def merge_env(dotenv_values: Dict[str, str]) -> Dict[str, str]:
    env = dict(dotenv_values)
    env.update(os.environ)
    return env


def clean_llm_output(text: str) -> str:
    text = re.sub(r"```[a-zA-Z0-9_+-]*\n?", "", text)
    text = text.replace("```", "")
    return text.strip() + "\n"


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


def source_non_spec_lines(text: str) -> List[str]:
    out: List[str] = []
    in_block = False
    for line in text.splitlines(keepends=True):
        is_spec, in_block = is_spec_line(line, in_block)
        if not is_spec:
            out.append(line)
    return out


def recompose_candidate_with_source(source_code: str, candidate_text: str) -> str:
    """Keep spec lines from candidate while restoring original non-spec lines byte-for-byte."""
    if not candidate_text.strip():
        return candidate_text

    src_non_spec = source_non_spec_lines(source_code)
    src_idx = 0
    in_block = False
    out: List[str] = []

    for line in candidate_text.splitlines(keepends=True):
        is_spec, in_block = is_spec_line(line, in_block)
        if is_spec:
            # Drop orphan annotations appended after the original source body.
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


def sanitize_c_annotations(text: str, source_code: str) -> str:
    lines = text.splitlines(keepends=True)
    out: List[str] = []

    source_has_struct = "struct " in source_code
    waiting_for_body_after_header = False

    def next_non_spec_code_line(start_idx: int) -> str | None:
        in_block_local = False
        j = start_idx
        while j < len(lines):
            cand = lines[j]
            cand_is_spec, in_block_local = is_spec_line(cand, in_block_local)
            if (not cand_is_spec) and cand.strip() != "":
                return cand
            j += 1
        return None

    def prev_non_spec_code_line(start_idx: int) -> str | None:
        in_block_local = False
        j = start_idx
        while j >= 0:
            cand = lines[j]
            cand_is_spec, in_block_local = is_spec_line(cand, in_block_local)
            if (not cand_is_spec) and cand.strip() != "":
                return cand
            j -= 1
        return None

    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.lstrip()

        is_spec, _ = is_spec_line(line, False)
        if not is_spec:
            if waiting_for_body_after_header and "{" in line:
                waiting_for_body_after_header = False
            if _looks_like_c_function_header(line):
                waiting_for_body_after_header = True
            out.append(line)
            i += 1
            continue

        # Handle line annotations.
        if stripped.startswith("//@"):
            if stripped.startswith("//@ : main"):
                next_code = next_non_spec_code_line(i + 1)
                prev_code = prev_non_spec_code_line(i - 1)
                if not (
                    (next_code is not None and _looks_like_c_function_header(next_code))
                    or (prev_code is not None and _looks_like_c_function_header(prev_code))
                ):
                    i += 1
                    continue
            if stripped.startswith("//@ requires") or stripped.startswith("//@ ensures"):
                next_code = next_non_spec_code_line(i + 1)
                prev_code = prev_non_spec_code_line(i - 1)
                if not (
                    (next_code is not None and _looks_like_c_function_header(next_code))
                    or (prev_code is not None and _looks_like_c_function_header(prev_code))
                ):
                    i += 1
                    continue
            if waiting_for_body_after_header:
                # In the function-header prelude, only contracts are valid.
                if not (
                    stripped.startswith("//@ : main")
                    or stripped.startswith("//@ requires")
                    or stripped.startswith("//@ ensures")
                ):
                    i += 1
                    continue
            out.append(line.replace("\\result", "result"))
            i += 1
            continue

        # Handle block annotations as a single chunk.
        if "/*@" in line:
            chunk_lines = [line]
            i += 1
            if "@*/" not in line[line.find("/*@"):]:
                while i < len(lines):
                    chunk_lines.append(lines[i])
                    if "@*/" in lines[i]:
                        i += 1
                        break
                    i += 1
            chunk = "".join(chunk_lines)
            chunk_lower = chunk.lower()

            if "auto_contract_marker" in chunk_lower:
                continue

            if waiting_for_body_after_header:
                # Before '{', keep only contract-like blocks.
                if "requires" not in chunk_lower and "ensures" not in chunk_lower:
                    continue

            if "requires" in chunk_lower or "ensures" in chunk_lower:
                next_code = next_non_spec_code_line(i)
                if next_code is None or not _looks_like_c_function_header(next_code):
                    continue

            # Remove obvious cross-file predicate templates for non-struct files.
            if (not source_has_struct) and ("predicate" in chunk_lower) and ("struct " in chunk_lower):
                continue

            out.append(chunk.replace("\\result", "result"))
            continue

        i += 1

    merged = "".join(out)
    if not merged.endswith("\n"):
        merged += "\n"
    return merged


def spec_projection(text: str) -> str:
    out: List[str] = []
    in_block = False
    for line in text.splitlines(keepends=True):
        i = 0
        kept = ""
        while i < len(line):
            if in_block:
                end = line.find("@*/", i)
                if end == -1:
                    i = len(line)
                    break
                in_block = False
                i = end + 3
                continue
            start_block = line.find("/*@", i)
            start_line = line.find("//@", i)
            if start_line != -1 and (start_block == -1 or start_line < start_block):
                kept += line[i:start_line]
                i = len(line)
                break
            if start_block != -1:
                kept += line[i:start_block]
                i = start_block + 3
                in_block = True
                continue
            kept += line[i:]
            break
        out.append(kept)
    return "".join(out)


def non_spec_unchanged(before: str, after: str) -> bool:
    return normalize_non_spec_text(spec_projection(before)) == normalize_non_spec_text(spec_projection(after))


def normalize_non_spec_text(text: str) -> str:
    # 允许空行、缩进、行尾空格等微小格式变动
    normalized: List[str] = []
    for line in text.splitlines():
        # 移除所有空白字符，仅保留非注释代码内容
        code = line.strip()
        if code == "":
            continue
        normalized.append(code)
    return "\n".join(normalized) + "\n"


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


def candidate_quality_issue(source_code: str, candidate_text: str) -> str | None:
    if not candidate_text.strip():
        return "empty output"

    if not non_spec_unchanged(source_code, candidate_text):
        return "changed non-spec code or dropped source body"

    contract_total, true_total = count_contracts_and_true_contracts(candidate_text)
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


def extract_c_function_name(line: str) -> str | None:
    stripped = line.strip()
    if not stripped or "(" not in stripped:
        return None
    matches = re.findall(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(", stripped)
    if not matches:
        return None
    candidate = matches[-1]
    if candidate in {"if", "for", "while", "switch", "return", "sizeof"}:
        return None
    return candidate


def c_contract_lines_for_header(line: str) -> List[str]:
    return ["//@ requires true;\n", "//@ ensures true;\n"]


def benchmark_file_suffix(benchmark: BenchmarkRecord) -> str:
    suffix = benchmark.source_path.suffix.lower()
    if suffix in {".c", ".java", ".rs"}:
        return suffix
    if benchmark.language == "c":
        return ".c"
    if benchmark.language == "java":
        return ".java"
    if benchmark.language == "rust":
        return ".rs"
    return ".txt"


def _looks_like_c_function_header(line: str) -> bool:
    stripped = line.strip()
    if not stripped:
        return False
    if stripped.startswith(("//@", "/*@", "#", "//", "*", "typedef", "struct", "enum", "union")):
        return False
    if stripped.endswith(";"):
        return False
    if "(" not in stripped or ")" not in stripped:
        return False
    lowered = stripped.lower()
    control_prefixes = ("if ", "if(", "for ", "for(", "while ", "while(", "switch ", "switch(")
    if lowered.startswith(control_prefixes):
        return False
    return True


def _has_contract_immediately_above(lines: List[str], idx: int) -> bool:
    j = idx - 1
    while j >= 0 and lines[j].strip() == "":
        j -= 1
    while j >= 0:
        s = lines[j].strip()
        if not s:
            j -= 1
            continue
        if s.startswith("//@"):
            if s.startswith("//@ requires") or s.startswith("//@ ensures"):
                return True
            j -= 1
            continue
        break
    return False


def _has_contract_immediately_below(lines: List[str], idx: int) -> bool:
    j = idx + 1
    while j < len(lines) and lines[j].strip() == "":
        j += 1
    while j < len(lines):
        s = lines[j].strip()
        if not s:
            j += 1
            continue
        if s.startswith("//@"):
            if s.startswith("//@ requires") or s.startswith("//@ ensures"):
                return True
            j += 1
            continue
        break
    return False


def add_minimal_c_contracts(text: str) -> Tuple[str, int]:
    lines = text.splitlines(keepends=True)
    if not lines:
        return text, 0

    output: List[str] = []
    inserted = 0
    i = 0
    while i < len(lines):
        line = lines[i]

        if not _looks_like_c_function_header(line):
            output.append(line)
            i += 1
            continue

        # Determine whether this header is followed by a body start '{' (same line or shortly after).
        has_body = "{" in line
        if not has_body:
            k = i + 1
            while k < len(lines):
                t = lines[k].strip()
                if t == "":
                    k += 1
                    continue
                if t.startswith("//@") or t.startswith("/*@"):
                    k += 1
                    continue
                has_body = t.startswith("{")
                break

        if has_body and not (_has_contract_immediately_above(lines, i) or _has_contract_immediately_below(lines, i)):
            if extract_c_function_name(line) == "main" and "//@ : main" not in line:
                if line.endswith("\n"):
                    line = line[:-1] + " //@ : main\n"
                else:
                    line = line + " //@ : main"
            indent = line[: len(line) - len(line.lstrip())]
            output.append(line)
            for contract_line in c_contract_lines_for_header(line):
                output.append(f"{indent}{contract_line}")
            inserted += 1
            i += 1
            continue

        output.append(line)
        i += 1

    merged = "".join(output)
    if not merged.endswith("\n"):
        merged += "\n"
    return merged, inserted


def run_verifast(path: Path, language: str, config: ExperimentConfig, timeout_sec: int) -> Tuple[bool, str, List[str]]:
    cmd = ["verifast", *config.verifast_args.get(language, []), str(path)]
    proc = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout_sec,
        cwd=str(path.parent),
    )
    stdout = (proc.stdout or b"").decode("utf-8", errors="ignore").strip()
    stderr = (proc.stderr or b"").decode("utf-8", errors="ignore").strip()
    message = stderr if stderr else stdout
    # For Java: "0 errors found" means verification success, even if linking fails
    # For C/Rust: rely on returncode == 0
    if language == "java":
        verified = "0 errors found" in stdout or "0 errors found" in stderr
    else:
        verified = proc.returncode == 0
    
    return verified, message, cmd


def parse_verifast_output(text: str) -> Dict[str, bool]:
    lower = text.lower()
    parse_error_markers = ["parse error", "syntax error", "unexpected token", "unexpected end of file"]
    type_error_markers = ["type error", "cannot unify", "mismatch", "unknown identifier", "not in scope"]
    parse_ok = not any(marker in lower for marker in parse_error_markers)
    type_ok = parse_ok and not any(marker in lower for marker in type_error_markers)
    return {"parse_ok": parse_ok, "type_ok": type_ok}


def score_status(verified: bool, parse_ok: bool, type_ok: bool) -> int:
    if verified:
        return 3
    if type_ok:
        return 2
    if parse_ok:
        return 1
    return 0


def api_settings(model: ModelConfig, env: Dict[str, str]) -> Tuple[str, str]:
    url = env.get(
        model.api_url_env,
        env.get("OPENAI_API_URL", env.get("API_URL", "https://api.openai.com/v1/chat/completions")),
    )
    key = env.get(model.api_key_env, env.get("OPENAI_API_KEY", env.get("API_KEY", "")))
    if not key:
        raise RuntimeError(f"Missing API key in {model.api_key_env} or OPENAI_API_KEY")
    return url, key


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


def prompt_variant(model: ModelConfig, prompt: str, candidate_index: int) -> str:
    # Deterministic decoding vs pass@5:
    # Option A: keep temperature=0 and perturb the prompt slightly per candidate.
    # Option B: use temperature>0 with a fixed seed per run/candidate.
    # This pipeline supports both via `sampling_mode`.
    if model.sampling_mode == "prompt_perturbation":
        return prompt + f"\n\nIndependent candidate index: {candidate_index}.\n"
    return prompt


def call_llm(url: str, key: str, model: ModelConfig, prompt: str, candidate_index: int, timeout_sec: int) -> str:
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
            return data["choices"][0]["message"]["content"]
        except (requests.RequestException, KeyError, ValueError, IndexError, TypeError) as exc:
            last_error = exc
            if attempt >= MAX_LLM_HTTP_RETRIES:
                break
            backoff_sec = min(8, 2 ** (attempt - 1))
            print(
                f"[llm] request failed attempt={attempt}/{MAX_LLM_HTTP_RETRIES}; retry_in={backoff_sec}s; error={exc}",
                flush=True,
            )
            time.sleep(backoff_sec)

    raise RuntimeError(f"LLM request failed after {MAX_LLM_HTTP_RETRIES} attempts: {last_error}")


def save_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def discover_benchmarks(benchmark_root: Path, manifest_path: Path | None) -> List[BenchmarkRecord]:
    if manifest_path is not None and manifest_path.exists():
        return load_manifest(manifest_path, benchmark_root)

    records: List[BenchmarkRecord] = []
    for source_path in sorted(benchmark_root.rglob("*")):
        if not source_path.is_file():
            continue
        if source_path.suffix.lower() not in {".c", ".java", ".rs"}:
            continue
        rel = source_path.relative_to(benchmark_root)
        records.append(
            BenchmarkRecord(
                benchmark_id=rel.as_posix(),
                language=infer_language(source_path),
                source_path=source_path.resolve(),
                expected_spec_path=source_path.resolve(),
            )
        )
    return records


def ensure_expected_total(records: Sequence[BenchmarkRecord], expected_total: int) -> None:
    if len(records) != expected_total:
        raise RuntimeError(f"Benchmark count mismatch: expected {expected_total}, found {len(records)}")


def run_repair_loop(
    api_url: str,
    api_key: str,
    model: ModelConfig,
    benchmark: BenchmarkRecord,
    config: ExperimentConfig,
    run_root: Path,
    candidate_index: int,
    candidate_text: str,
    base_prompt: str,
    llm_timeout: int,
    vf_timeout: int,
    max_rounds: int,
    source_code: str,
) -> Dict[str, object]:
    candidate_dir = run_root / model.name / benchmark.language / benchmark.benchmark_id.replace("/", "__")
    suffix = benchmark_file_suffix(benchmark)
    current_text = candidate_text
    history: List[Dict[str, object]] = []

    candidate_path = candidate_dir / f"candidate_{candidate_index:02d}{suffix}"
    save_text(candidate_path, current_text)
    verified, error, cmd = run_verifast(candidate_path, benchmark.language, config, vf_timeout)
    parsed = parse_verifast_output(error)
    history.append(
        {
            "round": 0,
            "file": str(candidate_path),
            "verified": verified,
            "parse_ok": parsed["parse_ok"],
            "type_ok": parsed["type_ok"],
            "command": cmd,
            "error": error,
        }
    )

    if verified:
        return {"verified": True, "history": history, "final_file": str(candidate_path)}

    last_score = score_status(verified, parsed["parse_ok"], parsed["type_ok"])

    for round_index in range(1, max_rounds + 1):
        repair_prompt = build_repair_prompt(base_prompt, error or "Verification failed.", benchmark.language)
        repair_prompt = prompt_variant(model, repair_prompt, candidate_index + round_index)
        raw = call_llm(api_url, api_key, model, repair_prompt, candidate_index + round_index, llm_timeout)
        fixed = clean_llm_output(raw)
        fixed = recompose_candidate_with_source(source_code, fixed)
        if benchmark.language == "c":
            fixed = sanitize_c_annotations(fixed, source_code)

        # Persist every repair round attempt for post-mortem error analysis.
        attempt_path = candidate_dir / f"candidate_{candidate_index:02d}_repair_{round_index:02d}_attempt{suffix}"
        save_text(attempt_path, fixed)

        if not non_spec_unchanged(current_text, fixed):
            rejected_path = candidate_dir / f"candidate_{candidate_index:02d}_repair_{round_index:02d}_rejected_non_spec_change{suffix}"
            save_text(rejected_path, fixed)
            history.append(
                {
                    "round": round_index,
                    "file": str(rejected_path),
                    "verified": False,
                    "parse_ok": False,
                    "type_ok": False,
                    "status": "rejected_non_spec_change",
                    "error": "LLM changed non-spec code; rejected.",
                }
            )
            continue

        quality_issue = candidate_quality_issue(source_code, fixed)
        if quality_issue is not None:
            rejected_path = candidate_dir / f"candidate_{candidate_index:02d}_repair_{round_index:02d}_rejected_low_quality{suffix}"
            save_text(rejected_path, fixed)
            history.append(
                {
                    "round": round_index,
                    "file": str(rejected_path),
                    "verified": False,
                    "parse_ok": False,
                    "type_ok": False,
                    "status": "rejected_low_quality_spec",
                    "error": f"Low-quality repair candidate rejected: {quality_issue}",
                }
            )
            continue

        current_text = fixed
        if benchmark.language == "c":
            current_text, inserted_contracts = add_minimal_c_contracts(current_text)
            if inserted_contracts > 0:
                print(
                    f"[repair] {benchmark.benchmark_id} k={candidate_index}/{config.pass_k} round={round_index} auto_contracts={inserted_contracts}",
                    flush=True,
                )
        repair_path = candidate_dir / f"candidate_{candidate_index:02d}_repair_{round_index:02d}{suffix}"
        save_text(repair_path, current_text)
        verified, error, cmd = run_verifast(repair_path, benchmark.language, config, vf_timeout)
        parsed = parse_verifast_output(error)
        score = score_status(verified, parsed["parse_ok"], parsed["type_ok"])
        history.append(
            {
                "round": round_index,
                "file": str(repair_path),
                "verified": verified,
                "parse_ok": parsed["parse_ok"],
                "type_ok": parsed["type_ok"],
                "improved": score > last_score,
                "command": cmd,
                "error": error,
            }
        )
        last_score = max(last_score, score)
        if verified:
            return {"verified": True, "history": history, "final_file": str(repair_path)}

    return {"verified": False, "history": history, "final_file": str(candidate_path)}


def run_generation(
    benchmark: BenchmarkRecord,
    model: ModelConfig,
    config: ExperimentConfig,
    env: Dict[str, str],
    run_root: Path,
    llm_timeout: int,
    vf_timeout: int,
    max_rounds: int,
) -> Dict[str, object]:
    api_url, api_key = api_settings(model, env)
    source_code = benchmark.source_path.read_text(encoding="utf-8", errors="ignore")
    suffix = benchmark_file_suffix(benchmark)
    benchmark_results: List[Dict[str, object]] = []

    for candidate_index in range(1, config.pass_k + 1):
        try:
            print(
                f"[candidate] {benchmark.benchmark_id} k={candidate_index}/{config.pass_k} start",
                flush=True,
            )
            settings_text = decoding_settings_text(model, candidate_index)
            base_prompt = build_prompt(
                benchmark.language,
                benchmark.benchmark_id,
                source_code,
                candidate_index,
                config.pass_k,
                settings_text,
            )
            candidate_root = run_root / model.name / benchmark.language / benchmark.benchmark_id.replace("/", "__")
            candidate_text = ""
            generation_error = ""
            for retry in range(1, MAX_CANDIDATE_RETRIES + 1):
                prompt = prompt_variant(model, base_prompt, candidate_index + retry - 1)
                if generation_error:
                    prompt += (
                        "\n\nPrevious output was rejected. "
                        f"Reason: {generation_error}. "
                        "Return the full source file, keep non-spec code unchanged, and provide non-trivial useful specs."
                    )
                raw = call_llm(api_url, api_key, model, prompt, candidate_index + retry - 1, llm_timeout)
                candidate_text = clean_llm_output(raw)
                candidate_text = recompose_candidate_with_source(source_code, candidate_text)
                if benchmark.language == "c":
                    candidate_text = sanitize_c_annotations(candidate_text, source_code)

                # Persist every generation retry output for later diagnostics.
                gen_attempt_path = candidate_root / f"candidate_{candidate_index:02d}_gen_{retry:02d}{suffix}"
                save_text(gen_attempt_path, candidate_text)

                generation_error = candidate_quality_issue(source_code, candidate_text) or ""
                if not generation_error:
                    break

            # Fallback stage: enforce stricter recovery prompt when normal retries fail.
            if generation_error:
                for retry in range(1, MAX_FALLBACK_RETRIES + 1):
                    recovery_prompt = prompt_variant(
                        model,
                        base_prompt + build_recovery_suffix(source_code, generation_error),
                        candidate_index + MAX_CANDIDATE_RETRIES + retry - 1,
                    )
                    raw = call_llm(
                        api_url,
                        api_key,
                        model,
                        recovery_prompt,
                        candidate_index + MAX_CANDIDATE_RETRIES + retry - 1,
                        llm_timeout,
                    )
                    candidate_text = clean_llm_output(raw)
                    candidate_text = recompose_candidate_with_source(source_code, candidate_text)
                    if benchmark.language == "c":
                        candidate_text = sanitize_c_annotations(candidate_text, source_code)

                    # Persist every fallback generation output.
                    fallback_attempt_path = candidate_root / f"candidate_{candidate_index:02d}_fallback_{retry:02d}{suffix}"
                    save_text(fallback_attempt_path, candidate_text)

                    generation_error = candidate_quality_issue(source_code, candidate_text) or ""
                    if not generation_error:
                        print(
                            f"[candidate] {benchmark.benchmark_id} k={candidate_index}/{config.pass_k} recovered_on_fallback={retry}",
                            flush=True,
                        )
                        break

            if generation_error == "empty output":
                # Use the original file as a baseline so the candidate can still enter VeriFast->repair.
                candidate_text = source_code if source_code.endswith("\n") else source_code + "\n"
                generation_error = ""
                print(
                    f"[candidate] {benchmark.benchmark_id} k={candidate_index}/{config.pass_k} fallback_to_source_on_empty",
                    flush=True,
                )

            if not generation_error:
                print(
                    f"[candidate] {benchmark.benchmark_id} k={candidate_index}/{config.pass_k} generated",
                    flush=True,
                )

            if generation_error:
                rejected_candidate_path = candidate_root / f"candidate_{candidate_index:02d}_rejected{suffix}"
                save_text(rejected_candidate_path, candidate_text)
                item = {
                    "candidate_index": candidate_index,
                    "candidate_file": str(rejected_candidate_path),
                    "prompt_hash": hashlib.sha256(base_prompt.encode("utf-8")).hexdigest(),
                    "decoding_settings": json.loads(settings_text),
                    "verification": {
                        "verified": False,
                        "parse_ok": False,
                        "type_ok": False,
                        "command": [],
                        "error": f"Generation rejected after retries: {generation_error}",
                    },
                    "repair": {"performed": False, "history": []},
                }
                benchmark_results.append(item)
                continue

            candidate_path = candidate_root / f"candidate_{candidate_index:02d}{suffix}"
            if benchmark.language == "c":
                candidate_text, inserted_contracts = add_minimal_c_contracts(candidate_text)
                if inserted_contracts > 0:
                    print(
                        f"[candidate] {benchmark.benchmark_id} k={candidate_index}/{config.pass_k} auto_contracts={inserted_contracts}",
                        flush=True,
                    )
            save_text(candidate_path, candidate_text)

            verified, error, cmd = run_verifast(candidate_path, benchmark.language, config, vf_timeout)
            parsed = parse_verifast_output(error)
            print(
                f"[candidate] {benchmark.benchmark_id} k={candidate_index}/{config.pass_k} verified={verified}",
                flush=True,
            )
            item = {
                "candidate_index": candidate_index,
                "candidate_file": str(candidate_path),
                "prompt_hash": hashlib.sha256(base_prompt.encode("utf-8")).hexdigest(),
                "decoding_settings": json.loads(settings_text),
                "verification": {
                    "verified": verified,
                    "parse_ok": parsed["parse_ok"],
                    "type_ok": parsed["type_ok"],
                    "command": cmd,
                    "error": error,
                },
            }

            if verified or max_rounds <= 0:
                item["repair"] = {"performed": False, "history": []}
                benchmark_results.append(item)
                continue

            repair = run_repair_loop(
                api_url=api_url,
                api_key=api_key,
                model=model,
                benchmark=benchmark,
                config=config,
                run_root=run_root,
                candidate_index=candidate_index,
                candidate_text=candidate_text,
                base_prompt=base_prompt,
                llm_timeout=llm_timeout,
                vf_timeout=vf_timeout,
                max_rounds=max_rounds,
                source_code=source_code,
            )
            item["repair"] = {"performed": True, **repair}
            benchmark_results.append(item)
        except Exception as exc:
            candidate_root = run_root / model.name / benchmark.language / benchmark.benchmark_id.replace("/", "__")
            failed_path = candidate_root / f"candidate_{candidate_index:02d}_failed{suffix}"
            failed_text = source_code if source_code.endswith("\n") else source_code + "\n"
            save_text(failed_path, failed_text)
            benchmark_results.append(
                {
                    "candidate_index": candidate_index,
                    "candidate_file": str(failed_path),
                    "prompt_hash": "",
                    "decoding_settings": {},
                    "verification": {
                        "verified": False,
                        "parse_ok": False,
                        "type_ok": False,
                        "command": [],
                        "error": f"Candidate failed due to runtime exception: {exc}",
                    },
                    "repair": {"performed": False, "history": []},
                }
            )
            print(
                f"[candidate] {benchmark.benchmark_id} k={candidate_index}/{config.pass_k} failed_exception={exc}",
                flush=True,
            )
            continue

    return {"benchmark": benchmark.benchmark_id, "language": benchmark.language, "model": model.name, "results": benchmark_results}


def build_summary_rows(report_results: List[Dict[str, object]]) -> List[Dict[str, object]]:
    grouped: Dict[Tuple[str, str], Dict[str, float]] = {}

    for item in report_results:
        model = str(item.get("model", "unknown"))
        language = str(item.get("language", "unknown"))
        key = (model, language)
        g = grouped.setdefault(
            key,
            {
                "benchmarks": 0,
                "file_success": 0,
                "candidate_total": 0,
                "candidate_verified": 0,
                "repair_attempted": 0,
                "repair_verified": 0,
                "repair_improved_steps": 0,
                "repair_steps": 0,
            },
        )

        g["benchmarks"] += 1
        per_file_success = False

        for cand in item.get("results", []):
            g["candidate_total"] += 1
            ver = bool(((cand.get("verification") or {}).get("verified")))
            if ver:
                g["candidate_verified"] += 1
                per_file_success = True

            repair = cand.get("repair") or {}
            if bool(repair.get("performed")):
                g["repair_attempted"] += 1
                if bool(repair.get("verified")):
                    g["repair_verified"] += 1
                    per_file_success = True

                for step in repair.get("history", []):
                    round_id = int(step.get("round", 0))
                    if round_id <= 0:
                        continue
                    g["repair_steps"] += 1
                    if bool(step.get("improved", False)):
                        g["repair_improved_steps"] += 1

        if per_file_success:
            g["file_success"] += 1

    rows: List[Dict[str, object]] = []
    for (model, language), g in sorted(grouped.items()):
        benchmarks = int(g["benchmarks"])
        candidate_total = int(g["candidate_total"])
        repair_attempted = int(g["repair_attempted"])
        repair_steps = int(g["repair_steps"])
        rows.append(
            {
                "model": model,
                "language": language,
                "benchmarks": benchmarks,
                "file_success": int(g["file_success"]),
                "file_success_rate": (g["file_success"] / benchmarks) if benchmarks else 0.0,
                "candidate_total": candidate_total,
                "candidate_verified": int(g["candidate_verified"]),
                "candidate_verify_rate": (g["candidate_verified"] / candidate_total) if candidate_total else 0.0,
                "repair_attempted": repair_attempted,
                "repair_verified": int(g["repair_verified"]),
                "repair_success_rate": (g["repair_verified"] / repair_attempted) if repair_attempted else 0.0,
                "repair_steps": repair_steps,
                "repair_improved_steps": int(g["repair_improved_steps"]),
                "repair_improve_rate": (g["repair_improved_steps"] / repair_steps) if repair_steps else 0.0,
            }
        )
    return rows


def write_summary_files(rows: List[Dict[str, object]], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    summary_json = out_dir / "repair_summary_by_model_language.json"
    summary_csv = out_dir / "repair_summary_by_model_language.csv"

    summary_json.write_text(json.dumps(rows, ensure_ascii=False, indent=2), encoding="utf-8")

    headers = [
        "model",
        "language",
        "benchmarks",
        "file_success",
        "file_success_rate",
        "candidate_total",
        "candidate_verified",
        "candidate_verify_rate",
        "repair_attempted",
        "repair_verified",
        "repair_success_rate",
        "repair_steps",
        "repair_improved_steps",
        "repair_improve_rate",
    ]
    with summary_csv.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=headers)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)

    print(f"[done] summary_json={summary_json}")
    print(f"[done] summary_csv={summary_csv}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Structured LLM->VeriFast experimental runner")
    parser.add_argument("--config", default=str(Path(__file__).with_name("configs") / "llm_spec_experiment.json"))
    parser.add_argument("--manifest", default=None)
    parser.add_argument("--benchmark-root", default=None)
    # 固定模型为 gpt5.5，不再暴露 --model 参数
    parser.add_argument("--language", default="all", choices=["all", "c", "java", "rust"])
    parser.add_argument("--pass_k", type=int, default=None)
    parser.add_argument("--max_rounds", type=int, default=None)
    parser.add_argument("--expected-total", type=int, default=None)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--llm-timeout", type=int, default=180)
    parser.add_argument("--vf-timeout", type=int, default=90)
    parser.add_argument("--max-files", type=int, default=0)
    parser.add_argument("--repair-only", action="store_true")
    parser.add_argument("--out-dir", default=None)
    parser.add_argument("--log-dir", default=None)
    parser.add_argument("--run-prefix", default="output")
    args = parser.parse_args()

    config = load_config(Path(args.config))
    if args.pass_k is not None:
        config = ExperimentConfig(
            expected_total=config.expected_total,
            benchmark_root=config.benchmark_root,
            output_root=config.output_root,
            log_root=config.log_root,
            manifest_path=config.manifest_path,
            pass_k=args.pass_k,
            max_rounds=config.max_rounds if args.max_rounds is None else args.max_rounds,
            verifast_args=config.verifast_args,
            models=config.models,
        )
    elif args.max_rounds is not None:
        config = ExperimentConfig(
            expected_total=config.expected_total,
            benchmark_root=config.benchmark_root,
            output_root=config.output_root,
            log_root=config.log_root,
            manifest_path=config.manifest_path,
            pass_k=config.pass_k,
            max_rounds=args.max_rounds,
            verifast_args=config.verifast_args,
            models=config.models,
        )

    benchmark_root = (Path(args.benchmark_root) if args.benchmark_root else Path(__file__).resolve().parents[1] / config.benchmark_root).resolve()
    manifest_path = Path(args.manifest).resolve() if args.manifest else (Path(__file__).resolve().parents[1] / config.manifest_path).resolve()
    records = discover_benchmarks(benchmark_root, manifest_path if manifest_path.exists() else None)

    discovered_total = len(records)
    expected_total = args.expected_total
    if expected_total is not None and discovered_total != expected_total:
        raise RuntimeError(f"Benchmark count mismatch: expected {expected_total}, found {discovered_total}")

    if args.language != "all":
        records = [record for record in records if record.language == args.language]
    if args.max_files > 0:
        records = records[: args.max_files]
    if not records:
        raise RuntimeError("No benchmarks selected after filtering")

    # 只允许 gpt-5.5
    model = config.models.get("gpt-5.5")
    if model is None:
        raise RuntimeError("Model 'gpt-5.5' not found in config.models; please check your config.")

    repo_root = Path(__file__).resolve().parents[1]
    out_root = (Path(args.out_dir) if args.out_dir else repo_root).resolve()
    run_id = time.strftime(f"{args.run_prefix}_%Y%m%d_%H%M%S")
    run_root = out_root / run_id
    if args.log_dir:
        log_root = Path(args.log_dir).resolve()
        log_run_root = log_root / run_id
    else:
        # Default: keep report/summary with generated candidates in the same timestamped output folder.
        log_run_root = run_root
    run_root.mkdir(parents=True, exist_ok=True)
    log_run_root.mkdir(parents=True, exist_ok=True)

    dotenv = load_dotenv(Path(__file__).resolve().parents[1] / ".env")
    env = merge_env(dotenv)

    print(f"[info] benchmark_root={benchmark_root}", flush=True)
    print(f"[info] manifest={manifest_path}", flush=True)
    if expected_total is None:
        print(f"[info] selected={len(records)} expected_total=auto({discovered_total})", flush=True)
    else:
        print(f"[info] selected={len(records)} expected_total={expected_total}", flush=True)
    print(f"[info] model={model.name}:{model.model_name}", flush=True)
    print(f"[info] pass_k={config.pass_k} max_rounds={config.max_rounds} workers={args.workers}", flush=True)


    # --- 统计实验总耗时 ---
    _exp_start = time.time()

    results: List[Dict[str, object]] = []
    max_rounds = 0 if args.repair_only else config.max_rounds

    if args.workers == 1:
        for idx, benchmark in enumerate(records, start=1):
            print(f"[file {idx}/{len(records)}] {benchmark.benchmark_id}", flush=True)
            try:
                results.append(run_generation(benchmark, model, config, env, run_root, args.llm_timeout, args.vf_timeout, max_rounds))
            except Exception as exc:
                print(f"[file-error] {benchmark.benchmark_id} error={exc}", flush=True)
                results.append(
                    {
                        "benchmark": benchmark.benchmark_id,
                        "language": benchmark.language,
                        "model": model.name,
                        "results": [
                            {
                                "candidate_index": 0,
                                "candidate_file": str(benchmark.source_path),
                                "prompt_hash": "",
                                "decoding_settings": {},
                                "verification": {
                                    "verified": False,
                                    "parse_ok": False,
                                    "type_ok": False,
                                    "command": [],
                                    "error": f"Benchmark failed due to runtime exception: {exc}",
                                },
                                "repair": {"performed": False, "history": []},
                            }
                        ],
                    }
                )
    else:
        with ThreadPoolExecutor(max_workers=args.workers) as executor:
            futures = {
                executor.submit(run_generation, benchmark, model, config, env, run_root, args.llm_timeout, args.vf_timeout, max_rounds): benchmark
                for benchmark in records
            }
            done = 0
            for future in as_completed(futures):
                benchmark = futures[future]
                done += 1
                try:
                    result = future.result()
                    results.append(result)
                    print(f"[done {done}/{len(records)}] {benchmark.benchmark_id}", flush=True)
                except Exception as exc:
                    print(f"[file-error {done}/{len(records)}] {benchmark.benchmark_id} error={exc}", flush=True)
                    results.append(
                        {
                            "benchmark": benchmark.benchmark_id,
                            "language": benchmark.language,
                            "model": model.name,
                            "results": [
                                {
                                    "candidate_index": 0,
                                    "candidate_file": str(benchmark.source_path),
                                    "prompt_hash": "",
                                    "decoding_settings": {},
                                    "verification": {
                                        "verified": False,
                                        "parse_ok": False,
                                        "type_ok": False,
                                        "command": [],
                                        "error": f"Benchmark failed due to runtime exception: {exc}",
                                    },
                                    "repair": {"performed": False, "history": []},
                                }
                            ],
                        }
                    )

    _exp_end = time.time()
    total_time_sec = _exp_end - _exp_start

    # --- 统计Token和成本 ---
    total_tokens = 0
    total_llm_calls = 0
    for item in results:
        for cand in item.get("results", []):
            # 候选生成
            total_llm_calls += 1
            total_tokens += model.max_tokens
            # 修复轮数
            repair = cand.get("repair") or {}
            if repair.get("performed"):
                # 每轮修复都算一次 LLM 调用
                for _ in repair.get("history", []):
                    total_llm_calls += 1
                    total_tokens += model.max_tokens

    # 成本估算（以 OpenAI 1M tokens 约 $1.5 美元计）
    cost_per_million = 1.5
    total_cost = total_tokens / 1_000_000 * cost_per_million

    # --- 输出统计信息 ---
    print("\n========== Experiment Statistics ==========")
    print(f"Total wall time: {total_time_sec:.1f} sec ({total_time_sec/60:.2f} min)")
    print(f"Total LLM calls: {total_llm_calls}")
    print(f"Total tokens (upper bound): {total_tokens}")
    print(f"Estimated cost (@$1.5/M): ${total_cost:.2f}")
    print("==========================================\n")

    report = {
        "time": time.strftime("%Y-%m-%d %H:%M:%S"),
        "benchmark_root": str(benchmark_root),
        "manifest": str(manifest_path),
        "expected_total": expected_total,
        "discovered_total": discovered_total,
        "processed": len(records),
        "model": asdict(model),
        "pass_k": config.pass_k,
        "max_rounds": max_rounds,
        "workers": args.workers,
        "results": results,
        "experiment_stats": {
            "total_time_sec": total_time_sec,
            "total_llm_calls": total_llm_calls,
            "total_tokens": total_tokens,
            "estimated_cost": total_cost,
        },
    }
    report_path = log_run_root / "experiment_report.json"
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
    summary_rows = build_summary_rows(results)
    write_summary_files(summary_rows, log_run_root)
    print(f"[done] report={report_path}", flush=True)


if __name__ == "__main__":
    main()
