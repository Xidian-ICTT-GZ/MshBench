#!/usr/bin/env python3
import requests
from pathlib import Path
import subprocess
import sys
import time
import json
import re
import random


API_URL = "https://api.linyinet.asia/v1/chat/completions"
API_KEY = "sk-pI1rFGsI8ea8K5jdjlAnL08GDEjtsx0m0y7ajuUuuuACp2Dx"

PASS_K = 5
SLEEP_BETWEEN_CALLS = 2

MAX_RETRIES_PER_ATTEMPT = 3
BASE_BACKOFF = 2.0
MAX_BACKOFF = 30.0
JITTER = 1.0

MODELS = {
    "claude-opus": "claude-opus-4-5-20251101",
    "qwen3": "qwen3-max",
    "deepseek": "deepseek-v3.2",
    "gpt52": "gpt-5.2",
}


def detect_language(path: Path) -> str:
    if path.suffix == ".c":
        return "c"
    if path.suffix == ".java":
        return "java"
    if path.suffix == ".rs":
        return "rust"
    return "unknown"


def load_prompt(lang: str, prompt_root: Path) -> str:
    prompt_file = prompt_root / f"{lang}.txt"
    if not prompt_file.exists():
        raise FileNotFoundError(f"Prompt not found: {prompt_file}")
    return prompt_file.read_text(encoding="utf-8")


def clean_output(text: str) -> str:
    text = re.sub(r"```[a-zA-Z]*\n?", "", text)
    text = re.sub(r"```", "", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def is_rate_limit_error(e: Exception) -> bool:
    return "429" in str(e) or "rate limit" in str(e).lower()


def is_auth_error(e: Exception) -> bool:
    return "401" in str(e) or "unauthorized" in str(e).lower()


def call_llm_with_retry(model_name: str, prompt: str) -> str:
    retry = 0
    while True:
        try:
            resp = requests.post(
                API_URL,
                headers={"Authorization": f"Bearer {API_KEY}"},
                json={
                    "model": model_name,
                    "messages": [{"role": "user", "content": prompt}],
                    "temperature": 0.2,
                },
                timeout=120,
            )
            resp.raise_for_status()
            return resp.json()["choices"][0]["message"]["content"]

        except Exception as e:
            if is_auth_error(e):
                print("    [FATAL] 401 authentication error")
                raise

            if is_rate_limit_error(e) and retry < MAX_RETRIES_PER_ATTEMPT:
                retry += 1
                backoff = min(MAX_BACKOFF, BASE_BACKOFF * (2 ** retry))
                backoff += random.uniform(0, JITTER)
                print(f"    [429] rate limited, retry {retry}, sleep {backoff:.1f}s")
                time.sleep(backoff)
                continue

            raise


def run_verifast(path: Path, lang: str) -> bool:
    try:
        if lang in ("c", "java", "rust"):
            cmd = ["verifast", str(path)]
        else:
            return False

        proc = subprocess.run(
            cmd,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=60,
        )
        return proc.returncode == 0
    except Exception:
        return False



def main(src_root, out_root, prompt_root):
    src_root = Path(src_root).resolve()
    out_root = Path(out_root).resolve()
    prompt_root = Path(prompt_root).resolve()

    out_root.mkdir(parents=True, exist_ok=True)

    results = []

    for model_key, model_name in MODELS.items():
        print(f"\n=== MODEL: {model_key} ===")
        model_out = out_root / model_key
        model_out.mkdir(parents=True, exist_ok=True)

        for src_file in src_root.rglob("*"):
            if not src_file.is_file():
                continue

            lang = detect_language(src_file)
            if lang == "unknown":
                continue

            rel = src_file.relative_to(src_root)
            print(f"\n[FILE] {rel}")

            code = src_file.read_text(encoding="utf-8", errors="ignore")
            prompt_template = load_prompt(lang, prompt_root)

            passed = False

            for k in range(1, PASS_K + 1):
                print(f"  attempt {k}/{PASS_K} ...")
                prompt = prompt_template.replace("{CODE}", code)

                try:
                    raw = call_llm_with_retry(model_name, prompt)
                    cleaned = clean_output(raw)
                except Exception as e:
                    print(f"    LLM error: {e}")
                    break

                out_file = model_out / f"sample_{k}" / lang / rel
                out_file.parent.mkdir(parents=True, exist_ok=True)
                out_file.write_text(cleaned, encoding="utf-8")

                if run_verifast(out_file, lang):
                    print(f" PASS at attempt {k}")
                    results.append({
                        "model": model_key,
                        "file": str(rel),
                        "language": lang,
                        "pass": True,
                        "pass_at": k,
                        "attempts": k
                    })
                    passed = True
                    break
                else:
                    print(f"  FAIL")

                time.sleep(SLEEP_BETWEEN_CALLS)

            if not passed:
                print(f" MISS pass@{PASS_K}")
                results.append({
                    "model": model_key,
                    "file": str(rel),
                    "language": lang,
                    "pass": False,
                    "pass_at": None,
                    "attempts": PASS_K
                })

    report = out_root / "pass_at_5_report.json"
    report.write_text(json.dumps(results, indent=2), encoding="utf-8")
    print(f"\n[REPORT] 写入 {report}")


if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("用法:")
        print("  python3 run_pass_at_5.py <benchmark_dir> <output_dir> <prompt_dir>")
        sys.exit(1)

    main(sys.argv[1], sys.argv[2], sys.argv[3])
