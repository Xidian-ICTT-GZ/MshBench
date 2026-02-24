#!/usr/bin/env python3

import requests
from pathlib import Path
import subprocess
import sys
import time
import json
import re
import hashlib
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed


API_URL = "https://api.linyinet.asia/v1/chat/completions"
API_KEY = ""

PASS_K = 5
MAX_REPAIR = 3

MAX_WORKERS = 4
MIN_API_INTERVAL = 1.2

SLEEP_AFTER_FAIL = 1

MODELS = {
    "claude-opus": "claude-opus-4-5-20251101",
    "qwen3": "qwen3-max",
    "deepseek": "deepseek-v3.2",
    "gpt52": "gpt-5.2",
}

CACHE_FILE = Path("llm_cache.json")


LOCK = threading.Lock()
LAST_API_CALL = 0

if CACHE_FILE.exists():
    CACHE = json.loads(CACHE_FILE.read_text())
else:
    CACHE = {}


def detect_language(path: Path) -> str:
    if path.suffix == ".c":
        return "c"
    if path.suffix == ".java":
        return "java"
    if path.suffix == ".rs":
        return "rust"
    return "unknown"


def load_prompt(lang: str, prompt_root: Path) -> str:
    p = prompt_root / f"{lang}.txt"
    if not p.exists():
        raise RuntimeError(f"Missing prompt {p}")
    return p.read_text()


def clean_output(text: str) -> str:
    text = re.sub(r"```[a-zA-Z]*\n?", "", text)
    text = re.sub(r"```", "", text)
    return text.strip()



def hash_prompt(prompt: str) -> str:
    return hashlib.sha256(prompt.encode()).hexdigest()


def cache_get(prompt):
    key = hash_prompt(prompt)
    return CACHE.get(key)


def cache_put(prompt, result):
    key = hash_prompt(prompt)
    CACHE[key] = result
    CACHE_FILE.write_text(json.dumps(CACHE))



def rate_limit():
    global LAST_API_CALL

    with LOCK:
        now = time.time()
        diff = now - LAST_API_CALL

        if diff < MIN_API_INTERVAL:
            time.sleep(MIN_API_INTERVAL - diff)

        LAST_API_CALL = time.time()


def call_llm(model, prompt):

    cached = cache_get(prompt)

    if cached:
        return cached

    rate_limit()

    resp = requests.post(
        API_URL,
        headers={"Authorization": f"Bearer {API_KEY}"},
        json={
            "model": model,
            "messages": [{"role": "user", "content": prompt}],
            "temperature": 0.2,
        },
        timeout=120,
    )

    resp.raise_for_status()

    output = resp.json()["choices"][0]["message"]["content"]

    cache_put(prompt, output)

    return output



def run_verifast(file: Path, lang: str):

    try:
        cmd = ["verifast", str(file)]

        proc = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=60,
        )

        success = proc.returncode == 0
        output = proc.stdout.decode(errors="ignore")

        return success, output

    except Exception as e:
        return False, str(e)



def build_repair_prompt(prompt_template, code, previous_output, error):

    repair_block = f"""

The previous attempt failed verification.

Verifier output:

{error}

Please fix the specifications.
Output the full corrected program.
"""

    return prompt_template.replace("{CODE}", code + "\n\n" + previous_output + repair_block)



def run_file(model_key, model_name, src_file, src_root, out_root, prompt_root):

    lang = detect_language(src_file)
    if lang == "unknown":
        return None

    prompt_template = load_prompt(lang, prompt_root)

    rel = src_file.relative_to(src_root)
    code = src_file.read_text(errors="ignore")

    passed = False
    pass_at = None

    for k in range(1, PASS_K + 1):

        prompt = prompt_template.replace("{CODE}", code)

        try:
            raw = call_llm(model_name, prompt)
            generated = clean_output(raw)
        except Exception as e:
            print("API error:", e)
            continue

        out_file = out_root / model_key / f"sample_{k}" / lang / rel
        out_file.parent.mkdir(parents=True, exist_ok=True)
        out_file.write_text(generated)

        ok, verifier_output = run_verifast(out_file, lang)

        if ok:
            passed = True
            pass_at = k
            break


        current_code = generated

        for r in range(MAX_REPAIR):

            repair_prompt = build_repair_prompt(
                prompt_template,
                code,
                current_code,
                verifier_output,
            )

            try:
                raw = call_llm(model_name, repair_prompt)
                fixed = clean_output(raw)
            except Exception:
                break

            repair_file = (
                out_root
                / model_key
                / f"sample_{k}"
                / f"repair_{r+1}"
                / lang
                / rel
            )

            repair_file.parent.mkdir(parents=True, exist_ok=True)
            repair_file.write_text(fixed)

            ok, verifier_output = run_verifast(repair_file, lang)

            if ok:
                passed = True
                pass_at = k
                break

            current_code = fixed

        if passed:
            break

        time.sleep(SLEEP_AFTER_FAIL)

    return {
        "model": model_key,
        "file": str(rel),
        "language": lang,
        "pass": passed,
        "pass_at": pass_at,
        "attempts": k if passed else PASS_K,
    }



def run_benchmark(src_root, out_root, prompt_root):

    src_root = Path(src_root)
    out_root = Path(out_root)
    prompt_root = Path(prompt_root)

    results = []

    files = [p for p in src_root.rglob("*") if p.is_file()]

    print("Total files:", len(files))

    for model_key, model_name in MODELS.items():

        print("\nMODEL:", model_key)

        with ThreadPoolExecutor(MAX_WORKERS) as executor:

            futures = []

            for f in files:
                futures.append(
                    executor.submit(
                        run_file,
                        model_key,
                        model_name,
                        f,
                        src_root,
                        out_root,
                        prompt_root,
                    )
                )

            for fut in as_completed(futures):

                res = fut.result()

                if res:
                    print(res)
                    results.append(res)

    report = out_root / "pass_at_5_repair_report.json"
    report.write_text(json.dumps(results, indent=2))

    print("\nReport written:", report)



if __name__ == "__main__":

    if len(sys.argv) != 4:
        print(
            "Usage:\n"
            "python3 run_pass5_repair_parallel.py "
            "<benchmark_dir> <output_dir> <prompt_dir>"
        )
        sys.exit(1)

    run_benchmark(sys.argv[1], sys.argv[2], sys.argv[3])