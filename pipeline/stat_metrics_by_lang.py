#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess
import sys
from pathlib import Path
from collections import defaultdict, Counter


MODELS = {
    "claude-opus": "claude-opus-4-5-20251101",
    "qwen3": "qwen3-max",
    "deepseek": "deepseek-v3.2",
    "gpt52": "gpt-5.2"
}



VERIFAST_CMD_C = ["verifast", "-shared"]
VERIFAST_CMD_OTHER = ["verifast"]



LANG_KEYWORDS = {
    "C": {
        "parse": ["parse error", "syntax error", "unexpected", "error:", "cannot parse"],
        "type": ["type error", "unknown identifier", "predicate not found", "no such predicate", "cannot find predicate"],
        "verify": ["verification failed", "postcondition might not hold", "assertion might fail"]
    },
    "Java": {
        "parse": ["parse error", "syntax error", "unexpected", "error:", "cannot parse"],
        "type": ["type error", "unknown identifier", "predicate not found", "no such predicate", "cannot find predicate"],
        "verify": ["verification failed", "postcondition might not hold", "assertion might fail"]
    },
    "Rust": {
        "parse": ["parse error", "syntax error", "unexpected", "error:", "cannot parse"],
        "type": ["type error", "unknown identifier", "predicate not found", "no such predicate", "cannot find predicate"],
        "verify": ["verification failed", "postcondition might not hold", "assertion might fail"]
    }
}



def detect_language(file_path: Path):
    if file_path.suffix == ".c":
        return "C"
    elif file_path.suffix == ".java":
        return "Java"
    elif file_path.suffix == ".rs":
        return "Rust"
    else:
        return None


def detect_model(file_path: Path):
    for k, name in MODELS.items():
        if k in str(file_path):
            return name
    return "Unknown"


def classify_result(file_path: Path, lang: str):
    if lang == "C":
        cmd = VERIFAST_CMD_C + [str(file_path)]
    else:
        cmd = VERIFAST_CMD_OTHER + [str(file_path)]

    result = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )

    output = (result.stdout + result.stderr).lower()
    keywords = LANG_KEYWORDS.get(lang, LANG_KEYWORDS["C"])

    if any(k in output for k in keywords["parse"]):
        return "syntax_error"
    if any(k in output for k in keywords["type"]):
        return "type_error"
    if result.returncode == 0:
        return "verified"
    if any(k in output for k in keywords["verify"]):
        return "verification_failed"

    return "unknown_failure"


def main(root_dir):
    root = Path(root_dir)
    files = list(root.rglob("*"))

    stats = defaultdict(lambda: defaultdict(Counter))  # stats[model][lang][result]
    totals = defaultdict(lambda: defaultdict(int))     # totals[model][lang]

    for f in files:
        lang = detect_language(f)
        if not lang:
            continue
        model = detect_model(f)
        totals[model][lang] += 1
        totals[model]["Overall"] += 1

        result = classify_result(f, lang)
        stats[model][lang][result] += 1
        stats[model]["Overall"][result] += 1



    print("\n========== 分模型+分语言统计 ==========\n")

    for model in totals:
        print(f"Model: {model}")
        for lang in list(totals[model].keys()):
            total = totals[model][lang]
            counter = stats[model][lang]

            syntax_valid = total - counter.get("syntax_error", 0)
            type_correct = syntax_valid - counter.get("type_error", 0)
            verified = counter.get("verified", 0)

            SAR = syntax_valid / total if total > 0 else 0.0
            TCR = type_correct / total if total > 0 else 0.0
            VSR = verified / total if total > 0 else 0.0

            print(f"  Language: {lang}")
            print(f"    Total: {total}")
            print(f"    syntax_error: {counter.get('syntax_error',0)}")
            print(f"    type_error: {counter.get('type_error',0)}")
            print(f"    verification_failed: {counter.get('verification_failed',0)}")
            print(f"    verified: {counter.get('verified',0)}")
            print(f"    --- Metrics ---")
            print(f"    SAR: {SAR:.4f}")
            print(f"    TCR: {TCR:.4f}")
            print(f"    VSR: {VSR:.4f}")
        print()

    print("=============================================")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python3 stat_metrics_by_model_lang.py <root_directory>")
        sys.exit(1)

    main(sys.argv[1])