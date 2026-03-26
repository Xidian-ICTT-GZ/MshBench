#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from pathlib import Path
from collections import defaultdict


root_dir = Path("/app/output")
models = ["claude-opus", "qwen3", "deepseek", "gpt52"]
languages = ["C", "Java", "Rust"]

failure_types = ["F1","F2","F3","F4","F5","F6"]

lang_counts = {lang: {f: 0 for f in failure_types} for lang in languages}
model_counts = {model: {f: 0 for f in failure_types} for model in models}

lang_files = {lang: {f: [] for f in failure_types} for lang in languages}

for model in models:
    model_path = root_dir / model
    if not model_path.exists():
        print(f"Warning: Model folder not found: {model_path}")
        continue

    for lang in languages:
        lang_path = model_path / lang
        if not lang_path.exists():
            continue

        for log_file in lang_path.glob("*.log"):
            with open(log_file, "r", encoding="utf-8") as f:
                lines = f.read().splitlines()

            file_failure_types = set(line.strip() for line in lines if line.strip() in failure_types)

            for ftype in file_failure_types:
                lang_counts[lang][ftype] += 1
                model_counts[model][ftype] += 1
                lang_files[lang][ftype].append(log_file.name)

print("\n=== Failure Mode Statistics by Language ===")
for lang in languages:
    print(f"\nLanguage: {lang}")
    for f in failure_types:
        count = lang_counts[lang][f]
        files = ', '.join(lang_files[lang][f][:3])
        print(f"{f}: {count}" + (f" (Files: {files} ...)" if count > 0 else ""))
    total = sum(lang_counts[lang].values())
    print(f"Total failures: {total}")

print("\n=== Failure Mode Statistics by Model ===")
for model in models:
    print(f"\nModel: {model}")
    for f in failure_types:
        count = model_counts[model][f]
        print(f"{f}: {count}")
    total = sum(model_counts[model].values())
    print(f"Total failures: {total}")