#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess
from pathlib import Path
from collections import defaultdict
import re

# ================== 配置 ==================
root_dir = Path("/app/output")  # 根目录
models = ["claude-opus", "qwen3", "deepseek", "gpt52"]
languages = ["C", "Java", "Rust"]

# F1–F6 正则增强版
failure_map = {
    "F1": [r"missing ownership", r"permission.*not provided", r"heap ownership.*required"],
    "F2": [r"incomplete frame", r"frame.*not preserved", r"resource.*not preserved"],
    "F3": [r"loop invariant", r"weak invariant", r"invariant.*insufficient", r"invariant.*violated"],
    "F4": [r"alias", r"aliasing constraint", r"pointer alias", r"assertion alias"],
    "F5": [r"over-strong", r"too strong", r"contract.*stronger than necessary"],
    "F6": [r"unsound assumption", r"assumption.*inconsistent", r"invalid assumption"]
}

# ================== 初始化统计 ==================
lang_counts = {lang: {f: 0 for f in failure_map} for lang in languages}
model_counts = {model: {f: 0 for f in failure_map} for model in models}

# ================== 遍历模型文件夹 ==================
for model in models:
    model_path = root_dir / model
    if not model_path.is_dir():
        print(f"Warning: Model folder not found: {model_path}")
        continue

    # 遍历模型文件夹下所有文件（递归）
    for src_file in model_path.glob("**/*"):
        if not src_file.is_file():
            continue  # 跳过目录

        # 判断语言
        if src_file.suffix == ".c":
            lang = "C"
        elif src_file.suffix == ".java":
            lang = "Java"
        elif src_file.suffix == ".rs":
            lang = "Rust"
        else:
            continue  # 跳过非源码文件

        print(f"\n=== Checking file: {src_file} (Model: {model}, Language: {lang}) ===")

        log_file = src_file.with_suffix(src_file.suffix + ".log")
        log_text = ""

        try:
            # 构建命令，C文件用 -shared
            if src_file.suffix == ".c":
                cmd = f"verifast -shared '{src_file}' > '{log_file}' 2>&1"
            else:
                cmd = f"verifast '{src_file}' > '{log_file}' 2>&1"

            subprocess.run(cmd, shell=True, timeout=60)
            if log_file.exists():
                log_text = log_file.read_text()
        except Exception as e:
            log_text = str(e)

        # 匹配 F1–F6
        matched = False
        for fmode, patterns in failure_map.items():
            if any(re.search(p, log_text, re.I) for p in patterns):
                lang_counts[lang][fmode] += 1
                model_counts[model][fmode] += 1
                matched = True
                print(f" -> Matched Failure Mode: {fmode}")
                break
        if not matched:
            print(" -> Matched Failure Mode: None")

# ================== 输出统计 ==================
print("\n=== Failure Mode Statistics by Language ===")
for lang in languages:
    print(f"\nLanguage: {lang}")
    total = sum(lang_counts[lang].values())
    for f in ["F1","F2","F3","F4","F5","F6"]:
        print(f"  {f}: {lang_counts[lang][f]}")
    print(f"  Total failures: {total}")

print("\n=== Failure Mode Statistics by Model ===")
for model in models:
    print(f"\nModel: {model}")
    total = sum(model_counts[model].values())
    for f in ["F1","F2","F3","F4","F5","F6"]:
        print(f"  {f}: {model_counts[model][f]}")
    print(f"  Total failures: {total}")