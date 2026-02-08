#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import sys
import subprocess
from pathlib import Path
from collections import defaultdict

SUPPORTED_LANGS = {
    ".c": "c",
    ".rs": "rs",
    ".java": "java",
}

def run_verifast(file_path: Path):
    if file_path.suffix == ".c":
        cmd = ["verifast", "-shared", str(file_path)]
    elif file_path.suffix in [".rs", ".java"]:
        cmd = ["verifast", str(file_path)]
    else:
        return None

    try:
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True
        )
        return result.returncode == 0
    except FileNotFoundError:
        print("[FATAL] verifast 未找到，请确认已安装并在 PATH 中")
        sys.exit(1)

def main(output_dir):
    output_dir = Path(output_dir).resolve()

    if not output_dir.exists():
        print(f"[ERROR] 输出目录不存在: {output_dir}")
        sys.exit(1)

    stats = defaultdict(lambda: defaultdict(lambda: {
        "total": 0,
        "pass": 0,
        "fail": 0
    }))

    print(f"=== 开始验证目录: {output_dir} ===\n")

    for file_path in output_dir.rglob("*"):
        if file_path.suffix not in SUPPORTED_LANGS:
            continue
        try:
            rel = file_path.relative_to(output_dir)
            model = rel.parts[0]
        except Exception:
            model = "UNKNOWN"

        lang = SUPPORTED_LANGS[file_path.suffix]

        stats[model][lang]["total"] += 1

        print(f"[VERIFY] ({model} | {lang}) {file_path}")
        ok = run_verifast(file_path)

        if ok:
            stats[model][lang]["pass"] += 1
            print("  -> PASS\n")
        else:
            stats[model][lang]["fail"] += 1
            print("  -> FAIL\n")


    print("\n=== 验证统计结果 ===\n")

    for model in sorted(stats.keys()):
        print(f"模型: {model}")
        for lang in ["c", "rs", "java"]:
            data = stats[model].get(lang)
            if not data:
                continue
            print(
                f"  {lang.upper():5s}: "
                f"总数 {data['total']:4d} | "
                f"通过 {data['pass']:4d} | "
                f"失败 {data['fail']:4d}"
            )
        print()

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("用法: python3 verify_output_by_model.py <output_dir>")
        sys.exit(1)

    main(sys.argv[1])
