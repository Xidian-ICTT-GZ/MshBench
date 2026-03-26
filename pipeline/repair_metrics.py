#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pathlib import Path
from collections import defaultdict
import difflib
import csv

# -------------------------------
# 配置路径和模型
# -------------------------------
ROOT_DIR = Path("/app/output_at_5")  # 输出路径
MODELS = ["qwen3", "claude-opus", "deepseek", "gpt52"]
LANGUAGES = ["c", "java", "rust"]
SAMPLES = ["sample_1", "sample_2", "sample_3", "sample_4", "sample_5"]

# 输出文件
CSV_FILE = "repair_metrics.csv"
LATEX_FILE = "repair_metrics_table.tex"
LOG_DIR = Path("repair_logs")
LOG_DIR.mkdir(exist_ok=True)

# -------------------------------
# 工具函数
# -------------------------------
def token_edit_distance(text1, text2):
    """简单 token-level 编辑距离"""
    t1 = text1.split()
    t2 = text2.split()
    sm = difflib.SequenceMatcher(None, t1, t2)
    return sum(block.size for block in sm.get_matching_blocks())

def ast_edit_distance(text1, text2):
    """简单 AST-level 编辑距离, 这里用 token-count 差代替"""
    t1 = text1.split()
    t2 = text2.split()
    return abs(len(t1) - len(t2))

def verify_success(file_path):
    """
    检查修复文件是否成功通过 Verifast。
    假设 log 文件在同目录下，并包含字符串 "Verification succeeded" 表示通过
    """
    log_file = file_path.with_suffix(".log")
    if not log_file.exists():
        return False
    content = log_file.read_text(errors="ignore")
    return "Verification succeeded" in content

# -------------------------------
# 统计每个模型的指标
# -------------------------------
results = defaultdict(lambda: {
    "total_repair_rounds": 0,
    "token_edit": 0,
    "ast_edit": 0,
    "success_count": 0,
    "program_count": 0
})

for model in MODELS:
    model_path = ROOT_DIR / model
    if not model_path.exists():
        continue

    for lang in LANGUAGES:
        lang_path = model_path / lang
        if not lang_path.exists():
            continue

        for orig_file in (lang_path / "sample_1").rglob("*.*"):
            if not orig_file.is_file():
                continue

            orig_text = orig_file.read_text(errors="ignore")
            repair_rounds = 0
            token_edits = 0
            ast_edits = 0
            success = False

            # 遍历 sample_2~sample_5
            for i, sample in enumerate(SAMPLES[1:], start=1):
                repaired_file = lang_path / sample / orig_file.name
                if not repaired_file.exists():
                    continue

                repaired_text = repaired_file.read_text(errors="ignore")
                token_edits += token_edit_distance(orig_text, repaired_text)
                ast_edits += ast_edit_distance(orig_text, repaired_text)
                repair_rounds = i

                if verify_success(repaired_file):
                    success = True
                    break  # 第一次成功即停止

            # 更新模型统计
            results[model]["total_repair_rounds"] += repair_rounds
            results[model]["token_edit"] += token_edits
            results[model]["ast_edit"] += ast_edits
            results[model]["success_count"] += 1 if success else 0
            results[model]["program_count"] += 1

            # 生成 log
            log_file_path = LOG_DIR / f"{model}_{lang}_{orig_file.stem}.log"
            with log_file_path.open("w") as logf:
                logf.write(f"Program: {orig_file}\n")
                logf.write(f"Repair rounds: {repair_rounds}\n")
                logf.write(f"Token-level edit distance: {token_edits}\n")
                logf.write(f"AST-level edit distance: {ast_edits}\n")
                logf.write(f"Success after repair: {'Yes' if success else 'No'}\n")

# -------------------------------
# 输出表格
# -------------------------------
print("Table 6: Repair Effort Metrics per Model\n")
header = ["Model", "AvgRepair", "TokenEdit", "ASTEdit", "SuccessAfterRepair"]
print("{:<12} {:<12} {:<12} {:<12} {:<12}".format(*header))
print("-" * 67)

# 写 CSV
with open(CSV_FILE, "w", newline="") as csvfile:
    writer = csv.writer(csvfile)
    writer.writerow(header)

    for model in MODELS:
        data = results[model]
        prog_count = max(data["program_count"], 1)
        avg_repair = data["total_repair_rounds"] / prog_count
        avg_token = data["token_edit"] / prog_count
        avg_ast = data["ast_edit"] / prog_count
        success_rate = 100 * data["success_count"] / prog_count

        print("{:<12} {:<12.2f} {:<12.2f} {:<12.2f} {:<12.2f}%".format(
            model, avg_repair, avg_token, avg_ast, success_rate
        ))
        writer.writerow([model, f"{avg_repair:.2f}", f"{avg_token:.2f}", f"{avg_ast:.2f}", f"{success_rate:.2f}%"])

# 写 LaTeX 表格
with open(LATEX_FILE, "w") as f:
    f.write("\\begin{tabular}{lcccc}\n")
    f.write("\\hline\n")
    f.write("Model & AvgRepair & TokenEdit & ASTEdit & SuccessAfterRepair \\\\\n")
    f.write("\\hline\n")
    for model in MODELS:
        data = results[model]
        prog_count = max(data["program_count"], 1)
        avg_repair = data["total_repair_rounds"] / prog_count
        avg_token = data["token_edit"] / prog_count
        avg_ast = data["ast_edit"] / prog_count
        success_rate = 100 * data["success_count"] / prog_count
        f.write(f"{model} & {avg_repair:.2f} & {avg_token:.2f} & {avg_ast:.2f} & {success_rate:.2f}\\% \\\\\n")
    f.write("\\hline\n")
    f.write("\\end{tabular}\n")

print(f"\nCSV saved: {CSV_FILE}")
print(f"LaTeX table saved: {LATEX_FILE}")
print(f"Repair logs saved in: {LOG_DIR}")