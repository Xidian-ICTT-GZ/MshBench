#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
分析生成文件的 SAR/TCR/VSR 并生成表格
- SAR: Syntactic Validity - 语法有效性
- TCR: Type Correctness - 类型正确性
- VSR: Verification Success - 验证成功
"""

import subprocess
from pathlib import Path
from collections import defaultdict
import json
from typing import Dict, Tuple, Optional
import re


def try_verifast_verify(file_path: Path, lang: str) -> Tuple[bool, str]:
    """
    尝试用 VeriFast 验证文件，返回 (是否成功, 失败阶段)
    失败阶段: 'none'(成功), 'syntax', 'type', 'verification'
    """
    try:
        if lang == "c":
            cmd = ["verifast", "-shared", str(file_path)]
        elif lang == "java":
            cmd = ["verifast", "-emit_vfmanifest", str(file_path)]
        else:  # rust
            cmd = ["verifast", str(file_path)]
        
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=30,
        )
        
        output = result.stdout + result.stderr
        
        # 成功判定
        if "0 errors found" in output:
            return True, "none"
        
        # 确定失败阶段
        output_lower = output.lower()
        
        # 类型检查阶段（包括符号解析）
        if any(pat in output_lower for pat in [
            "undefined", "cannot find", "cannot resolve", "unresolved",
            "type error", "incompatible", "no field", "not found"
        ]):
            return False, "type"
        
        # 语法阶段
        if any(pat in output_lower for pat in [
            "syntax error", "parse error", "unexpected",
            "expected", "bracket", "parenthesis"
        ]):
            return False, "syntax"
        
        # 验证阶段（其他错误）
        return False, "verification"
        
    except subprocess.TimeoutExpired:
        return False, "verification"
    except FileNotFoundError:
        # VeriFast 不可用，使用启发式方法
        return None, "verifast_not_found"
    except Exception as e:
        return False, "verification"


def heuristic_sar_check(code: str, lang: str) -> bool:
    """启发式 SAR 检查（语法有效性）"""
    if not code.strip():
        return False
    
    # 括号配对检查
    if code.count('(') != code.count(')'):
        return False
    if code.count('{') != code.count('}'):
        return False
    if code.count('[') != code.count(']'):
        return False
    
    return True


def heuristic_tcr_check(code: str, lang: str) -> bool:
    """启发式 TCR 检查（类型正确性）"""
    if not heuristic_sar_check(code, lang):
        return False
    
    # 明显的错误模式
    if any(pat in code.lower() for pat in ["todo", "fixme", "xxx"]):
        return False
    
    # 不完整的省略号
    if "..." in code and lang in ['java', 'rust']:
        if re.search(r'fn\s+\w+.*\{.*\.\.\.|.*\.\.\.*\}', code):
            return False
    
    return True


def analyze_output_directory(output_dir: Path) -> Dict:
    """
    分析 output_YYYYMMDD_HHMMSS 目录中的所有文件
    """
    models = sorted([d.name for d in output_dir.iterdir() if d.is_dir()])
    languages = ["c", "java", "rust"]
    ext_map = {"c": ".c", "java": ".java", "rust": ".rs"}
    
    results = {}
    verifast_available = None  # 标记 VeriFast 是否可用
    
    print(f"分析目录: {output_dir}")
    print("=" * 80)
    
    for model in models:
        print(f"\n处理模型: {model}")
        model_path = output_dir / model
        
        model_results = {
            "c": {"total": 0, "sar": 0, "tcr": 0, "vsr": 0},
            "java": {"total": 0, "sar": 0, "tcr": 0, "vsr": 0},
            "rust": {"total": 0, "sar": 0, "tcr": 0, "vsr": 0},
        }
        
        for lang in languages:
            lang_path = model_path / lang
            if not lang_path.exists():
                continue
            
            ext = ext_map[lang]
            files = list(lang_path.rglob(f"*{ext}"))
            
            print(f"  {lang.upper():6} - 处理 {len(files):3} 个文件", end="")
            
            for file_path in files:
                code = file_path.read_text(encoding='utf-8', errors='ignore')
                total = len(files)
                model_results[lang]["total"] = total
                
                # 先尝试 VeriFast
                if verifast_available is None:
                    success, stage = try_verifast_verify(file_path, lang)
                    if stage == "verifast_not_found":
                        verifast_available = False
                        print("\n    ℹ VeriFast 不可用，使用启发式判断")
                    else:
                        verifast_available = True
                
                if verifast_available:
                    # 使用 VeriFast 结果
                    success, stage = try_verifast_verify(file_path, lang)
                    if success:
                        model_results[lang]["vsr"] += 1
                        model_results[lang]["tcr"] += 1
                        model_results[lang]["sar"] += 1
                    elif stage == "verification":
                        model_results[lang]["tcr"] += 1
                        model_results[lang]["sar"] += 1
                    elif stage == "type":
                        model_results[lang]["sar"] += 1
                else:
                    # 使用启发式判断
                    if heuristic_sar_check(code, lang):
                        model_results[lang]["sar"] += 1
                    if heuristic_tcr_check(code, lang):
                        model_results[lang]["tcr"] += 1
                    # VSR 需要实际验证，启发式无法判定
            
            # 统计
            r = model_results[lang]
            if r["total"] > 0:
                sar_pct = r["sar"] / r["total"] * 100
                tcr_pct = r["tcr"] / r["total"] * 100
                vsr_pct = r["vsr"] / r["total"] * 100
                print(f" ✓ [SAR {sar_pct:5.1f}% | TCR {tcr_pct:5.1f}% | VSR {vsr_pct:5.1f}%]")
        
        results[model] = model_results
    
    return results


def print_summary_table(results: Dict):
    """打印汇总表"""
    print("\n" + "=" * 80)
    print("汇总表格")
    print("=" * 80)
    print()
    
    print(f"{'模型':<15} {'总数':<8} {'SAR':<12} {'TCR':<12} {'VSR':<12}")
    print("-" * 80)
    
    for model in sorted(results.keys()):
        total = sum(results[model][lang]["total"] for lang in ["c", "java", "rust"])
        sar = sum(results[model][lang]["sar"] for lang in ["c", "java", "rust"])
        tcr = sum(results[model][lang]["tcr"] for lang in ["c", "java", "rust"])
        vsr = sum(results[model][lang]["vsr"] for lang in ["c", "java", "rust"])
        
        sar_pct = sar / total * 100 if total > 0 else 0
        tcr_pct = tcr / total * 100 if total > 0 else 0
        vsr_pct = vsr / total * 100 if total > 0 else 0
        
        print(f"{model:<15} {total:<8} {sar:3}/{total:3} ({sar_pct:5.1f}%)  "
              f"{tcr:3}/{total:3} ({tcr_pct:5.1f}%)  {vsr:3}/{total:3} ({vsr_pct:5.1f}%)")
    
    print()


def generate_latex_table(results: Dict):
    """生成 LaTeX 表格代码"""
    print("=" * 80)
    print("LaTeX 表格代码")
    print("=" * 80)
    print()
    
    # 模型名称映射
    model_display = {
        "claude-opus": "Claude",
        "deepseek": "DeepSeek",
        "gpt52": "GPT-5.2",
        "qwen3": "Qwen"
    }
    
    print(r"\begin{table}")
    print(r"\centering")
    print(r"\begin{tabular}{lccc}")
    print(r"\toprule")
    print(r"模型 & SAR & TCR & VSR \\")
    print(r"\midrule")
    
    for model in sorted(results.keys()):
        total = sum(results[model][lang]["total"] for lang in ["c", "java", "rust"])
        sar = sum(results[model][lang]["sar"] for lang in ["c", "java", "rust"])
        tcr = sum(results[model][lang]["tcr"] for lang in ["c", "java", "rust"])
        vsr = sum(results[model][lang]["vsr"] for lang in ["c", "java", "rust"])
        
        sar_pct = sar / total * 100 if total > 0 else 0
        tcr_pct = tcr / total * 100 if total > 0 else 0
        vsr_pct = vsr / total * 100 if total > 0 else 0
        
        display_name = model_display.get(model, model)
        print(f"{display_name:12} & {sar_pct:5.1f}\\% & {tcr_pct:5.1f}\\% & {vsr_pct:5.1f}\\% \\\\")
    
    print(r"\bottomrule")
    print(r"\end{tabular}")
    print(r"\end{table}")
    print()


def save_json_results(results: Dict, output_file: Path):
    """保存结果为 JSON"""
    output_data = {}
    for model in results:
        output_data[model] = {}
        for lang in results[model]:
            r = results[model][lang]
            total = r["total"]
            output_data[model][lang] = {
                "total": total,
                "sar": r["sar"],
                "sar_pct": r["sar"] / total * 100 if total > 0 else 0,
                "tcr": r["tcr"],
                "tcr_pct": r["tcr"] / total * 100 if total > 0 else 0,
                "vsr": r["vsr"],
                "vsr_pct": r["vsr"] / total * 100 if total > 0 else 0,
            }
    
    output_file.write_text(json.dumps(output_data, indent=2, ensure_ascii=False))
    print(f"结果已保存: {output_file}")


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="分析生成文件的 SAR/TCR/VSR 指标")
    parser.add_argument("--input", type=Path, default=Path("output_20260321_064953"),
                        help="输入目录（包含各模型子目录）")
    parser.add_argument("--output", type=Path, default=None,
                        help="保存 JSON 结果的文件")
    
    args = parser.parse_args()
    
    if not args.input.exists():
        print(f"错误: 输入目录不存在: {args.input}")
        return
    
    results = analyze_output_directory(args.input)
    print_summary_table(results)
    generate_latex_table(results)
    
    if args.output:
        save_json_results(results, args.output)


if __name__ == "__main__":
    main()
