#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import json
import csv
from pathlib import Path
from datetime import datetime

GROUND_TRUE_ROOT = Path(__file__).resolve().parent.parent / "ground_true"

def count_lines(file_path):
    """Count total, code, and spec annotation lines."""
    try:
        content = file_path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return {"total": 0, "code": 0, "spec": 0}
    
    lines = content.splitlines()
    total = len(lines)
    code = 0
    spec = 0
    
    for line in lines:
        stripped = line.strip()
        
        # Track block annotations (/*@ ... @*/)
        if "/*@" in line and "@*/" in line:
            spec += 1
        elif "/*@" in line:
            spec += 1
        elif "@*/" in line:
            spec += 1
        
        # Track line specs (//@ ...)
        elif "//@ " in line:
            spec += 1
        else:
            if stripped and not stripped.startswith("*"):
                code += 1
    
    return {
        "total": total,
        "code": code,
        "spec": spec
    }

def get_ext(lang):
    """Get file extension for language."""
    exts = {"c": ".c", "java": ".java", "rust": ".rs"}
    return exts.get(lang, "")

def analyze_ground_true():
    """Analyze ground_true data structure by language and category."""
    results = {}
    
    # Iterate through c, java, rust
    for lang_dir in GROUND_TRUE_ROOT.iterdir():
        if not lang_dir.is_dir():
            continue
        
        lang = lang_dir.name
        results[lang] = {}
        
        # Iterate through categories (Arithmetic, Arrays, Linklist, etc.)
        for cat_dir in lang_dir.iterdir():
            if not cat_dir.is_dir():
                continue
            
            category = cat_dir.name
            files = list(cat_dir.glob(f"*{get_ext(lang)}"))
            
            if not files:
                continue
            
            total_files = len(files)
            total_lines = 0
            total_code = 0
            total_spec = 0
            
            for file_path in files:
                counts = count_lines(file_path)
                total_lines += counts["total"]
                total_code += counts["code"]
                total_spec += counts["spec"]
            
            avg_lines = total_lines // total_files if total_files > 0 else 0
            
            results[lang][category] = {
                "files": total_files,
                "total_lines": total_lines,
                "code_lines": total_code,
                "spec_lines": total_spec,
                "avg_file_lines": avg_lines,
                "spec_ratio": round(total_spec / total_lines * 100 if total_lines > 0 else 0, 2)
            }
    
    return results

def print_statistics(results):
    """Print human-readable statistics."""
    print("\n" + "=" * 130)
    print("GROUND_TRUE DATASET STATISTICS (按语言分类)")
    print("=" * 130)
    
    for lang in sorted(results.keys()):
        print(f"\n{'=' * 130}")
        print(f"✓ 语言: {lang.upper()}")
        print(f"{'=' * 130}")
        print(f"{'数据结构':<15} {'文件数':<10} {'总代码行':<12} {'代码行':<12} {'规约行':<12} {'平均行数':<12} {'规约占比':<10}")
        print("-" * 130)
        
        lang_total_files = 0
        lang_total_lines = 0
        lang_total_code = 0
        lang_total_spec = 0
        
        for category in sorted(results[lang].keys()):
            stats = results[lang][category]
            spec_pct = stats["spec_ratio"]
            
            print(f"{category:<15} {stats['files']:<10} {stats['total_lines']:<12} {stats['code_lines']:<12} {stats['spec_lines']:<12} {stats['avg_file_lines']:<12} {spec_pct:<10.1f}%")
            
            lang_total_files += stats["files"]
            lang_total_lines += stats["total_lines"]
            lang_total_code += stats["code_lines"]
            lang_total_spec += stats["spec_lines"]
        
        print("-" * 130)
        lang_spec_pct = (lang_total_spec / lang_total_lines * 100) if lang_total_lines > 0 else 0
        avg_file_lines = lang_total_lines // lang_total_files if lang_total_files > 0 else 0
        print(f"{'总计':<15} {lang_total_files:<10} {lang_total_lines:<12} {lang_total_code:<12} {lang_total_spec:<12} {avg_file_lines:<12} {lang_spec_pct:<10.1f}%")
    
    # Overall summary
    print("\n" + "=" * 130)
    print("总体统计摘要")
    print("=" * 130)
    
    overall_files = 0
    overall_lines = 0
    overall_code = 0
    overall_spec = 0
    
    for lang in results:
        for category in results[lang]:
            stats = results[lang][category]
            overall_files += stats["files"]
            overall_lines += stats["total_lines"]
            overall_code += stats["code_lines"]
            overall_spec += stats["spec_lines"]
    
    overall_spec_pct = (overall_spec / overall_lines * 100) if overall_lines > 0 else 0
    print(f"总文件数:       {overall_files}")
    print(f"总代码行:       {overall_lines}")
    print(f"代码行:         {overall_code}")
    print(f"规约行:         {overall_spec}")
    print(f"规约占比:       {overall_spec_pct:.1f}%")
    print("=" * 130)

def generate_json_report(results, output_path):
    """Generate JSON report."""
    report = {
        "timestamp": datetime.now().isoformat(),
        "root": str(GROUND_TRUE_ROOT),
        "data": results,
        "summary": {}
    }
    
    # Add summary statistics
    total_files = 0
    total_lines = 0
    total_code = 0
    total_spec = 0
    
    for lang in results:
        for category in results[lang]:
            stats = results[lang][category]
            total_files += stats["files"]
            total_lines += stats["total_lines"]
            total_code += stats["code_lines"]
            total_spec += stats["spec_lines"]
    
    report["summary"] = {
        "total_files": total_files,
        "total_lines": total_lines,
        "total_code_lines": total_code,
        "total_spec_lines": total_spec,
        "overall_spec_ratio": round(total_spec / total_lines * 100 if total_lines > 0 else 0, 2)
    }
    
    output_path.write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"✓ JSON 报告已保存: {output_path}")

def generate_csv_reports(results, output_dir):
    """Generate CSV reports by language."""
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # 1. Per-language detailed reports
    for lang in sorted(results.keys()):
        csv_path = output_dir / f"ground_true_{lang}_detailed.csv"
        
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(["数据结构", "文件数", "总代码行", "代码行", "规约行", "平均行数", "规约占比(%)"])
            
            lang_total_files = 0
            lang_total_lines = 0
            lang_total_code = 0
            lang_total_spec = 0
            
            for category in sorted(results[lang].keys()):
                stats = results[lang][category]
                writer.writerow([
                    category,
                    stats["files"],
                    stats["total_lines"],
                    stats["code_lines"],
                    stats["spec_lines"],
                    stats["avg_file_lines"],
                    f"{stats['spec_ratio']:.1f}"
                ])
                
                lang_total_files += stats["files"]
                lang_total_lines += stats["total_lines"]
                lang_total_code += stats["code_lines"]
                lang_total_spec += stats["spec_lines"]
            
            lang_spec_pct = (lang_total_spec / lang_total_lines * 100) if lang_total_lines > 0 else 0
            avg_file_lines = lang_total_lines // lang_total_files if lang_total_files > 0 else 0
            writer.writerow([])
            writer.writerow(["总计", lang_total_files, lang_total_lines, lang_total_code, lang_total_spec, avg_file_lines, f"{lang_spec_pct:.1f}"])
        
        print(f"✓ {lang.upper()} CSV 已保存: {csv_path}")
    
    # 2. Language comparison summary
    summary_path = output_dir / "ground_true_language_summary.csv"
    with open(summary_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["语言", "总文件数", "总代码行", "代码行", "规约行", "规约占比(%)"])
        
        for lang in sorted(results.keys()):
            lang_total_files = 0
            lang_total_lines = 0
            lang_total_code = 0
            lang_total_spec = 0
            
            for category in results[lang]:
                stats = results[lang][category]
                lang_total_files += stats["files"]
                lang_total_lines += stats["total_lines"]
                lang_total_code += stats["code_lines"]
                lang_total_spec += stats["spec_lines"]
            
            lang_spec_pct = (lang_total_spec / lang_total_lines * 100) if lang_total_lines > 0 else 0
            writer.writerow([
                lang.upper(),
                lang_total_files,
                lang_total_lines,
                lang_total_code,
                lang_total_spec,
                f"{lang_spec_pct:.1f}"
            ])
    
    print(f"✓ 语言对比汇总 CSV 已保存: {summary_path}")

def main():
    print("\n正在分析 ground_true 数据集...")
    results = analyze_ground_true()
    
    print_statistics(results)
    
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_dir = Path(__file__).resolve().parent.parent / "output_log"
    output_dir.mkdir(parents=True, exist_ok=True)
    
    json_report = output_dir / f"ground_true_analysis_{ts}.json"
    generate_json_report(results, json_report)
    
    csv_dir = output_dir / f"ground_true_csv_{ts}"
    generate_csv_reports(results, csv_dir)
    
    print("\n" + "=" * 130)
    print("✓ 分析完成!")
    print("=" * 130)
    print(f"JSON 报告: {json_report}")
    print(f"CSV 目录: {csv_dir}")

if __name__ == "__main__":
    main()

