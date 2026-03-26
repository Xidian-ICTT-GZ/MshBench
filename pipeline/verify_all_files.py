#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse
import subprocess
from datetime import datetime
from pathlib import Path

import matplotlib.pyplot as plt

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_INPUT = REPO_ROOT / "output_20260318_123118"
DEFAULT_OUTPUT = REPO_ROOT / "output_log" / f"verifast_pass_table_{datetime.now().strftime('%Y%m%d_%H%M%S')}.pdf"

LANG_ORDER = ["c", "java", "rust"]
EXT_BY_LANG = {"c": ".c", "java": ".java", "rust": ".rs"}


def run_verifast(file_path: Path, lang: str, timeout: int) -> bool:
    try:
        if lang == "c":
            cmd = ["verifast", "-shared", str(file_path)]
        elif lang == "java":
            # Java files may require emitting vfmanifest to avoid link-phase false failures.
            cmd = ["verifast", "-emit_vfmanifest", str(file_path)]
        else:
            cmd = ["verifast", str(file_path)]

        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        out = result.stdout or ""
        # Unified policy for all languages: pass iff verifier reports zero errors.
        return "0 errors found" in out
    except subprocess.TimeoutExpired:
        return False
    except Exception:
        return False


def collect_files(root: Path, lang: str):
    ext = EXT_BY_LANG[lang]
    if not root.exists():
        return []
    return [p for p in root.rglob(f"*{ext}") if p.is_file()]


def verify_model_language(model_root: Path, lang: str, timeout: int):
    lang_root = model_root / lang
    files = collect_files(lang_root, lang)
    passed = 0
    for f in files:
        if run_verifast(f, lang, timeout):
            passed += 1
    return passed, len(files)


def build_table(results, models):
    headers = ["Model", "C", "Java", "Rust", "Total"]
    rows = []

    for model in models:
        row = [model]
        total = 0
        for lang in LANG_ORDER:
            passed, _total = results[model][lang]
            row.append(str(passed))
            total += passed
        row.append(str(total))
        rows.append(row)

    return headers, rows


def render_pdf_table(headers, rows, out_pdf: Path, title: str):
    fig, ax = plt.subplots(figsize=(8.2, 2.2 + 0.35 * len(rows)))
    ax.axis("off")

    table = ax.table(
        cellText=rows,
        colLabels=headers,
        loc="center",
        cellLoc="center",
    )
    table.auto_set_font_size(False)
    table.set_fontsize(11)
    table.scale(1, 1.35)

    ax.set_title(title, fontsize=13, pad=10)
    fig.tight_layout()
    out_pdf.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_pdf, format="pdf")
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(
        description="Verify VeriFast pass counts by model and language and export PDF table"
    )
    parser.add_argument(
        "--input",
        type=Path,
        default=DEFAULT_INPUT,
        help="Output directory to verify (default: output_20260318_123118)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="PDF file path to write (default includes timestamp)",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=120,
        help="VeriFast timeout seconds per file",
    )
    parser.add_argument(
        "--title",
        default="VeriFast Verified Programs by Model and Language",
        help="Table title",
    )
    args = parser.parse_args()

    input_root = args.input.resolve()
    if not input_root.exists():
        raise SystemExit(f"Input directory not found: {input_root}")

    models = [p.name for p in input_root.iterdir() if p.is_dir()]
    models.sort()

    results = {m: {} for m in models}

    for model in models:
        model_root = input_root / model
        for lang in LANG_ORDER:
            passed, total = verify_model_language(model_root, lang, args.timeout)
            results[model][lang] = (passed, total)
            print(f"{model}/{lang}: {passed}/{total}")

    headers, rows = build_table(results, models)
    render_pdf_table(headers, rows, args.output, args.title)
    print(f"PDF saved: {args.output}")


if __name__ == "__main__":
    main()