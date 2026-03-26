#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse
import csv
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
GROUND_TRUE = ROOT / "ground_true"
OUTPUT_LOG = ROOT / "output_log"

LANG_EXT = {
    "c": ".c",
    "java": ".java",
    "rust": ".rs",
}

LANG_DISPLAY = {
    "c": "C",
    "java": "Java",
    "rust": "Rust",
}


@dataclass
class FileStats:
    total: int
    spec: int


def count_lines(file_path: Path) -> FileStats:
    text = file_path.read_text(encoding="utf-8", errors="ignore")
    lines = text.splitlines()

    total = len(lines)
    spec = 0

    in_block_spec = False
    for line in lines:
        stripped = line.strip()

        if "/*@" in line:
            in_block_spec = True
            spec += 1
            if "@*/" in line:
                in_block_spec = False
            continue

        if in_block_spec:
            spec += 1
            if "@*/" in line:
                in_block_spec = False
            continue

        if stripped.startswith("//@") or " //@" in line:
            spec += 1

    return FileStats(total=total, spec=spec)


def collect_stats() -> Dict[str, Dict[str, List[FileStats]]]:
    result: Dict[str, Dict[str, List[FileStats]]] = {}

    for lang in sorted(LANG_EXT.keys()):
        lang_dir = GROUND_TRUE / lang
        if not lang_dir.exists() or not lang_dir.is_dir():
            continue

        categories: Dict[str, List[FileStats]] = {}
        ext = LANG_EXT[lang]

        for cat_dir in sorted(lang_dir.iterdir(), key=lambda p: p.name.lower()):
            if not cat_dir.is_dir():
                continue
            files = sorted(cat_dir.glob(f"*{ext}"))
            if not files:
                continue

            file_stats = [count_lines(p) for p in files]
            categories[cat_dir.name] = file_stats

        if categories:
            result[lang] = categories

    return result


def calc_row(file_stats: List[FileStats]) -> Tuple[int, float, float, int, int]:
    number = len(file_stats)
    total_loc = sum(s.total for s in file_stats)
    total_spec = sum(s.spec for s in file_stats)
    avg_loc = total_loc / number if number else 0.0
    avg_spec = total_spec / number if number else 0.0
    max_loc = max((s.total for s in file_stats), default=0)
    max_spec = max((s.spec for s in file_stats), default=0)
    return number, avg_loc, avg_spec, max_loc, max_spec


def build_table_rows(stats: Dict[str, Dict[str, List[FileStats]]]) -> List[Tuple[str, str, int, float, float, int, int]]:
    rows: List[Tuple[str, str, int, float, float, int, int]] = []

    all_files: List[FileStats] = []

    for lang in sorted(stats.keys()):
        lang_files: List[FileStats] = []

        for category in sorted(stats[lang].keys(), key=lambda s: s.lower()):
            fs = stats[lang][category]
            lang_files.extend(fs)
            all_files.extend(fs)

            number, avg_loc, avg_spec, max_loc, max_spec = calc_row(fs)
            rows.append((LANG_DISPLAY.get(lang, lang.upper()), category, number, avg_loc, avg_spec, max_loc, max_spec))

        l_number, l_avg_loc, l_avg_spec, l_max_loc, l_max_spec = calc_row(lang_files)
        rows.append((LANG_DISPLAY.get(lang, lang.upper()), "All", l_number, l_avg_loc, l_avg_spec, l_max_loc, l_max_spec))

    a_number, a_avg_loc, a_avg_spec, a_max_loc, a_max_spec = calc_row(all_files)
    rows.append(("All", "All", a_number, a_avg_loc, a_avg_spec, a_max_loc, a_max_spec))

    return rows


def write_csv(rows: List[Tuple[str, str, int, float, float, int, int]], out_path: Path) -> None:
    with out_path.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["Source", "Data-source", "Number", "Avg-LoC", "Avg-Spec-LoC", "Max-LoC", "Max-Spec-LoC"])
        for source, ds, num, avg_loc, avg_spec, max_loc, max_spec in rows:
            w.writerow([source, ds, num, f"{avg_loc:.1f}", f"{avg_spec:.1f}", max_loc, max_spec])


def write_markdown(rows: List[Tuple[str, str, int, float, float, int, int]], out_path: Path, title: str) -> None:
    lines = [
        f"## {title}",
        "",
        "| Source | Data-source | Number | Avg-LoC | Avg-Spec-LoC | Max-LoC | Max-Spec-LoC |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for source, ds, num, avg_loc, avg_spec, max_loc, max_spec in rows:
        lines.append(
            f"| {source} | {ds} | {num} | {avg_loc:.1f} | {avg_spec:.1f} | {max_loc} | {max_spec} |"
        )
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def latex_escape(text: str) -> str:
    escaped = text.replace("\\", "\\textbackslash{}")
    escaped = escaped.replace("&", "\\&")
    escaped = escaped.replace("%", "\\%")
    escaped = escaped.replace("$", "\\$")
    escaped = escaped.replace("#", "\\#")
    escaped = escaped.replace("_", "\\_")
    escaped = escaped.replace("{", "\\{")
    escaped = escaped.replace("}", "\\}")
    escaped = escaped.replace("~", "\\textasciitilde{}")
    escaped = escaped.replace("^", "\\textasciicircum{}")
    return escaped


def write_latex_three_line(rows: List[Tuple[str, str, int, float, float, int, int]], out_path: Path, title: str) -> None:
    lines: List[str] = []
    lines.append("% Requires: \\usepackage{booktabs,graphicx}")
    lines.append("\\begin{table}[t]")
    lines.append("  \\centering")
    lines.append("  \\scriptsize")
    lines.append("  \\setlength{\\tabcolsep}{3.2pt}")
    lines.append("  \\renewcommand{\\arraystretch}{0.95}")
    lines.append(f"  \\caption{{{latex_escape(title)}}}")
    lines.append("  \\resizebox{\\columnwidth}{!}{%")
    lines.append("  \\begin{tabular}{llrrrrr}")
    lines.append("    \\toprule")
    lines.append("    Source & Data-source & Number & Avg-LoC & Avg-Spec-LoC & Max-LoC & Max-Spec-LoC \\\\")
    lines.append("    \\midrule")

    prev_source = ""
    for source, ds, num, avg_loc, avg_spec, max_loc, max_spec in rows:
        source_cell = source if source != prev_source else ""
        prev_source = source
        lines.append(
            "    "
            + f"{latex_escape(source_cell)} & {latex_escape(ds)} & {num} & {avg_loc:.1f} & {avg_spec:.1f} & {max_loc} & {max_spec} \\\\"
        )
        if ds == "All" and source != "All":
            lines.append("    \\addlinespace[1pt]")

    lines.append("    \\bottomrule")
    lines.append("  \\end{tabular}")
    lines.append("  }")
    lines.append("\\end{table}")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def xml_escape(text: str) -> str:
    return (
        text.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
        .replace("'", "&apos;")
    )


def write_svg(rows: List[Tuple[str, str, int, float, float, int, int]], out_path: Path, title: str) -> None:
    headers = ["Source", "Data-source", "Number", "Avg-LoC", "Avg-Spec-LoC", "Max-LoC", "Max-Spec-LoC"]
    widths = [120, 210, 90, 95, 130, 95, 120]

    left = 40
    top = 70
    row_h = 34
    table_w = sum(widths)
    table_h = row_h * (len(rows) + 1)
    svg_w = left * 2 + table_w
    svg_h = top + table_h + 50

    x_pos = [left]
    for w in widths[:-1]:
        x_pos.append(x_pos[-1] + w)

    parts: List[str] = []
    parts.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{svg_w}" height="{svg_h}">')
    parts.append('<rect x="0" y="0" width="100%" height="100%" fill="white"/>')
    parts.append(
        f'<text x="{svg_w/2:.1f}" y="36" text-anchor="middle" font-size="26" '
        f'font-family="Times New Roman, serif" font-weight="bold">{xml_escape(title)}</text>'
    )

    parts.append(
        f'<rect x="{left}" y="{top}" width="{table_w}" height="{table_h}" fill="white" stroke="#333" stroke-width="1.2"/>'
    )

    for i in range(1, len(rows) + 1):
        y = top + row_h * i
        stroke = "#333" if i in (1, len(rows), len(rows) - 1) else "#999"
        width = "1.1" if i in (1, len(rows), len(rows) - 1) else "0.8"
        parts.append(f'<line x1="{left}" y1="{y}" x2="{left + table_w}" y2="{y}" stroke="{stroke}" stroke-width="{width}"/>')

    for i, w in enumerate(widths[:-1]):
        x = left + sum(widths[: i + 1])
        parts.append(f'<line x1="{x}" y1="{top}" x2="{x}" y2="{top + table_h}" stroke="#999" stroke-width="0.8"/>')

    for i, h in enumerate(headers):
        x = x_pos[i] + widths[i] / 2
        y = top + row_h / 2 + 6
        parts.append(
            f'<text x="{x:.1f}" y="{y:.1f}" text-anchor="middle" font-size="16" '
            f'font-family="Times New Roman, serif" font-weight="bold">{xml_escape(h)}</text>'
        )

    for r, row in enumerate(rows):
        y = top + row_h * (r + 1) + row_h / 2 + 6
        source, ds, num, avg_loc, avg_spec, max_loc, max_spec = row
        cells = [source, ds, str(num), f"{avg_loc:.1f}", f"{avg_spec:.1f}", str(max_loc), str(max_spec)]
        for c, cell in enumerate(cells):
            align_right = c >= 2
            if align_right:
                x = x_pos[c] + widths[c] - 10
                anchor = "end"
            else:
                x = x_pos[c] + 8
                anchor = "start"
            weight = "bold" if ds == "All" or (source == "All" and ds == "All") else "normal"
            parts.append(
                f'<text x="{x:.1f}" y="{y:.1f}" text-anchor="{anchor}" font-size="15" '
                f'font-family="Times New Roman, serif" font-weight="{weight}">{xml_escape(cell)}</text>'
            )

    parts.append("</svg>")
    out_path.write_text("\n".join(parts), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Render paper-style table for ground_true statistics")
    parser.add_argument("--output-dir", type=Path, default=OUTPUT_LOG, help="Output directory")
    parser.add_argument("--title", type=str, default="Table: Statistics of Ground Truth Sources")
    args = parser.parse_args()

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_dir = args.output_dir / f"ground_true_table_{ts}"
    out_dir.mkdir(parents=True, exist_ok=True)

    stats = collect_stats()
    rows = build_table_rows(stats)

    csv_path = out_dir / "ground_true_table.csv"
    md_path = out_dir / "ground_true_table.md"
    svg_path = out_dir / "ground_true_table.svg"
    tex_path = out_dir / "ground_true_table_three_line.tex"

    write_csv(rows, csv_path)
    write_markdown(rows, md_path, args.title)
    write_svg(rows, svg_path, args.title)
    write_latex_three_line(rows, tex_path, args.title)

    print(f"Saved CSV: {csv_path}")
    print(f"Saved Markdown: {md_path}")
    print(f"Saved SVG: {svg_path}")
    print(f"Saved LaTeX (three-line): {tex_path}")


if __name__ == "__main__":
    main()
