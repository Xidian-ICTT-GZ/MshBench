from __future__ import annotations

import argparse
import csv
import json
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from statistics import median
from typing import Dict, Iterable, List, Tuple

LANG_EXTENSIONS = {
    "c": {".c"},
    "java": {".java"},
    "rust": {".rs"},
}

STRUCTURE_CANONICAL = {
    "arithmetic": "Arithmetic",
    "arrays": "Arrays",
    "linklist": "Linklist",
    "stack": "Stack",
    "struct": "Struct",
    "tree": "Tree",
    "other": "Other",
}


@dataclass
class FileMetric:
    file_path: str
    language: str
    structure: str
    loc: int
    spec_loc: int
    code_loc: int


def nonempty_lines(text: str) -> List[str]:
    return [line for line in text.splitlines() if line.strip()]


def count_loc_spec_code(text: str) -> Tuple[int, int, int]:
    loc = 0
    spec_loc = 0
    in_spec_block = False

    for raw in text.splitlines():
        if not raw.strip():
            continue

        loc += 1
        line = raw
        stripped = line.lstrip()
        is_spec = False

        if in_spec_block:
            is_spec = True
            if "@*/" in line:
                in_spec_block = False

        if "/*@" in line:
            is_spec = True
            if "@*/" not in line[line.find("/*@"):]:
                in_spec_block = True

        if stripped.startswith("//@") or "//@" in line:
            is_spec = True

        if is_spec:
            spec_loc += 1

    code_loc = loc - spec_loc
    return loc, spec_loc, code_loc


def detect_language(path: Path) -> str | None:
    top = path.parts[0].lower() if path.parts else ""
    suffix = path.suffix.lower()

    if top in LANG_EXTENSIONS and suffix in LANG_EXTENSIONS[top]:
        return top

    for lang, exts in LANG_EXTENSIONS.items():
        if suffix in exts:
            return lang
    return None


def detect_structure(relative_path: Path) -> str:
    if len(relative_path.parts) < 2:
        return "_root"
    raw = relative_path.parts[1].strip()
    key = raw.lower()
    return STRUCTURE_CANONICAL.get(key, raw)


def collect_metrics(root: Path) -> List[FileMetric]:
    metrics: List[FileMetric] = []

    for file_path in sorted(root.rglob("*")):
        if not file_path.is_file():
            continue

        rel = file_path.relative_to(root)
        language = detect_language(rel)
        if language is None:
            continue

        text = file_path.read_text(encoding="utf-8", errors="ignore")
        loc, spec_loc, code_loc = count_loc_spec_code(text)
        metrics.append(
            FileMetric(
                file_path=rel.as_posix(),
                language=language,
                structure=detect_structure(rel),
                loc=loc,
                spec_loc=spec_loc,
                code_loc=code_loc,
            )
        )

    return metrics


def safe_div(a: float, b: float) -> float:
    if b == 0:
        return 0.0
    return a / b


def summarize_group(rows: Iterable[FileMetric], group_name: str, language: str) -> Dict[str, object]:
    items = list(rows)
    sample_count = len(items)
    loc_values = [r.loc for r in items]
    spec_values = [r.spec_loc for r in items]
    code_values = [r.code_loc for r in items]

    total_loc = sum(loc_values)
    total_spec = sum(spec_values)
    total_code = sum(code_values)

    return {
        "language": language,
        "structure": group_name,
        "sample_count": sample_count,
        "Total-LoC": total_loc,
        "Total-Spec-LoC": total_spec,
        "Total-Code-LoC": total_code,
        "Avg-LoC": round(safe_div(total_loc, sample_count), 4),
        "Avg-Spec-LoC": round(safe_div(total_spec, sample_count), 4),
        "Avg-Code-LoC": round(safe_div(total_code, sample_count), 4),
        "MaxLoC": max(loc_values) if loc_values else 0,
        "Max_SpecLoC": max(spec_values) if spec_values else 0,
        "Median-LoC": median(loc_values) if loc_values else 0,
        "Median-Spec-LoC": median(spec_values) if spec_values else 0,
        "Spec/LoC": round(safe_div(total_spec, total_loc), 6),
        "Code/LoC": round(safe_div(total_code, total_loc), 6),
        "Spec/Code": round(safe_div(total_spec, total_code), 6),
    }


def build_summaries(metrics: List[FileMetric]) -> Tuple[List[Dict[str, object]], List[Dict[str, object]], Dict[str, object]]:
    by_lang_struct: Dict[Tuple[str, str], List[FileMetric]] = defaultdict(list)
    by_struct: Dict[str, List[FileMetric]] = defaultdict(list)

    for m in metrics:
        by_lang_struct[(m.language, m.structure)].append(m)
        by_struct[m.structure].append(m)

    lang_struct_rows: List[Dict[str, object]] = []
    for (lang, struct), rows in sorted(by_lang_struct.items()):
        lang_struct_rows.append(summarize_group(rows, struct, lang))

    struct_rows: List[Dict[str, object]] = []
    for struct, rows in sorted(by_struct.items()):
        struct_rows.append(summarize_group(rows, struct, "all"))

    overall = summarize_group(metrics, "all", "all")
    return lang_struct_rows, struct_rows, overall


def build_by_language_nested(rows: List[Dict[str, object]]) -> Dict[str, List[Dict[str, object]]]:
    out: Dict[str, List[Dict[str, object]]] = defaultdict(list)
    for row in rows:
        lang = str(row["language"])
        out[lang].append(row)
    return dict(sorted(out.items()))


def write_csv(path: Path, rows: List[Dict[str, object]]) -> None:
    if not rows:
        path.write_text("", encoding="utf-8")
        return

    headers = list(rows[0].keys())
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=headers)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def write_markdown(path: Path, title: str, rows: List[Dict[str, object]]) -> None:
    if not rows:
        path.write_text(f"# {title}\n\nNo data.\n", encoding="utf-8")
        return

    headers = list(rows[0].keys())
    lines = [f"# {title}", "", "| " + " | ".join(headers) + " |", "| " + " | ".join(["---"] * len(headers)) + " |"]
    for row in rows:
        lines.append("| " + " | ".join(str(row[h]) for h in headers) + " |")
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def write_grouped_markdown(path: Path, title: str, rows: List[Dict[str, object]], overall: Dict[str, object]) -> None:
    lines: List[str] = [f"# {title}", ""]

    overview_headers = [
        "sample_count",
        "Total-LoC",
        "Total-Spec-LoC",
        "Total-Code-LoC",
        "Avg-LoC",
        "Avg-Spec-LoC",
        "MaxLoC",
        "Max_SpecLoC",
        "Spec/LoC",
    ]
    lines.append("## Overall")
    lines.append("")
    lines.append("| " + " | ".join(overview_headers) + " |")
    lines.append("| " + " | ".join(["---"] * len(overview_headers)) + " |")
    lines.append("| " + " | ".join(str(overall[h]) for h in overview_headers) + " |")
    lines.append("")

    per_language: Dict[str, List[Dict[str, object]]] = defaultdict(list)
    for row in rows:
        per_language[str(row["language"])].append(row)

    metric_headers = [
        "structure",
        "sample_count",
        "Avg-LoC",
        "Avg-Spec-LoC",
        "Avg-Code-LoC",
        "MaxLoC",
        "Max_SpecLoC",
        "Spec/LoC",
        "Spec/Code",
    ]

    for language in sorted(per_language):
        lines.append(f"## Language: {language}")
        lines.append("")
        lines.append("| " + " | ".join(metric_headers) + " |")
        lines.append("| " + " | ".join(["---"] * len(metric_headers)) + " |")
        for row in sorted(per_language[language], key=lambda x: str(x["structure"])):
            lines.append("| " + " | ".join(str(row[h]) for h in metric_headers) + " |")
        lines.append("")

    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute dataset stats for code/spec distribution in ground_true.")
    parser.add_argument("--root", default="ground_true", help="Dataset root directory.")
    parser.add_argument("--out-dir", default="output_log", help="Output directory for statistics files.")
    parser.add_argument("--prefix", default="ground_true_dataset_stats", help="Output file prefix.")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    if not root.exists():
        raise FileNotFoundError(f"Root not found: {root}")

    out_dir = Path(args.out_dir).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    metrics = collect_metrics(root)
    lang_struct_rows, struct_rows, overall = build_summaries(metrics)

    json_path = out_dir / f"{args.prefix}.json"
    csv_lang_struct_path = out_dir / f"{args.prefix}_by_language_structure.csv"
    csv_struct_path = out_dir / f"{args.prefix}_by_structure.csv"
    md_lang_struct_path = out_dir / f"{args.prefix}_by_language_structure.md"
    md_struct_path = out_dir / f"{args.prefix}_by_structure.md"
    md_grouped_path = out_dir / f"{args.prefix}_grouped_by_language.md"
    json_by_language_path = out_dir / f"{args.prefix}_by_language_nested.json"

    report = {
        "root": str(root),
        "file_count": len(metrics),
        "overall": overall,
        "by_language_structure": lang_struct_rows,
        "by_language_nested": build_by_language_nested(lang_struct_rows),
        "by_structure": struct_rows,
    }

    json_path.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
    write_csv(csv_lang_struct_path, lang_struct_rows)
    write_csv(csv_struct_path, struct_rows)
    write_markdown(md_lang_struct_path, "Ground Truth Stats by Language and Structure", lang_struct_rows)
    write_markdown(md_struct_path, "Ground Truth Stats by Structure", struct_rows)
    write_grouped_markdown(md_grouped_path, "Ground Truth Dataset Dashboard", lang_struct_rows, overall)
    json_by_language_path.write_text(
        json.dumps(report["by_language_nested"], ensure_ascii=False, indent=2),
        encoding="utf-8",
    )

    print(f"[done] json={json_path}")
    print(f"[done] csv_by_language_structure={csv_lang_struct_path}")
    print(f"[done] csv_by_structure={csv_struct_path}")
    print(f"[done] md_by_language_structure={md_lang_struct_path}")
    print(f"[done] md_by_structure={md_struct_path}")
    print(f"[done] md_grouped_by_language={md_grouped_path}")
    print(f"[done] json_by_language_nested={json_by_language_path}")


if __name__ == "__main__":
    main()
