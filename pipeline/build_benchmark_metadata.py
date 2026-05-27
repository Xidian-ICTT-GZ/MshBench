from __future__ import annotations

import argparse
import csv
from pathlib import Path
from typing import Dict, List, Tuple

from .stat_ground_true_dataset import count_loc_spec_code, detect_structure

LANG_EXTENSIONS = {
    "c": {".c"},
    "java": {".java"},
    "rust": {".rs"},
}


def detect_language(path: Path) -> str | None:
    top = path.parts[0].lower() if path.parts else ""
    suffix = path.suffix.lower()
    if top in LANG_EXTENSIONS and suffix in LANG_EXTENSIONS[top]:
        return top
    for lang, exts in LANG_EXTENSIONS.items():
        if suffix in exts:
            return lang
    return None


def collect_files(root: Path) -> List[Path]:
    files: List[Path] = []
    for file_path in sorted(root.rglob("*")):
        if not file_path.is_file():
            continue
        rel = file_path.relative_to(root)
        if detect_language(rel) is None:
            continue
        files.append(file_path)
    return files


def write_metadata(rows: List[Dict[str, object]], out_path: Path) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    headers = [
        "sample_id",
        "file_path",
        "language",
        "structure",
        "loc_total",
        "loc_spec",
        "loc_code",
        "is_in_benchmark",
    ]
    with out_path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=headers)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def main() -> None:
    parser = argparse.ArgumentParser(description="Build benchmark metadata CSV.")
    parser.add_argument("--root", default="benchmark", help="Benchmark root directory.")
    parser.add_argument("--out", default="data/benchmark_metadata.csv", help="Output CSV path.")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    if not root.exists():
        raise FileNotFoundError(f"Root not found: {root}")

    rows: List[Dict[str, object]] = []
    for idx, file_path in enumerate(collect_files(root), start=1):
        rel = file_path.relative_to(root)
        language = detect_language(rel)
        if language is None:
            continue
        text = file_path.read_text(encoding="utf-8", errors="ignore")
        loc, spec_loc, code_loc = count_loc_spec_code(text)
        rows.append(
            {
                "sample_id": f"S{idx:04d}",
                "file_path": rel.as_posix(),
                "language": language,
                "structure": detect_structure(rel),
                "loc_total": loc,
                "loc_spec": spec_loc,
                "loc_code": code_loc,
                "is_in_benchmark": True,
            }
        )

    write_metadata(rows, Path(args.out).resolve())
    print(f"[done] metadata={Path(args.out).resolve()}")


if __name__ == "__main__":
    main()
