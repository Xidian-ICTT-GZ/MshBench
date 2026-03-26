#!/usr/bin/env python3
"""Count files per folder under each language directory."""

import argparse
from pathlib import Path
from typing import Dict, Tuple


def count_files_recursive(folder: Path) -> int:
    return sum(1 for p in folder.rglob("*") if p.is_file())


def collect_counts(root: Path) -> Dict[str, Dict[str, int]]:
    results: Dict[str, Dict[str, int]] = {}

    for lang_dir in sorted(p for p in root.iterdir() if p.is_dir()):
        lang_name = lang_dir.name
        folder_counts: Dict[str, int] = {}

        direct_files = sum(1 for p in lang_dir.iterdir() if p.is_file())
        if direct_files > 0:
            folder_counts["."] = direct_files

        for sub in sorted(p for p in lang_dir.iterdir() if p.is_dir()):
            folder_counts[sub.name] = count_files_recursive(sub)

        folder_counts["__TOTAL__"] = direct_files + sum(
            v for k, v in folder_counts.items() if k not in {".", "__TOTAL__"}
        )
        results[lang_name] = folder_counts

    return results


def print_report(results: Dict[str, Dict[str, int]]) -> None:
    for lang, counts in results.items():
        print(f"\n[{lang}]")
        for folder, cnt in counts.items():
            if folder == "__TOTAL__":
                continue
            label = "(root files)" if folder == "." else folder
            print(f"  {label}: {cnt}")
        print(f"  TOTAL: {counts['__TOTAL__']}")


def parse_args() -> argparse.Namespace:
    repo_root = Path(__file__).resolve().parent.parent
    default_root = repo_root / "ground_true"

    parser = argparse.ArgumentParser(
        description="统计各语言目录下各子文件夹的文件数量（递归统计）。"
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=default_root,
        help=f"待统计根目录，默认: {default_root}",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    root = args.root

    if not root.exists() or not root.is_dir():
        raise FileNotFoundError(f"Root directory not found: {root}")

    results = collect_counts(root)
    if not results:
        print("No language directories found.")
        return

    print_report(results)


if __name__ == "__main__":
    main()
