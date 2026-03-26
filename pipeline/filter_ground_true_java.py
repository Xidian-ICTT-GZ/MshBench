#!/usr/bin/env python3
"""Collect ground_true Java sources that pass VeriFast logs into a new folder."""

import argparse
import shutil
from pathlib import Path
from typing import Set, Tuple

PASS_TOKEN = "0 errors found"


def default_paths() -> Tuple[Path, Path, Path]:
    repo_root = Path(__file__).resolve().parent.parent
    src_dir = repo_root / "ground_true" / "java"
    log_dir = repo_root / "ground_ture_logs" / "java"
    dest_dir = repo_root / "ground_true_java_pass"
    return src_dir, log_dir, dest_dir


def collect_pass_relpaths(log_dir: Path) -> Set[Path]:
    if not log_dir.exists():
        raise FileNotFoundError(f"Log directory not found: {log_dir}")

    pass_set: Set[Path] = set()
    for log_path in log_dir.rglob("*.log"):
        try:
            content = log_path.read_text(encoding="utf-8", errors="ignore")
        except Exception as exc:  # pragma: no cover
            print(f"Failed to read {log_path}: {exc}")
            continue
        if PASS_TOKEN in content:
            rel = log_path.relative_to(log_dir).with_suffix("")
            if rel.suffix == ".java":
                pass_set.add(rel)
    return pass_set


def ensure_clean_destination(dest_dir: Path, overwrite: bool) -> None:
    if dest_dir.exists():
        if not overwrite:
            raise FileExistsError(
                f"Destination {dest_dir} already exists. Use --overwrite to reset it."
            )
        shutil.rmtree(dest_dir)
    dest_dir.mkdir(parents=True, exist_ok=True)


def copy_pass_files(
    src_dir: Path,
    dest_dir: Path,
    pass_relpaths: Set[Path],
    dry_run: bool = False,
) -> None:
    copied = 0
    missing = 0

    for rel_path in sorted(pass_relpaths):
        src_file = src_dir / rel_path
        if not src_file.exists():
            print(f"WARNING: Source file missing for log entry: {src_file}")
            missing += 1
            continue
        dest_file = dest_dir / rel_path
        if dry_run:
            print(f"[DRY-RUN] Would copy {rel_path}")
        else:
            dest_file.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src_file, dest_file)
            print(f"Copied {rel_path}")
        copied += 1

    print(f"Copied {copied} PASS files into {dest_dir}")
    if missing:
        print(f"Skipped {missing} entries because source files were missing")


def parse_args() -> argparse.Namespace:
    src_default, log_default, dest_default = default_paths()
    parser = argparse.ArgumentParser(
        description=(
            "Collect ground_true Java files whose logs contain '0 errors found' into a new folder."
        )
    )
    parser.add_argument("--src", type=Path, default=src_default, help=f"Source Java directory (default: {src_default})")
    parser.add_argument("--logs", type=Path, default=log_default, help=f"Log directory (default: {log_default})")
    parser.add_argument(
        "--dest",
        type=Path,
        default=dest_default,
        help=f"Destination directory for PASS files (default: {dest_default})",
    )
    parser.add_argument(
        "--overwrite",
        action="store_true",
        help="Remove destination directory if it already exists.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show which files would be copied without writing them.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    pass_relpaths = collect_pass_relpaths(args.logs)
    if not pass_relpaths:
        print("No PASS logs found. Nothing to copy.")
        return
    ensure_clean_destination(args.dest, args.overwrite)
    copy_pass_files(args.src, args.dest, pass_relpaths, dry_run=args.dry_run)


if __name__ == "__main__":
    main()
