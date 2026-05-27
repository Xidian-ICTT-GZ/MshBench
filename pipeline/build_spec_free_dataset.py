from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Dict, List, Tuple

from .experiment_utils import split_spec_and_code, save_text, save_json


def load_metadata(path: Path) -> List[Dict[str, str]]:
    with path.open("r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        return [dict(row) for row in reader]


def build_dataset(metadata_path: Path, benchmark_root: Path, out_dir: Path) -> None:
    rows = load_metadata(metadata_path)
    out_dir.mkdir(parents=True, exist_ok=True)

    for row in rows:
        sample_id = row["sample_id"]
        rel_path = row["file_path"]
        file_path = (benchmark_root / rel_path).resolve()
        if not file_path.exists():
            raise FileNotFoundError(f"Missing benchmark file: {file_path}")

        text = file_path.read_text(encoding="utf-8", errors="ignore")
        spec_lines, code_lines = split_spec_and_code(text)
        spec_text = "".join(spec_lines).strip() + ("\n" if spec_lines else "")
        code_text = "".join(code_lines)
        if not code_text.endswith("\n"):
            code_text += "\n"

        sample_dir = out_dir / sample_id
        sample_dir.mkdir(parents=True, exist_ok=True)

        original_path = sample_dir / f"original{file_path.suffix}"
        input_path = sample_dir / f"input_no_spec{file_path.suffix}"
        spec_path = sample_dir / "ground_truth_spec.txt"
        metadata_json = sample_dir / "metadata.json"

        save_text(original_path, text if text.endswith("\n") else text + "\n")
        save_text(input_path, code_text)
        save_text(spec_path, spec_text)

        payload = {
            **row,
            "original_path": original_path.as_posix(),
            "input_no_spec_path": input_path.as_posix(),
            "ground_truth_spec_path": spec_path.as_posix(),
        }
        save_json(metadata_json, payload)

    print(f"[done] dataset={out_dir}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Build spec-free dataset from benchmark metadata.")
    parser.add_argument("--metadata", default="data/benchmark_metadata.csv", help="Metadata CSV path.")
    parser.add_argument("--benchmark-root", default="benchmark", help="Benchmark root directory.")
    parser.add_argument("--out-dir", default="data/benchmark", help="Output dataset directory.")
    args = parser.parse_args()

    build_dataset(Path(args.metadata).resolve(), Path(args.benchmark_root).resolve(), Path(args.out_dir).resolve())


if __name__ == "__main__":
    main()
