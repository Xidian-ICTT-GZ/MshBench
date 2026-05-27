from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Tuple


def load_rows(path: Path) -> List[Dict[str, str]]:
    if not path.exists():
        return []
    with path.open("r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        return [dict(row) for row in reader]


def as_bool(value: str) -> bool:
    return str(value).lower() == "true"


def summarize(initial_rows: List[Dict[str, str]], repair_rows: List[Dict[str, str]], pass_k: int) -> List[Dict[str, object]]:
    grouped: Dict[Tuple[str, str], Dict[str, object]] = defaultdict(lambda: {
        "benchmarks": 0,
        "candidate_total": 0,
        "candidate_verified": 0,
        "file_success": 0,
        "repair_attempted": 0,
        "repair_verified": 0,
    })

    by_sample: Dict[Tuple[str, str, str], Dict[str, object]] = {}
    for row in initial_rows:
        key = (row["model_name"], row["language"], row["sample_id"])
        item = by_sample.setdefault(key, {
            "candidates": [],
            "any_success": False,
        })
        verified = as_bool(row.get("verify_success", ""))
        item["candidates"].append(verified)
        if verified:
            item["any_success"] = True

    for row in repair_rows:
        key = (row["model_name"], row.get("language", ""), row["sample_id"])
        item = by_sample.setdefault(key, {
            "candidates": [],
            "any_success": False,
        })
        if as_bool(row.get("verify_success", "")):
            item["any_success"] = True

    for row in initial_rows:
        key = (row["model_name"], row["language"], row["sample_id"])
        g = grouped[(row["model_name"], row["language"])]
        g["candidate_total"] = int(g["candidate_total"]) + 1
        if as_bool(row.get("verify_success", "")):
            g["candidate_verified"] = int(g["candidate_verified"]) + 1

        if key not in grouped:
            continue

    for (model, language, sample_id), item in by_sample.items():
        g = grouped[(model, language)]
        g["benchmarks"] = int(g["benchmarks"]) + 1
        if item["any_success"]:
            g["file_success"] = int(g["file_success"]) + 1

    for row in repair_rows:
        g = grouped[(row["model_name"], row.get("language", ""))]
        g["repair_attempted"] = int(g["repair_attempted"]) + 1
        if as_bool(row.get("verify_success", "")):
            g["repair_verified"] = int(g["repair_verified"]) + 1

    rows: List[Dict[str, object]] = []
    for (model, language), g in sorted(grouped.items()):
        benchmarks = int(g["benchmarks"])
        candidate_total = int(g["candidate_total"])
        repair_attempted = int(g["repair_attempted"])
        rows.append(
            {
                "model": model,
                "language": language,
                "benchmarks": benchmarks,
                "file_success": int(g["file_success"]),
                "file_success_rate": (g["file_success"] / benchmarks) if benchmarks else 0.0,
                "candidate_total": candidate_total,
                "candidate_verified": int(g["candidate_verified"]),
                "candidate_verify_rate": (g["candidate_verified"] / candidate_total) if candidate_total else 0.0,
                "repair_attempted": repair_attempted,
                "repair_verified": int(g["repair_verified"]),
                "repair_success_rate": (g["repair_verified"] / repair_attempted) if repair_attempted else 0.0,
            }
        )
    return rows


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


def main() -> None:
    parser = argparse.ArgumentParser(description="Summarize experiment results.")
    parser.add_argument("--initial-results", default="output/initial_results.csv")
    parser.add_argument("--repair-results", default="output/repair_results.csv")
    parser.add_argument("--out", default="output/exp_summary.csv")
    parser.add_argument("--pass-k", type=int, default=5)
    args = parser.parse_args()

    initial_rows = load_rows(Path(args.initial_results).resolve())
    repair_rows = load_rows(Path(args.repair_results).resolve())
    rows = summarize(initial_rows, repair_rows, args.pass_k)
    write_csv(Path(args.out).resolve(), rows)
    print(f"[done] summary={Path(args.out).resolve()}")


if __name__ == "__main__":
    main()
