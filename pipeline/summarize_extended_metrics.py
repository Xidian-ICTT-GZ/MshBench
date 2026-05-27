from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Tuple


def load_rows(path: Path) -> List[Dict[str, str]]:
    if not path.exists():
        return []
    with path.open("r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        return [dict(row) for row in reader]


def as_bool(value: str) -> bool:
    return str(value).lower() == "true"


def as_int(value: str) -> int:
    try:
        return int(float(value))
    except (TypeError, ValueError):
        return 0


def as_float(value: str) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return 0.0


def write_csv(path: Path, rows: List[Dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    headers = list(rows[0].keys())
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=headers)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def build_sample_info(initial_rows: List[Dict[str, str]]) -> Dict[Tuple[str, str], Dict[str, str]]:
    info: Dict[Tuple[str, str], Dict[str, str]] = {}
    for row in initial_rows:
        model = row.get("model_name", "")
        sample_id = row.get("sample_id", "")
        key = (model, sample_id)
        if key in info:
            continue
        info[key] = {
            "language": row.get("language", ""),
            "structure": row.get("structure", ""),
        }
    return info


def build_sample_success(initial_rows: List[Dict[str, str]], repair_rows: List[Dict[str, str]]) -> Dict[Tuple[str, str], bool]:
    success: Dict[Tuple[str, str], bool] = defaultdict(bool)
    for row in initial_rows:
        key = (row.get("model_name", ""), row.get("sample_id", ""))
        if as_bool(row.get("verify_success", "")):
            success[key] = True
    for row in repair_rows:
        key = (row.get("model_name", ""), row.get("sample_id", ""))
        if as_bool(row.get("verify_success", "")):
            success[key] = True
    return success


def summarize_overall_and_language(
    initial_rows: List[Dict[str, str]],
    repair_rows: List[Dict[str, str]],
) -> Tuple[List[Dict[str, object]], List[Dict[str, object]], List[Dict[str, object]]]:
    sample_info = build_sample_info(initial_rows)
    sample_success = build_sample_success(initial_rows, repair_rows)

    by_model: Dict[str, Dict[str, object]] = defaultdict(lambda: {
        "samples": set(),
        "file_success": 0,
        "candidate_total": 0,
        "candidate_verified": 0,
        "repair_attempted": 0,
        "repair_verified": 0,
    })
    by_language: Dict[Tuple[str, str], Dict[str, object]] = defaultdict(lambda: {
        "samples": set(),
        "file_success": 0,
        "candidate_total": 0,
        "candidate_verified": 0,
        "repair_attempted": 0,
        "repair_verified": 0,
    })
    by_structure: Dict[Tuple[str, str, str], Dict[str, object]] = defaultdict(lambda: {
        "samples": set(),
        "file_success": 0,
        "candidate_total": 0,
        "candidate_verified": 0,
    })

    for row in initial_rows:
        model = row.get("model_name", "")
        sample_id = row.get("sample_id", "")
        language = row.get("language", "")
        structure = row.get("structure", "")

        by_model[model]["candidate_total"] = int(by_model[model]["candidate_total"]) + 1
        by_language[(model, language)]["candidate_total"] = int(by_language[(model, language)]["candidate_total"]) + 1
        by_structure[(model, language, structure)]["candidate_total"] = int(by_structure[(model, language, structure)]["candidate_total"]) + 1

        if as_bool(row.get("verify_success", "")):
            by_model[model]["candidate_verified"] = int(by_model[model]["candidate_verified"]) + 1
            by_language[(model, language)]["candidate_verified"] = int(by_language[(model, language)]["candidate_verified"]) + 1
            by_structure[(model, language, structure)]["candidate_verified"] = int(by_structure[(model, language, structure)]["candidate_verified"]) + 1

    for row in repair_rows:
        model = row.get("model_name", "")
        language = row.get("language", "")
        by_model[model]["repair_attempted"] = int(by_model[model]["repair_attempted"]) + 1
        by_language[(model, language)]["repair_attempted"] = int(by_language[(model, language)]["repair_attempted"]) + 1
        if as_bool(row.get("verify_success", "")):
            by_model[model]["repair_verified"] = int(by_model[model]["repair_verified"]) + 1
            by_language[(model, language)]["repair_verified"] = int(by_language[(model, language)]["repair_verified"]) + 1

    for (model, sample_id), info in sample_info.items():
        language = info.get("language", "")
        structure = info.get("structure", "")
        by_model[model]["samples"].add(sample_id)
        by_language[(model, language)]["samples"].add(sample_id)
        by_structure[(model, language, structure)]["samples"].add(sample_id)
        if sample_success.get((model, sample_id), False):
            by_model[model]["file_success"] = int(by_model[model]["file_success"]) + 1
            by_language[(model, language)]["file_success"] = int(by_language[(model, language)]["file_success"]) + 1
            by_structure[(model, language, structure)]["file_success"] = int(by_structure[(model, language, structure)]["file_success"]) + 1

    overall_rows: List[Dict[str, object]] = []
    for model, g in sorted(by_model.items()):
        benchmarks = len(g["samples"])
        candidate_total = int(g["candidate_total"])
        repair_attempted = int(g["repair_attempted"])
        overall_rows.append(
            {
                "model": model,
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

    language_rows: List[Dict[str, object]] = []
    for (model, language), g in sorted(by_language.items()):
        benchmarks = len(g["samples"])
        candidate_total = int(g["candidate_total"])
        repair_attempted = int(g["repair_attempted"])
        language_rows.append(
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

    structure_rows: List[Dict[str, object]] = []
    for (model, language, structure), g in sorted(by_structure.items()):
        benchmarks = len(g["samples"])
        candidate_total = int(g["candidate_total"])
        structure_rows.append(
            {
                "model": model,
                "language": language,
                "structure": structure,
                "benchmarks": benchmarks,
                "file_success": int(g["file_success"]),
                "file_success_rate": (g["file_success"] / benchmarks) if benchmarks else 0.0,
                "candidate_total": candidate_total,
                "candidate_verified": int(g["candidate_verified"]),
                "candidate_verify_rate": (g["candidate_verified"] / candidate_total) if candidate_total else 0.0,
            }
        )

    return overall_rows, language_rows, structure_rows


def summarize_failure_distribution(rows: List[Dict[str, str]], source: str) -> List[Dict[str, object]]:
    counts: Dict[Tuple[str, str, str, str, str], int] = defaultdict(int)
    totals: Dict[Tuple[str, str, str], int] = defaultdict(int)

    for row in rows:
        model = row.get("model_name", "")
        language = row.get("language", "")
        stage = row.get("failure_stage", "")
        category = row.get("failure_category", "")
        key = (source, model, language, stage, category)
        counts[key] += 1
        totals[(source, model, language)] += 1

    output: List[Dict[str, object]] = []
    for (source, model, language, stage, category), count in sorted(counts.items()):
        total = totals[(source, model, language)]
        output.append(
            {
                "source": source,
                "model": model,
                "language": language,
                "failure_stage": stage,
                "failure_category": category,
                "count": count,
                "percent": (count / total) if total else 0.0,
            }
        )
    return output


def summarize_repair_rounds(repair_rows: List[Dict[str, str]]) -> List[Dict[str, object]]:
    grouped: Dict[Tuple[str, str, int], Dict[str, int]] = defaultdict(lambda: {
        "attempts": 0,
        "successes": 0,
    })

    for row in repair_rows:
        model = row.get("model_name", "")
        language = row.get("language", "")
        round_id = as_int(row.get("repair_round", "0"))
        g = grouped[(model, language, round_id)]
        g["attempts"] += 1
        if as_bool(row.get("verify_success", "")):
            g["successes"] += 1

    rows: List[Dict[str, object]] = []
    for (model, language, round_id), g in sorted(grouped.items()):
        attempts = g["attempts"]
        rows.append(
            {
                "model": model,
                "language": language,
                "repair_round": round_id,
                "attempts": attempts,
                "successes": g["successes"],
                "success_rate": (g["successes"] / attempts) if attempts else 0.0,
            }
        )
    return rows


def summarize_repair_cost(repair_rows: List[Dict[str, str]]) -> List[Dict[str, object]]:
    grouped: Dict[Tuple[str, str], Dict[str, float]] = defaultdict(lambda: {
        "repair_calls": 0.0,
        "tokens_in": 0.0,
        "tokens_out": 0.0,
        "latency_sec": 0.0,
    })

    for row in repair_rows:
        model = row.get("model_name", "")
        language = row.get("language", "")
        g = grouped[(model, language)]
        g["repair_calls"] += 1
        g["tokens_in"] += as_float(row.get("tokens_in", "0"))
        g["tokens_out"] += as_float(row.get("tokens_out", "0"))
        g["latency_sec"] += as_float(row.get("latency_sec", "0"))

    rows: List[Dict[str, object]] = []
    for (model, language), g in sorted(grouped.items()):
        calls = g["repair_calls"]
        rows.append(
            {
                "model": model,
                "language": language,
                "repair_calls": int(calls),
                "tokens_in_total": round(g["tokens_in"], 4),
                "tokens_out_total": round(g["tokens_out"], 4),
                "latency_sec_total": round(g["latency_sec"], 4),
                "tokens_in_avg": round((g["tokens_in"] / calls) if calls else 0.0, 4),
                "tokens_out_avg": round((g["tokens_out"] / calls) if calls else 0.0, 4),
                "latency_sec_avg": round((g["latency_sec"] / calls) if calls else 0.0, 4),
            }
        )

    return rows


def summarize_residual_errors(
    initial_rows: List[Dict[str, str]],
    repair_rows: List[Dict[str, str]],
) -> List[Dict[str, object]]:
    sample_info = build_sample_info(initial_rows)
    sample_success = build_sample_success(initial_rows, repair_rows)

    by_sample: Dict[Tuple[str, str], List[Dict[str, object]]] = defaultdict(list)
    for row in initial_rows:
        by_sample[(row.get("model_name", ""), row.get("sample_id", ""))].append(
            {
                "is_repair": False,
                "attempt_id": as_int(row.get("attempt_id", "0")),
                "repair_round": 0,
                "stage": row.get("failure_stage", ""),
                "category": row.get("failure_category", ""),
                "language": row.get("language", ""),
            }
        )

    for row in repair_rows:
        by_sample[(row.get("model_name", ""), row.get("sample_id", ""))].append(
            {
                "is_repair": True,
                "attempt_id": as_int(row.get("attempt_id", "0")),
                "repair_round": as_int(row.get("repair_round", "0")),
                "stage": row.get("failure_stage", ""),
                "category": row.get("failure_category", ""),
                "language": row.get("language", ""),
            }
        )

    residual_counts: Dict[Tuple[str, str, str, str], int] = defaultdict(int)
    totals: Dict[Tuple[str, str], int] = defaultdict(int)

    for (model, sample_id), entries in by_sample.items():
        if sample_success.get((model, sample_id), False):
            continue
        info = sample_info.get((model, sample_id), {})
        language = info.get("language", "")
        if not entries:
            continue
        entries.sort(key=lambda e: (e["is_repair"], e["repair_round"], e["attempt_id"]))
        last = entries[-1]
        stage = last.get("stage", "")
        category = last.get("category", "")
        residual_counts[(model, language, stage, category)] += 1
        totals[(model, language)] += 1

    rows: List[Dict[str, object]] = []
    for (model, language, stage, category), count in sorted(residual_counts.items()):
        total = totals[(model, language)]
        rows.append(
            {
                "model": model,
                "language": language,
                "failure_stage": stage,
                "failure_category": category,
                "count": count,
                "percent": (count / total) if total else 0.0,
            }
        )
    return rows


def generate_all_metrics(initial_path: Path, repair_path: Path, out_dir: Path) -> None:
    initial_rows = load_rows(initial_path)
    repair_rows = load_rows(repair_path)

    overall_rows, language_rows, structure_rows = summarize_overall_and_language(initial_rows, repair_rows)
    failure_rows = summarize_failure_distribution(initial_rows, "initial") + summarize_failure_distribution(repair_rows, "repair")
    repair_round_rows = summarize_repair_rounds(repair_rows)
    residual_rows = summarize_residual_errors(initial_rows, repair_rows)
    repair_cost_rows = summarize_repair_cost(repair_rows)

    write_csv(out_dir / "exp_overall_metrics.csv", overall_rows)
    write_csv(out_dir / "exp_language_metrics.csv", language_rows)
    write_csv(out_dir / "exp_structure_metrics.csv", structure_rows)
    write_csv(out_dir / "exp_failure_distribution.csv", failure_rows)
    write_csv(out_dir / "exp_repair_rounds.csv", repair_round_rows)
    write_csv(out_dir / "exp_residual_errors.csv", residual_rows)
    write_csv(out_dir / "exp_repair_costs.csv", repair_cost_rows)


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate extended experiment metrics.")
    parser.add_argument("--initial-results", default="output/initial_results.csv")
    parser.add_argument("--repair-results", default="output/repair_results.csv")
    parser.add_argument("--out-dir", default="output")
    args = parser.parse_args()

    generate_all_metrics(Path(args.initial_results).resolve(), Path(args.repair_results).resolve(), Path(args.out_dir).resolve())
    print(f"[done] extended_metrics={Path(args.out_dir).resolve()}")


if __name__ == "__main__":
    main()
