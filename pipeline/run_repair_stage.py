from __future__ import annotations

import argparse
import csv
import os
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List

from .error_taxonomy import classify_failure
from .experiment_utils import (
    api_settings,
    build_recovery_suffix,
    candidate_quality_issue,
    call_llm,
    clean_llm_output,
    parse_verifast_output,
    prompt_variant,
    recompose_candidate_with_source,
    run_verifast,
    save_text,
    sha256_text,
)
from .llm_spec_config import load_config


def load_rows(path: Path) -> List[Dict[str, str]]:
    with path.open("r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        return [dict(row) for row in reader]


def extract_spec(text: str) -> str:
    lines: List[str] = []
    in_block = False
    for line in text.splitlines(keepends=True):
        stripped = line.lstrip()
        if in_block:
            lines.append(line)
            if "@*/" in line:
                in_block = False
            continue
        if stripped.startswith("//@"):
            lines.append(line)
            continue
        if "/*@" in line:
            lines.append(line)
            if "@*/" not in line:
                in_block = True
            continue
    return "".join(lines).strip() + ("\n" if lines else "")


def build_repair_prompt(no_spec_program: str, current_spec: str, error_msg: str) -> str:
    return (
        "You are repairing VeriFast specifications only.\n"
        "Return the full program with updated annotations.\n\n"
        "[Program without specifications]\n"
        f"{no_spec_program}\n\n"
        "[Current specifications]\n"
        f"{current_spec}\n\n"
        "[VeriFast error message]\n"
        f"{error_msg}\n\n"
        "Revise only the specifications; keep all runtime code byte-for-byte unchanged."
    )


def write_row(writer: csv.DictWriter, row: Dict[str, object]) -> None:
    writer.writerow({k: row.get(k, "") for k in writer.fieldnames})


def run_repair(
    initial_results_path: Path,
    data_dir: Path,
    out_dir: Path,
    config_path: Path,
    model_name: str,
    max_rounds: int,
    llm_timeout: int,
    vf_timeout: int,
    workers: int,
    progress_every: int,
) -> None:
    config = load_config(config_path)
    if not config.models:
        raise RuntimeError("No models configured.")
    if model_name not in config.models:
        raise RuntimeError(f"Unknown model '{model_name}'. Available: {list(config.models.keys())}")
    model = config.models[model_name]

    env = dict(os.environ)
    api_url, api_key = api_settings(model, env)

    initial_rows = load_rows(initial_results_path)
    repair_path = out_dir / "repair_results.csv"
    repair_path.parent.mkdir(parents=True, exist_ok=True)

    headers = [
        "model_name",
        "sample_id",
        "language",
        "attempt_id",
        "repair_round",
        "repair_prompt_path",
        "repair_raw_output_path",
        "repaired_program_path",
        "parse_success",
        "type_success",
        "verify_success",
        "failure_stage",
        "failure_category",
        "stdout_path",
        "stderr_path",
        "tokens_in",
        "tokens_out",
        "latency_sec",
        "prompt_hash",
    ]

    def process_row(row: Dict[str, str]) -> List[Dict[str, object]]:
        if row.get("verify_success", "").lower() == "true":
            return []

        sample_id = row["sample_id"]
        attempt_id = int(row["attempt_id"])
        inserted_program_path = Path(row["inserted_program_path"]).resolve()
        language = row["language"]
        suffix = inserted_program_path.suffix

        no_spec_path = data_dir / sample_id / f"input_no_spec{suffix}"
        no_spec_program = no_spec_path.read_text(encoding="utf-8", errors="ignore")
        current_program = inserted_program_path.read_text(encoding="utf-8", errors="ignore")
        current_spec = extract_spec(current_program)
        last_error = ""
        last_program = current_program

        results: List[Dict[str, object]] = []
        for round_id in range(1, max_rounds + 1):
            prompt = build_repair_prompt(no_spec_program, current_spec, last_error)
            prompt = prompt_variant(model, prompt, attempt_id + round_id)
            prompt_hash = sha256_text(prompt)

            round_dir = out_dir / "repair" / model.name / sample_id / f"attempt_{attempt_id:02d}" / f"round_{round_id:02d}"
            round_dir.mkdir(parents=True, exist_ok=True)

            prompt_path = round_dir / "repair_prompt.txt"
            raw_path = round_dir / "repair_raw_output.txt"
            repaired_path = round_dir / f"repaired_program{suffix}"
            stdout_path = round_dir / "verifast_stdout.txt"
            stderr_path = round_dir / "verifast_stderr.txt"

            save_text(prompt_path, prompt)
            start = time.time()
            raw_output = ""
            usage: Dict[str, int] = {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0}
            cleaned = ""
            repaired = ""
            last_issue = ""

            # Retry on empty or low-quality repair candidates
            max_retries = 2
            for retry in range(1, max_retries + 1):
                prompt_retry = prompt
                if last_issue:
                    prompt_retry = prompt + build_recovery_suffix(no_spec_program, last_issue)

                raw_output, usage = call_llm(api_url, api_key, model, prompt_retry, attempt_id + round_id + retry - 1, llm_timeout)
                cleaned = clean_llm_output(raw_output)
                repaired = recompose_candidate_with_source(no_spec_program, cleaned)
                last_issue = candidate_quality_issue(no_spec_program, repaired, language) or ""
                if not last_issue:
                    break

            latency = time.time() - start
            save_text(raw_path, raw_output)
            save_text(repaired_path, repaired)

            vf = run_verifast(repaired_path, language, config.verifast_args, vf_timeout)
            save_text(stdout_path, vf["stdout"])
            save_text(stderr_path, vf["stderr"])

            parsed = parse_verifast_output(vf["output"])
            failure = classify_failure(vf["output"], vf["verified"], parsed["parse_ok"], parsed["type_ok"])

            results.append(
                {
                    "model_name": model.model_name,
                    "sample_id": sample_id,
                    "language": language,
                    "attempt_id": attempt_id,
                    "repair_round": round_id,
                    "repair_prompt_path": prompt_path.as_posix(),
                    "repair_raw_output_path": raw_path.as_posix(),
                    "repaired_program_path": repaired_path.as_posix(),
                    "parse_success": parsed["parse_ok"],
                    "type_success": parsed["type_ok"],
                    "verify_success": vf["verified"],
                    "failure_stage": failure.stage,
                    "failure_category": failure.category,
                    "stdout_path": stdout_path.as_posix(),
                    "stderr_path": stderr_path.as_posix(),
                    "tokens_in": usage.get("prompt_tokens", 0),
                    "tokens_out": usage.get("completion_tokens", 0),
                    "latency_sec": round(latency, 4),
                    "prompt_hash": prompt_hash,
                }
            )

            if vf["verified"]:
                break

            last_error = vf["output"]
            last_program = repaired
            current_spec = extract_spec(last_program)

        return results

    results: List[Dict[str, object]] = []
    total_tasks = sum(1 for row in initial_rows if row.get("verify_success", "").lower() != "true")
    completed = 0
    # Track repaired samples already reported as successful
    succeeded_repairs: set[str] = set()
    if workers <= 1:
        for row in initial_rows:
            added = process_row(row)
            results.extend(added)
            # Report first successful repair per sample
            for item in added:
                try:
                    if item.get("verify_success") is True and item.get("sample_id") not in succeeded_repairs:
                        print(f"[success][repair] {item.get('sample_id')} repaired on attempt {item.get('attempt_id')} round {item.get('repair_round')}", flush=True)
                        succeeded_repairs.add(item.get("sample_id"))
                except Exception:
                    pass
            completed += 1
            if progress_every > 0 and (completed % progress_every == 0 or completed == total_tasks):
                print(f"[progress][repair] {completed}/{total_tasks}", flush=True)
    else:
        with ThreadPoolExecutor(max_workers=workers) as executor:
            futures = [executor.submit(process_row, row) for row in initial_rows]
            for fut in as_completed(futures):
                added = fut.result()
                results.extend(added)
                for item in added:
                    try:
                        if item.get("verify_success") is True and item.get("sample_id") not in succeeded_repairs:
                            print(f"[success][repair] {item.get('sample_id')} repaired on attempt {item.get('attempt_id')} round {item.get('repair_round')}", flush=True)
                            succeeded_repairs.add(item.get("sample_id"))
                    except Exception:
                        pass
                completed += 1
                if progress_every > 0 and (completed % progress_every == 0 or completed == total_tasks):
                    print(f"[progress][repair] {completed}/{total_tasks}", flush=True)

    with repair_path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=headers)
        writer.writeheader()
        for item in results:
            write_row(writer, item)

    print(f"[done] repair_results={repair_path}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Run verifier-guided repair stage.")
    parser.add_argument("--initial-results", default="output/initial_results.csv")
    parser.add_argument("--data-dir", default="data/benchmark")
    parser.add_argument("--out-dir", default="output")
    parser.add_argument("--config", default=str(Path(__file__).with_name("configs") / "llm_spec_experiment.json"))
    parser.add_argument("--max-rounds", type=int, default=3)
    parser.add_argument("--model", type=str, default="", help="Model name from config (required if config has multiple models)")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--progress-every", type=int, default=10)
    parser.add_argument("--llm-timeout", type=int, default=180)
    parser.add_argument("--vf-timeout", type=int, default=90)
    args = parser.parse_args()

    model_name = args.model or _auto_select_model(Path(args.config).resolve())

    run_repair(
        Path(args.initial_results).resolve(),
        Path(args.data_dir).resolve(),
        Path(args.out_dir).resolve(),
        Path(args.config).resolve(),
        model_name,
        args.max_rounds,
        args.llm_timeout,
        args.vf_timeout,
        args.workers,
        args.progress_every,
    )


def _auto_select_model(config_path: Path) -> str:
    """Auto-select the first (or only) model when --model is not specified."""
    config = load_config(config_path)
    if not config.models:
        raise RuntimeError("No models configured in config file.")
    keys = list(config.models.keys())
    if len(keys) == 1:
        return keys[0]
    raise RuntimeError(f"Multiple models found in config ({keys}). Please specify --model.")


if __name__ == "__main__":
    main()
