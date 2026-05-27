from __future__ import annotations

import argparse
import csv
import json
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
    decoding_settings_text,
    parse_verifast_output,
    prompt_variant,
    recompose_candidate_with_source,
    run_verifast,
    save_json,
    save_text,
    sha256_text,
)
from .llm_spec_config import ExperimentConfig, load_config
from .llm_spec_prompts import build_prompt


def load_metadata(path: Path) -> List[Dict[str, str]]:
    with path.open("r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        return [dict(row) for row in reader]


def load_sample_input(data_dir: Path, sample_id: str, suffix: str) -> str:
    input_path = data_dir / sample_id / f"input_no_spec{suffix}"
    return input_path.read_text(encoding="utf-8", errors="ignore")


def write_row(writer: csv.DictWriter, row: Dict[str, object]) -> None:
    writer.writerow({k: row.get(k, "") for k in writer.fieldnames})


def run_generation(
    metadata_path: Path,
    data_dir: Path,
    out_dir: Path,
    config_path: Path,
    model_name: str,
    pass_k: int,
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

    rows = load_metadata(metadata_path)
    results_path = out_dir / "initial_results.csv"
    results_path.parent.mkdir(parents=True, exist_ok=True)

    sample_cache: Dict[str, tuple[str, str]] = {}
    for row in rows:
        sample_id = row["sample_id"]
        if sample_id in sample_cache:
            continue
        suffix = Path(row["file_path"]).suffix
        sample_cache[sample_id] = (suffix, load_sample_input(data_dir, sample_id, suffix))

    headers = [
        "model_name",
        "sample_id",
        "language",
        "structure",
        "attempt_id",
        "prompt_path",
        "raw_output_path",
        "inserted_program_path",
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
        "decoding_settings",
    ]

    def process_attempt(row: Dict[str, str], attempt_id: int) -> Dict[str, object]:
        sample_id = row["sample_id"]
        language = row["language"]
        structure = row["structure"]
        file_path = Path(row["file_path"])
        suffix, source_no_spec = sample_cache[sample_id]

        settings_text = decoding_settings_text(model, attempt_id)
        base_prompt = build_prompt(
            language=language,
            benchmark_id=str(file_path),
            source_code=source_no_spec,
            candidate_index=attempt_id,
            pass_k=pass_k,
            decoding_settings=settings_text,
        )
        prompt = prompt_variant(model, base_prompt, attempt_id)
        prompt_hash = sha256_text(base_prompt)

        attempt_dir = out_dir / "generation" / model.name / sample_id / f"attempt_{attempt_id:02d}"
        attempt_dir.mkdir(parents=True, exist_ok=True)

        prompt_path = attempt_dir / "prompt.txt"
        raw_path = attempt_dir / "raw_output.txt"
        inserted_path = attempt_dir / f"inserted_program{suffix}"
        stdout_path = attempt_dir / "verifast_stdout.txt"
        stderr_path = attempt_dir / "verifast_stderr.txt"

        save_text(prompt_path, prompt)

        start = time.time()
        raw_output = ""
        usage: Dict[str, int] = {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0}
        cleaned = ""
        inserted = ""
        last_issue = ""

        # Try a few times when output is empty or low-quality (esp. Java trivial specs)
        max_retries = 3
        for retry in range(1, max_retries + 1):
            prompt_retry = prompt
            if last_issue:
                prompt_retry = prompt + build_recovery_suffix(source_no_spec, last_issue)

            raw_output, usage = call_llm(api_url, api_key, model, prompt_retry, attempt_id + retry - 1, llm_timeout)
            cleaned = clean_llm_output(raw_output)
            inserted = recompose_candidate_with_source(source_no_spec, cleaned)
            last_issue = candidate_quality_issue(source_no_spec, inserted, language) or ""
            if not last_issue:
                break

        latency = time.time() - start
        save_text(raw_path, raw_output)
        save_text(inserted_path, inserted)

        vf = run_verifast(inserted_path, language, config.verifast_args, vf_timeout)
        save_text(stdout_path, vf["stdout"])
        save_text(stderr_path, vf["stderr"])

        parsed = parse_verifast_output(vf["output"])
        failure = classify_failure(vf["output"], vf["verified"], parsed["parse_ok"], parsed["type_ok"])

        return {
            "model_name": model.model_name,
            "sample_id": sample_id,
            "language": language,
            "structure": structure,
            "attempt_id": attempt_id,
            "prompt_path": prompt_path.as_posix(),
            "raw_output_path": raw_path.as_posix(),
            "inserted_program_path": inserted_path.as_posix(),
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
            "decoding_settings": settings_text,
        }

    results: List[Dict[str, object]] = []
    total_tasks = len(rows) * pass_k
    completed = 0
    # Track samples that already had a successful verification to avoid duplicate prints
    succeeded_samples: set[str] = set()
    if workers <= 1:
        for row in rows:
            for attempt_id in range(1, pass_k + 1):
                item = process_attempt(row, attempt_id)
                results.append(item)
                # Print success when a sample is first verified
                try:
                    if item.get("verify_success") is True and item.get("sample_id") not in succeeded_samples:
                        print(f"[success][generation] {item.get('sample_id')} verified by attempt {item.get('attempt_id')}", flush=True)
                        succeeded_samples.add(item.get("sample_id"))
                except Exception:
                    pass
                completed += 1
                if progress_every > 0 and (completed % progress_every == 0 or completed == total_tasks):
                    print(f"[progress][generation] {completed}/{total_tasks}", flush=True)
    else:
        with ThreadPoolExecutor(max_workers=workers) as executor:
            futures = []
            for row in rows:
                for attempt_id in range(1, pass_k + 1):
                    futures.append(executor.submit(process_attempt, row, attempt_id))
            for fut in as_completed(futures):
                item = fut.result()
                results.append(item)
                # Print success when a sample is first verified (thread-safe enough for our use)
                try:
                    if item.get("verify_success") is True and item.get("sample_id") not in succeeded_samples:
                        print(f"[success][generation] {item.get('sample_id')} verified by attempt {item.get('attempt_id')}", flush=True)
                        succeeded_samples.add(item.get("sample_id"))
                except Exception:
                    pass
                completed += 1
                if progress_every > 0 and (completed % progress_every == 0 or completed == total_tasks):
                    print(f"[progress][generation] {completed}/{total_tasks}", flush=True)

    results.sort(key=lambda r: (str(r.get("sample_id", "")), int(r.get("attempt_id", 0))))

    with results_path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=headers)
        writer.writeheader()
        for item in results:
            write_row(writer, item)

    print(f"[done] initial_results={results_path}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Run initial generation stage.")
    parser.add_argument("--metadata", default="data/benchmark_metadata.csv")
    parser.add_argument("--data-dir", default="data/benchmark")
    parser.add_argument("--out-dir", default="output")
    parser.add_argument("--config", default=str(Path(__file__).with_name("configs") / "llm_spec_experiment.json"))
    parser.add_argument("--pass-k", type=int, default=5)
    parser.add_argument("--model", type=str, default="", help="Model name from config (required if config has multiple models)")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--progress-every", type=int, default=25)
    parser.add_argument("--llm-timeout", type=int, default=180)
    parser.add_argument("--vf-timeout", type=int, default=90)
    args = parser.parse_args()

    model_name = args.model or _auto_select_model(Path(args.config).resolve())

    run_generation(
        Path(args.metadata).resolve(),
        Path(args.data_dir).resolve(),
        Path(args.out_dir).resolve(),
        Path(args.config).resolve(),
        model_name,
        args.pass_k,
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
