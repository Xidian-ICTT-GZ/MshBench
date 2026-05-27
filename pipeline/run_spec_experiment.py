from __future__ import annotations

import argparse
import csv
from pathlib import Path

import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))
    from pipeline.build_benchmark_metadata import main as build_metadata_main  # type: ignore
    from pipeline.build_spec_free_dataset import build_dataset  # type: ignore
    from pipeline.experiment_utils import now_timestamp  # type: ignore
    from pipeline.run_generation_stage import run_generation  # type: ignore
    from pipeline.run_repair_stage import run_repair  # type: ignore
    from pipeline.summarize_experiment_results import summarize, write_csv  # type: ignore
    from pipeline.summarize_extended_metrics import generate_all_metrics  # type: ignore
else:
    from .build_benchmark_metadata import main as build_metadata_main
    from .build_spec_free_dataset import build_dataset
    from .experiment_utils import now_timestamp
    from .run_generation_stage import run_generation
    from .run_repair_stage import run_repair
    from .summarize_experiment_results import summarize, write_csv
    from .summarize_extended_metrics import generate_all_metrics


def ensure_metadata(metadata_path: Path, benchmark_root: Path) -> None:
    if metadata_path.exists():
        return
    args = ["--root", str(benchmark_root), "--out", str(metadata_path)]
    # Run metadata builder via subprocess-like arg injection
    import sys

    old_argv = sys.argv
    try:
        sys.argv = ["build_benchmark_metadata.py", *args]
        build_metadata_main()
    finally:
        sys.argv = old_argv


def filter_metadata_by_languages(metadata_path: Path, languages: set[str], out_path: Path) -> Path:
    if not languages:
        return metadata_path

    with metadata_path.open("r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        rows = [dict(row) for row in reader if str(row.get("language", "")).lower() in languages]
        headers = list(reader.fieldnames or [])

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=headers)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)

    return out_path


def main() -> None:
    parser = argparse.ArgumentParser(description="Run full spec experiment pipeline with timestamped outputs.")
    parser.add_argument("--benchmark-root", default="benchmark")
    parser.add_argument("--metadata", default="data/benchmark_metadata.csv")
    parser.add_argument("--data-dir", default="data/benchmark")
    parser.add_argument("--config", default=str(Path(__file__).with_name("configs") / "llm_spec_experiment.json"))
    parser.add_argument("--pass-k", type=int, default=5)
    parser.add_argument("--max-rounds", type=int, default=3)
    parser.add_argument("--model", type=str, default="", help="Model name from config (required if config has multiple models)")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--progress-every", type=int, default=25)
    parser.add_argument("--llm-timeout", type=int, default=180)
    parser.add_argument("--vf-timeout", type=int, default=90)
    parser.add_argument("--run-prefix", default="output")
    parser.add_argument("--out-root", default=".")
    parser.add_argument("--run-dir", default=None, help="Exact output directory name (overrides --run-prefix timestamping)")
    parser.add_argument("--languages", default="all", help="Comma-separated languages, e.g. c,java,rust or all")
    args = parser.parse_args()

    benchmark_root = Path(args.benchmark_root).resolve()
    metadata_path = Path(args.metadata).resolve()
    data_dir = Path(args.data_dir).resolve()
    out_root = Path(args.out_root).resolve()

    ensure_metadata(metadata_path, benchmark_root)

    run_id = now_timestamp(args.run_prefix)
    run_root = out_root / run_id
    if args.run_dir:
        run_root = out_root / args.run_dir
    run_root.mkdir(parents=True, exist_ok=True)

    selected_langs: set[str] = set()
    if str(args.languages).strip().lower() != "all":
        selected_langs = {x.strip().lower() for x in str(args.languages).split(",") if x.strip()}
        allowed = {"c", "java", "rust"}
        unknown = selected_langs - allowed
        if unknown:
            raise ValueError(f"Unknown languages: {sorted(unknown)}")

    filtered_metadata = filter_metadata_by_languages(
        metadata_path,
        selected_langs,
        run_root / "metadata.filtered.csv",
    )
    build_dataset(filtered_metadata, benchmark_root, data_dir)

    # Call run_generation with backward/forward-compatible args
    import inspect

    gen_sig = inspect.signature(run_generation)
    gen_params = list(gen_sig.parameters.keys())
    model_name = args.model
    if not model_name:
        from .llm_spec_config import load_config as _load_config
        _cfg = _load_config(Path(args.config).resolve())
        _keys = list(_cfg.models.keys())
        if len(_keys) == 1:
            model_name = _keys[0]
        else:
            raise RuntimeError(f"Multiple models in config ({_keys}). Please specify --model.")

    gen_args = [
        filtered_metadata,
        data_dir,
        run_root,
        Path(args.config).resolve(),
        model_name,
        args.pass_k,
        args.llm_timeout,
        args.vf_timeout,
        args.workers,
    ]
    if "progress_every" in gen_params:
        gen_args.append(args.progress_every)

    run_generation(*gen_args)

    # Call run_repair with backward/forward-compatible args
    rep_sig = inspect.signature(run_repair)
    rep_params = list(rep_sig.parameters.keys())
    rep_args = [
        run_root / "initial_results.csv",
        data_dir,
        run_root,
        Path(args.config).resolve(),
        model_name,
        args.max_rounds,
        args.llm_timeout,
        args.vf_timeout,
        args.workers,
    ]
    if "progress_every" in rep_params:
        rep_args.append(args.progress_every)

    run_repair(*rep_args)

    summary_rows = summarize(
        load_rows(run_root / "initial_results.csv"),
        load_rows(run_root / "repair_results.csv"),
        args.pass_k,
    )
    write_csv(run_root / "exp_summary.csv", summary_rows)
    generate_all_metrics(run_root / "initial_results.csv", run_root / "repair_results.csv", run_root)
    print(f"[done] run_root={run_root}")


def load_rows(path: Path):
    if not path.exists():
        return []
    import csv

    with path.open("r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        return [dict(row) for row in reader]


if __name__ == "__main__":
    main()
