#!/usr/bin/env python3
import argparse
import csv
import json
import random
import re
import subprocess
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from math import comb
from pathlib import Path

import requests

ROOT_DIR = Path(__file__).resolve().parent.parent
ENV_FILE = ROOT_DIR / ".env"


def load_env_file(env_file: Path):
    env = {}
    if not env_file.exists():
        return env

    for raw_line in env_file.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        clean_value = value.strip().strip('"').strip("'")
        if key in env and env[key] and clean_value == "":
            continue
        env[key] = clean_value
    return env


ENV = load_env_file(ENV_FILE)
API_URL = ENV.get("API_URL", "")
API_KEY = ENV.get("API_KEY", "")


def env_int(name: str, default: int) -> int:
    raw = ENV.get(name)
    if raw is None:
        return default
    try:
        return int(raw)
    except Exception:
        return default


def env_float(name: str, default: float) -> float:
    raw = ENV.get(name)
    if raw is None:
        return default
    try:
        return float(raw)
    except Exception:
        return default


def env_bool(name: str, default: bool) -> bool:
    raw = ENV.get(name)
    if raw is None:
        return default
    return str(raw).strip().lower() in {"1", "true", "yes", "on"}

PASS_K = env_int("PASS_K", 5)
TEMPERATURE = env_float("TEMPERATURE", 0.2)
SLEEP_BETWEEN_CALLS = env_float("SLEEP_BETWEEN_CALLS", 1.0)

MAX_RETRIES = env_int("MAX_RETRIES", 3)
BASE_BACKOFF = env_float("BASE_BACKOFF", 2.0)
MAX_BACKOFF = env_float("MAX_BACKOFF", 30.0)
JITTER = env_float("JITTER", 1.0)
MIN_API_INTERVAL = env_float("MIN_API_INTERVAL", 0.4)
CONNECT_TIMEOUT = env_float("CONNECT_TIMEOUT", 15.0)
REQUEST_TIMEOUT = env_float("REQUEST_TIMEOUT", 180.0)
DEFAULT_WORKERS = env_int("WORKERS", 4)
DEFAULT_TIMESTAMP_SUBDIR = env_bool("TIMESTAMP_SUBDIR", False)

DEFAULT_CONFIG = ROOT_DIR / "pipeline" / "configs" / "llm_spec_experiment.json"


def load_model_config(config_path: Path) -> dict:
    data = json.loads(config_path.read_text(encoding="utf-8"))
    models = data.get("models", {})
    if not models:
        raise RuntimeError(f"No models found in config: {config_path}")
    return models


def parse_selected_models(models_arg: str, config_path: Path):
    models = load_model_config(config_path)

    if not models_arg or not models_arg.strip():
        return {k: v for k, v in models.items()}

    keys = [k.strip() for k in models_arg.split(",") if k.strip()]
    if not keys:
        return {k: v for k, v in models.items()}

    unknown = [k for k in keys if k not in models]
    if unknown:
        raise RuntimeError(
            f"Unknown model key(s): {unknown}. Available: {list(models.keys())}"
        )

    return {k: models[k] for k in keys}


REQ_LOCK = threading.Lock()
LAST_API_TS = 0.0


def resolve_input_path(path_text: str) -> Path:
    """Resolve input path with repo-root fallback for Docker usage.

    If user runs from `pipeline/` and passes `benchmark`, this resolves to
    `<repo_root>/benchmark` instead of `<cwd>/benchmark` when possible.
    """
    p = Path(path_text)
    if p.is_absolute():
        return p.resolve()

    cwd_candidate = p.resolve()
    if cwd_candidate.exists():
        return cwd_candidate

    root_candidate = (ROOT_DIR / p).resolve()
    return root_candidate


def resolve_output_base(path_text: str) -> Path:
    p = Path(path_text)
    if p.is_absolute():
        return p.resolve()
    return (ROOT_DIR / p).resolve()


def validate_api_key() -> None:
    if not API_URL:
        raise RuntimeError("Missing API_URL in .env at repo root")
    if not API_KEY:
        raise RuntimeError("Missing API_KEY in .env at repo root")
    try:
        f"Bearer {API_KEY}".encode("latin-1")
    except UnicodeEncodeError as e:
        raise RuntimeError(
            "Invalid API_KEY characters for HTTP headers. "
            "Please clean smart quotes/invisible chars in .env"
        ) from e


def collect_benchmark_files(src_root: Path):
    files = [f for f in src_root.rglob("*") if f.is_file() and detect_language(f)]
    if not files:
        raise RuntimeError(
            "No benchmark files found. "
            f"Resolved benchmark_dir={src_root}. "
            "Expected files with suffix .c/.java/.rs"
        )
    return files


def resolve_and_validate_roots(benchmark_dir: str, prompt_dir: str):
    src_root = resolve_input_path(str(benchmark_dir))
    prompt_root = resolve_input_path(str(prompt_dir))

    if not src_root.exists() or not src_root.is_dir():
        raise RuntimeError(f"benchmark_dir not found or not a directory: {src_root}")
    if not prompt_root.exists() or not prompt_root.is_dir():
        raise RuntimeError(f"prompt_dir not found or not a directory: {prompt_root}")

    for lang in ("c", "java", "rust"):
        prompt_file = prompt_root / f"{lang}.txt"
        if not prompt_file.exists():
            raise RuntimeError(f"prompt missing: {prompt_file}")

    return src_root, prompt_root


def build_summary_rows(report_items):
    grouped = {}
    for item in report_items:
        model = item.get("model", "unknown")
        lang = item.get("language", "unknown")
        key = (model, lang)
        if key not in grouped:
            grouped[key] = {
                "model": model,
                "language": lang,
                "files": 0,
                "success_files": 0,
                "attempted_total": 0,
                "early_stop_files": 0,
                "pass1_total": 0.0,
                "pass5_total": 0.0,
            }

        g = grouped[key]
        g["files"] += 1
        g["success_files"] += int(item.get("c", 0) > 0)
        g["attempted_total"] += int(item.get("attempted", 0))
        g["early_stop_files"] += int(bool(item.get("stopped_early", False)))
        g["pass1_total"] += float(item.get("pass@1", 0.0))
        g["pass5_total"] += float(item.get("pass@5", 0.0))

    rows = []
    for _, g in sorted(grouped.items(), key=lambda kv: (kv[0][0], kv[0][1])):
        files = g["files"]
        rows.append(
            {
                "model": g["model"],
                "language": g["language"],
                "files": files,
                "success_files": g["success_files"],
                "pass_rate": (g["success_files"] / files) if files else 0.0,
                "avg_attempts": (g["attempted_total"] / files) if files else 0.0,
                "early_stop_files": g["early_stop_files"],
                "avg_pass@1": (g["pass1_total"] / files) if files else 0.0,
                "avg_pass@5": (g["pass5_total"] / files) if files else 0.0,
            }
        )

    return rows


def write_summary_outputs(report_file: Path, out_root: Path):
    report_items = json.loads(report_file.read_text(encoding="utf-8"))
    rows = build_summary_rows(report_items)

    summary_json = out_root / "passk_summary.json"
    summary_csv = out_root / "passk_summary.csv"
    summary_md = out_root / "passk_summary.md"
    summary_tex = out_root / "passk_summary.tex"

    summary_json.write_text(json.dumps(rows, indent=2), encoding="utf-8")

    with summary_csv.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "model",
                "language",
                "files",
                "success_files",
                "pass_rate",
                "avg_attempts",
                "early_stop_files",
                "avg_pass@1",
                "avg_pass@5",
            ]
        )
        for r in rows:
            writer.writerow(
                [
                    r["model"],
                    r["language"],
                    r["files"],
                    r["success_files"],
                    f"{r['pass_rate']:.4f}",
                    f"{r['avg_attempts']:.2f}",
                    r["early_stop_files"],
                    f"{r['avg_pass@1']:.4f}",
                    f"{r['avg_pass@5']:.4f}",
                ]
            )

    md_lines = [
        "# pass@k Summary by Model and Language",
        "",
        "| model | language | files | success_files | pass_rate | avg_attempts | early_stop_files | avg_pass@1 | avg_pass@5 |",
        "|---|---|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for r in rows:
        md_lines.append(
            f"| {r['model']} | {r['language']} | {r['files']} | {r['success_files']} | {r['pass_rate']:.4f} | {r['avg_attempts']:.2f} | {r['early_stop_files']} | {r['avg_pass@1']:.4f} | {r['avg_pass@5']:.4f} |"
        )
    summary_md.write_text("\n".join(md_lines) + "\n", encoding="utf-8")

    tex_lines = [
        "% Requires: \\usepackage{booktabs,graphicx}",
        "\\begin{table}[t]",
        "  \\centering",
        "  \\scriptsize",
        "  \\setlength{\\tabcolsep}{3.0pt}",
        "  \\renewcommand{\\arraystretch}{0.95}",
        "  \\caption{pass@k Summary by Model and Language}",
        "  \\resizebox{\\columnwidth}{!}{%",
        "  \\begin{tabular}{llrrrrrrr}",
        "    \\toprule",
        "    Model & Lang & Files & Success & PassRate & AvgAttempts & EarlyStop & AvgPass@1 & AvgPass@5 \\\\",
        "    \\midrule",
    ]
    prev_model = ""
    for r in rows:
        model_cell = r["model"] if r["model"] != prev_model else ""
        prev_model = r["model"]
        tex_lines.append(
            "    "
            + f"{model_cell} & {r['language']} & {r['files']} & {r['success_files']} & {r['pass_rate']:.4f} & {r['avg_attempts']:.2f} & {r['early_stop_files']} & {r['avg_pass@1']:.4f} & {r['avg_pass@5']:.4f} \\\\"
        )
    tex_lines.extend(
        [
            "    \\bottomrule",
            "  \\end{tabular}",
            "  }",
            "\\end{table}",
        ]
    )
    summary_tex.write_text("\n".join(tex_lines) + "\n", encoding="utf-8")

    print("summary json:", summary_json)
    print("summary csv:", summary_csv)
    print("summary md:", summary_md)
    print("summary tex:", summary_tex)


def detect_language(path: Path):
    if path.suffix == ".c":
        return "c"
    if path.suffix == ".java":
        return "java"
    if path.suffix == ".rs":
        return "rust"
    return None


def load_prompt(lang, prompt_root):
    prompt_file = prompt_root / f"{lang}.txt"
    if not prompt_file.exists():
        raise RuntimeError(f"prompt missing: {prompt_file}")
    return prompt_file.read_text(encoding="utf-8")


def clean_output(text):
    text = re.sub(r"```[a-zA-Z]*\n?", "", text)
    text = re.sub(r"```", "", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def call_llm(model, prompt):
    global LAST_API_TS

    retry = 0
    while True:
        try:
            auth_value = f"Bearer {API_KEY}"
            auth_value.encode("latin-1")

            with REQ_LOCK:
                now = time.time()
                wait = MIN_API_INTERVAL - (now - LAST_API_TS)
                if wait > 0:
                    time.sleep(wait)
                LAST_API_TS = time.time()

            resp = requests.post(
                API_URL,
                headers={"Authorization": auth_value},
                json={
                    "model": model,
                    "messages": [{"role": "user", "content": prompt}],
                    "temperature": TEMPERATURE,
                },
                timeout=(CONNECT_TIMEOUT, REQUEST_TIMEOUT),
            )
            resp.raise_for_status()
            data = resp.json()
            return data["choices"][0]["message"]["content"]

        except Exception as e:
            if retry >= MAX_RETRIES:
                raise
            retry += 1
            backoff = min(MAX_BACKOFF, BASE_BACKOFF * (2 ** retry)) + random.uniform(0, JITTER)
            print(f"retry {retry} sleep {backoff:.1f}s model={model} err={type(e).__name__}: {e}")
            time.sleep(backoff)


def clip_text(text: str, max_lines: int = 20, max_chars: int = 3000) -> str:
    if not text:
        return ""
    lines = text.splitlines()
    clipped = "\n".join(lines[:max_lines]).strip()
    if len(clipped) > max_chars:
        clipped = clipped[:max_chars].rstrip() + "\n...[truncated]"
    return clipped


def sanitize_verifier_message(text: str) -> str:
    if not text:
        return ""
    filtered = []
    for line in text.splitlines():
        l = line.strip()
        if ".long-type-" in l:
            continue
        if "consider using `--verbose`" in l:
            continue
        filtered.append(line)
    return "\n".join(filtered).strip()


def cleanup_long_type_files(path: Path) -> None:
    parent = path.parent
    stem = path.stem
    for p in parent.glob(f"{stem}.long-type-*.txt"):
        try:
            p.unlink()
        except Exception:
            pass


def run_verifast(path: Path, lang):
    try:
        if lang == "c":
            cmd = ["verifast", "-shared", str(path)]
        elif lang == "java":
            # Relax Java link-phase strictness by emitting vfmanifest.
            cmd = ["verifast", "-emit_vfmanifest", str(path)]
        elif lang == "rust":
            cmd = ["verifast", str(path)]
        else:
            return False, "Unsupported language for VeriFast"

        proc = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
        )
        if lang == "rust":
            cleanup_long_type_files(path)
        success = proc.returncode == 0
        if success:
            return True, ""

        raw_err = (proc.stderr or b"").decode("utf-8", errors="ignore").strip()
        raw_out = (proc.stdout or b"").decode("utf-8", errors="ignore").strip()
        msg = raw_err if raw_err else raw_out
        msg = sanitize_verifier_message(msg)
        return False, clip_text(msg)
    except Exception as e:
        return False, f"VeriFast execution error: {e}"


def pass_at_k(n, c, k):
    if c == 0:
        return 0.0
    if n - c < k:
        return 1.0
    return 1 - comb(n - c, k) / comb(n, k)


def process_one_file(model_key, model_name, src_file, src_root, prompt_root, out_root):
    rel = src_file.relative_to(src_root)
    lang = detect_language(src_file)
    if not lang:
        return None

    code = src_file.read_text(encoding="utf-8", errors="ignore")
    prompt_template = load_prompt(lang, prompt_root)

    success_count = 0
    samples = []
    last_failed_output = ""
    last_verifast_error = ""

    for k in range(1, PASS_K + 1):
        prompt = prompt_template.replace("{CODE}", code)
        if last_verifast_error:
            prompt += (
                "\n\nPrevious attempt failed VeriFast. "
                "Please revise the solution to fix these errors. "
                "Return only the full corrected code."
                "\n\n[Previous Generated Code]\n"
                + last_failed_output
                + "\n\n[VeriFast Error]\n"
                + last_verifast_error
            )

        try:
            raw = call_llm(model_name, prompt)
            cleaned = clean_output(raw)
        except Exception as e:
            samples.append({"sample": k, "success": False, "error": str(e)})
            continue

        out_file = out_root / model_key / f"sample_{k}" / lang / rel
        out_file.parent.mkdir(parents=True, exist_ok=True)
        out_file.write_text(cleaned, encoding="utf-8")

        success, vf_error = run_verifast(out_file, lang)
        sample_item = {
            "sample": k,
            "success": success,
            "output_file": str(out_file.relative_to(out_root)),
        }
        if vf_error:
            sample_item["error"] = vf_error
        samples.append(sample_item)

        if success:
            success_count = 1
            break

        last_failed_output = cleaned
        last_verifast_error = vf_error or "Verification failed without detailed stderr."

        time.sleep(SLEEP_BETWEEN_CALLS)

    return {
        "model": model_key,
        "file": str(rel),
        "language": lang,
        "n": PASS_K,
        "attempted": len(samples),
        "c": success_count,
        "stopped_early": success_count > 0,
        "pass@1": pass_at_k(PASS_K, success_count, 1),
        "pass@5": pass_at_k(PASS_K, success_count, 5),
        "samples": samples,
    }


def run_all(src_root, out_root, prompt_root, workers, selected_models):
    validate_api_key()

    src_root, prompt_root = resolve_and_validate_roots(src_root, prompt_root)
    out_root = Path(out_root).resolve()

    out_root.mkdir(parents=True, exist_ok=True)

    files = collect_benchmark_files(src_root)

    print("benchmark size:", len(files))
    print(
        "run config:",
        {
            "workers": workers,
            "pass_k": PASS_K,
            "sleep_between_calls": SLEEP_BETWEEN_CALLS,
            "min_api_interval": MIN_API_INTERVAL,
            "max_retries": MAX_RETRIES,
            "base_backoff": BASE_BACKOFF,
            "max_backoff": MAX_BACKOFF,
            "jitter": JITTER,
        },
    )
    all_model_results = {}

    for model_key, model_name in selected_models.items():
        print("\n==============================")
        print("MODEL:", model_key)
        print("==============================")

        model_results = []

        with ThreadPoolExecutor(max_workers=max(1, workers)) as executor:
            future_to_src = {
                executor.submit(
                    process_one_file,
                    model_key,
                    model_name,
                    src_file,
                    src_root,
                    prompt_root,
                    out_root,
                ): src_file
                for src_file in files
            }

            for future in as_completed(future_to_src):
                src_file = future_to_src[future]
                try:
                    item = future.result()
                except Exception as e:
                    rel = str(src_file.relative_to(src_root))
                    lang = detect_language(src_file)
                    item = {
                        "model": model_key,
                        "file": rel,
                        "language": lang,
                        "n": PASS_K,
                        "attempted": 0,
                        "c": 0,
                        "stopped_early": False,
                        "pass@1": 0.0,
                        "pass@5": 0.0,
                        "samples": [{"sample": 0, "success": False, "error": f"future_error: {e}"}],
                    }
                if item is None:
                    continue
                model_results.append(item)
                status = "PASS" if item["c"] > 0 else "FAIL"
                print(
                    f"[{model_key}] {item['file']} -> {status} "
                    f"(attempted {item['attempted']}/{PASS_K})"
                )

        all_model_results[model_key] = model_results
        model_report_file = out_root / model_key / "passk_report.json"
        model_report_file.parent.mkdir(parents=True, exist_ok=True)
        model_report_file.write_text(json.dumps(model_results, indent=2), encoding="utf-8")
        print(f"[{model_key}] report saved: {model_report_file}")
        write_summary_outputs(model_report_file, model_report_file.parent)

    combined_results = []
    for model_results in all_model_results.values():
        combined_results.extend(model_results)

    combined_report_file = out_root / "passk_report.json"
    combined_report_file.write_text(json.dumps(combined_results, indent=2), encoding="utf-8")
    print("\nCombined report saved:", combined_report_file)
    write_summary_outputs(combined_report_file, out_root)

    summary = {}
    for r in combined_results:
        m = r["model"]
        summary.setdefault(m, {"p1": [], "p5": []})
        summary[m]["p1"].append(r["pass@1"])
        summary[m]["p5"].append(r["pass@5"])

    print("\n===== SUMMARY =====")
    for m in summary:
        p1 = sum(summary[m]["p1"]) / len(summary[m]["p1"]) if summary[m]["p1"] else 0
        p5 = sum(summary[m]["p5"]) / len(summary[m]["p5"]) if summary[m]["p5"] else 0
        print(m)
        print(" pass@1 =", round(p1, 3))
        print(" pass@5 =", round(p5, 3))


def preflight_checks(benchmark_dir: str, prompt_dir: str):
    src_root, prompt_root = resolve_and_validate_roots(benchmark_dir, prompt_dir)
    files = collect_benchmark_files(src_root)
    validate_api_key()

    print("preflight ok")
    print(" benchmark_dir:", src_root)
    print(" prompt_dir:", prompt_root)
    print(" benchmark size:", len(files))


def main():
    global SLEEP_BETWEEN_CALLS, MIN_API_INTERVAL
    global MAX_RETRIES, BASE_BACKOFF, MAX_BACKOFF, JITTER
    global CONNECT_TIMEOUT, REQUEST_TIMEOUT

    parser = argparse.ArgumentParser(
        description="Run pass@5 with early stop and multithreading"
    )
    parser.add_argument("benchmark_dir", nargs="?", help="input benchmark directory")
    parser.add_argument("output_dir", nargs="?", help="output directory prefix (timestamp appended)")
    parser.add_argument("prompt_dir", nargs="?", help="prompt directory")
    parser.add_argument("--workers", type=int, default=DEFAULT_WORKERS, help="worker threads per model")
    parser.add_argument("--min-api-interval", type=float, default=MIN_API_INTERVAL, help="minimum interval between API calls (seconds)")
    parser.add_argument("--sleep-between-calls", type=float, default=SLEEP_BETWEEN_CALLS, help="sleep between attempts of same file (seconds)")
    parser.add_argument("--max-retries", type=int, default=MAX_RETRIES, help="max retries for one API call")
    parser.add_argument("--base-backoff", type=float, default=BASE_BACKOFF, help="base exponential backoff seconds")
    parser.add_argument("--max-backoff", type=float, default=MAX_BACKOFF, help="max backoff seconds")
    parser.add_argument("--jitter", type=float, default=JITTER, help="random jitter added to backoff")
    parser.add_argument("--connect-timeout", type=float, default=CONNECT_TIMEOUT, help="HTTP connect timeout seconds")
    parser.add_argument("--request-timeout", type=float, default=REQUEST_TIMEOUT, help="HTTP read timeout seconds")
    parser.add_argument(
        "--report-json",
        type=str,
        default=None,
        help="only build tables from an existing passk_report.json",
    )
    parser.add_argument(
        "--timestamp-subdir",
        action="store_true",
        default=DEFAULT_TIMESTAMP_SUBDIR,
        help="store outputs under output_dir/output_YYYYmmdd_HHMMSS",
    )
    parser.add_argument(
        "--check-only",
        action="store_true",
        help="run preflight checks only, do not call models",
    )
    parser.add_argument(
        "--config",
        type=str,
        default=str(DEFAULT_CONFIG),
        help="Path to experiment config JSON with model definitions",
    )
    parser.add_argument(
        "--models",
        type=str,
        default="",
        help="Comma-separated model keys from config (default: all models in config)",
    )
    args = parser.parse_args()

    SLEEP_BETWEEN_CALLS = max(0.0, args.sleep_between_calls)
    MIN_API_INTERVAL = max(0.0, args.min_api_interval)
    MAX_RETRIES = max(0, args.max_retries)
    BASE_BACKOFF = max(0.0, args.base_backoff)
    MAX_BACKOFF = max(0.0, args.max_backoff)
    JITTER = max(0.0, args.jitter)
    CONNECT_TIMEOUT = max(1.0, args.connect_timeout)
    REQUEST_TIMEOUT = max(1.0, args.request_timeout)

    if args.report_json:
        report_file = Path(args.report_json).resolve()
        if not report_file.exists():
            raise RuntimeError(f"report json not found: {report_file}")
        write_summary_outputs(report_file, report_file.parent)
        return

    if not args.benchmark_dir or not args.output_dir or not args.prompt_dir:
        raise RuntimeError(
            "benchmark_dir/output_dir/prompt_dir are required unless --report-json is provided"
        )

    if args.check_only:
        preflight_checks(args.benchmark_dir, args.prompt_dir)
        return

    config_path = Path(args.config).resolve()
    selected_models = parse_selected_models(args.models, config_path)
    print("selected models:", list(selected_models.keys()))

    out_base = resolve_output_base(args.output_dir)
    if args.timestamp_subdir:
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        out_root = out_base / f"output_{ts}"
    else:
        out_root = out_base

    print("output dir:", out_root)

    run_all(args.benchmark_dir, out_root, args.prompt_dir, args.workers, selected_models)


if __name__ == "__main__":
    main()
