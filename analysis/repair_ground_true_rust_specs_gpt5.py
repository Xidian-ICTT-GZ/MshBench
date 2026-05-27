#!/usr/bin/env python3

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
import re
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import requests


def load_dotenv(dotenv_path: Path) -> Dict[str, str]:
    values: Dict[str, str] = {}
    if not dotenv_path.exists():
        return values

    for raw in dotenv_path.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue

        k, v = line.split("=", 1)
        key = k.strip()
        val = v.strip()

        if len(val) >= 2 and ((val[0] == '"' and val[-1] == '"') or (val[0] == "'" and val[-1] == "'")):
            val = val[1:-1]

        values[key] = val

    return values


def merged_env(dotenv_values: Dict[str, str]) -> Dict[str, str]:
    env = dict(dotenv_values)
    env.update(os.environ)
    return env


def clean_llm_output(text: str) -> str:
    text = re.sub(r"```[a-zA-Z0-9_+-]*\n?", "", text)
    text = text.replace("```", "")
    return text.strip() + "\n"


def strip_spec_only_projection(code: str) -> str:
    """
    Build a projection that removes VeriFast spec-only parts.
    Used to guarantee non-spec Rust code is unchanged.

    Removed segments:
    - block specs: /*@ ... @*/
    - line specs: //@ ... (keeps code before //@)
    """
    out: List[str] = []
    in_block = False

    for line in code.splitlines(keepends=True):
        i = 0
        keep = ""

        while i < len(line):
            if in_block:
                end = line.find("@*/", i)
                if end == -1:
                    i = len(line)
                    break
                in_block = False
                i = end + 3
                continue

            start_block = line.find("/*@", i)
            start_line = line.find("//@", i)

            if start_line != -1 and (start_block == -1 or start_line < start_block):
                keep += line[i:start_line]
                i = len(line)
                break

            if start_block != -1:
                keep += line[i:start_block]
                i = start_block + 3
                in_block = True
                continue

            keep += line[i:]
            break

        out.append(keep)

    return "".join(out)


def non_spec_unchanged(before: str, after: str) -> bool:
    return strip_spec_only_projection(before) == strip_spec_only_projection(after)


def cleanup_long_type_files(rs_file: Path) -> None:
    for p in rs_file.parent.glob(f"{rs_file.stem}.long-type-*.txt"):
        try:
            p.unlink()
        except Exception:
            pass


def run_verifast(rs_file: Path, allow_assume: bool, timeout_sec: int) -> Tuple[bool, str, List[str]]:
    cmd = ["verifast"]
    if allow_assume:
        cmd.append("-allow_assume")
    cmd.append(str(rs_file))

    try:
        proc = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_sec,
            cwd=str(rs_file.parent),
        )
    except Exception as e:
        return False, f"VeriFast execution error: {e}", cmd

    cleanup_long_type_files(rs_file)

    if proc.returncode == 0:
        return True, "", cmd

    out = (proc.stdout or b"").decode("utf-8", errors="ignore").strip()
    err = (proc.stderr or b"").decode("utf-8", errors="ignore").strip()
    msg = err if err else out

    # Trim noisy output to reduce prompt size.
    lines = [ln for ln in msg.splitlines() if ".long-type-" not in ln]
    msg = "\n".join(lines[:80]).strip()

    return False, msg, cmd


@dataclass
class ApiConfig:
    url: str
    key: str
    model: str


def read_api_config(env: Dict[str, str]) -> ApiConfig:
    url = env.get("OPENAI_API_URL") or env.get("API_URL") or "https://api.openai.com/v1/chat/completions"
    key = env.get("OPENAI_API_KEY") or env.get("API_KEY")
    model = env.get("GPT5_MODEL") or env.get("OPENAI_MODEL") or env.get("MODEL") or "gpt-5.5"

    if not key:
        raise RuntimeError("Missing API key in .env / environment. Expected OPENAI_API_KEY or API_KEY.")

    return ApiConfig(url=url, key=key, model=model)


def call_gpt5(api: ApiConfig, prompt: str, timeout_sec: int) -> str:
    resp = requests.post(
        api.url,
        headers={
            "Authorization": f"Bearer {api.key}",
            "Content-Type": "application/json",
        },
        json={
            "model": api.model,
            "messages": [{"role": "user", "content": prompt}],
            "temperature": 0.1,
        },
        timeout=timeout_sec,
    )
    resp.raise_for_status()

    data = resp.json()
    return data["choices"][0]["message"]["content"]


def build_prompt(file_path: Path, current_code: str, vf_error: str) -> str:
    return f"""You are fixing a Rust file for VeriFast.

File: {file_path}

Hard constraints (must follow):
1) Modify ONLY VeriFast specification parts:
   - lines/comments starting with //@
   - block specs delimited by /*@ ... @*/
2) Do NOT change Rust executable code, imports, function signatures, control flow, or literals.
3) Return the full file content only. No markdown fences.

Current file content:
{current_code}

VeriFast error output:
{vf_error}

Task:
- Repair the VeriFast specifications so verification can proceed.
- Keep all non-spec code byte-for-byte unchanged.
"""


def iter_rust_files(src_root: Path) -> List[Path]:
    return sorted(p for p in src_root.rglob("*.rs") if p.is_file())


def process_one_file(
    rs_file: Path,
    src_root: Path,
    out_root: Path,
    api: ApiConfig,
    rounds: int,
    allow_assume: bool,
    vf_timeout: int,
    llm_timeout: int,
    in_place: bool,
    sleep_sec: float,
) -> Dict[str, object]:
    rel = rs_file.relative_to(src_root)
    original = rs_file.read_text(encoding="utf-8", errors="ignore")
    current = original

    if in_place:
        working_file = rs_file
    else:
        working_file = out_root / rel
        working_file.parent.mkdir(parents=True, exist_ok=True)
        working_file.write_text(current, encoding="utf-8")

    history: List[Dict[str, object]] = []

    ok, err, cmd = run_verifast(working_file, allow_assume=allow_assume, timeout_sec=vf_timeout)
    history.append(
        {
            "round": 0,
            "status": "pass" if ok else "fail",
            "verifast_command": " ".join(cmd),
            "error": err,
        }
    )

    if ok:
        return {
            "file": str(rel),
            "verified": True,
            "used_rounds": 0,
            "output_file": str(working_file),
            "history": history,
        }

    for r in range(1, rounds + 1):
        prompt = build_prompt(rel, current, err)

        try:
            raw = call_gpt5(api, prompt, timeout_sec=llm_timeout)
            candidate = clean_llm_output(raw)
        except Exception as e:
            history.append(
                {
                    "round": r,
                    "status": "llm_error",
                    "error": f"LLM call failed: {e}",
                }
            )
            break

        if not non_spec_unchanged(current, candidate):
            history.append(
                {
                    "round": r,
                    "status": "rejected_non_spec_change",
                    "error": "Model changed non-spec Rust code; candidate rejected.",
                }
            )
            err = "Previous candidate changed non-spec Rust code. Fix only //@ and /*@ ... @*/ parts."
            time.sleep(sleep_sec)
            continue

        current = candidate
        working_file.write_text(current, encoding="utf-8")

        ok, err, cmd = run_verifast(working_file, allow_assume=allow_assume, timeout_sec=vf_timeout)
        history.append(
            {
                "round": r,
                "status": "pass" if ok else "fail",
                "verifast_command": " ".join(cmd),
                "error": err,
            }
        )

        if ok:
            return {
                "file": str(rel),
                "verified": True,
                "used_rounds": r,
                "output_file": str(working_file),
                "history": history,
            }

        time.sleep(sleep_sec)

    return {
        "file": str(rel),
        "verified": False,
        "used_rounds": rounds,
        "output_file": str(working_file),
        "history": history,
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run VeriFast on all ground_true/rust files and repair specs with GPT-5.5 (spec-only changes)."
    )
    parser.add_argument("--project-root", default=str(Path(__file__).resolve().parents[1]))
    parser.add_argument("--src", default="ground_true/rust")
    parser.add_argument("--out", default="output_repair/gpt5_5_spec_repair")
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--vf-timeout", type=int, default=90)
    parser.add_argument("--llm-timeout", type=int, default=180)
    parser.add_argument("--sleep", type=float, default=0.6)
    parser.add_argument("--allow-assume", action="store_true", default=True)
    parser.add_argument("--no-allow-assume", action="store_false", dest="allow_assume")
    parser.add_argument("--in-place", action="store_true")
    parser.add_argument("--max-files", type=int, default=0)
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()

    project_root = Path(args.project_root).resolve()
    src_root = (project_root / args.src).resolve()
    out_root = (project_root / args.out).resolve()

    if not src_root.exists():
        raise RuntimeError(f"Rust source folder not found: {src_root}")

    dotenv_path = project_root / ".env"
    env = merged_env(load_dotenv(dotenv_path))
    api = read_api_config(env)

    files = iter_rust_files(src_root)
    if args.max_files > 0:
        files = files[: args.max_files]

    if not files:
        raise RuntimeError(f"No .rs files found under {src_root}")

    if args.workers < 1:
        raise RuntimeError("--workers must be >= 1")

    run_root = out_root / time.strftime("run_%Y%m%d_%H%M%S")
    if not args.in_place:
        run_root.mkdir(parents=True, exist_ok=True)

    results: List[Dict[str, object]] = []

    print(f"[info] project_root={project_root}")
    print(f"[info] source={src_root}")
    print(f"[info] files={len(files)}")
    print(f"[info] model={api.model}")
    print(f"[info] allow_assume={args.allow_assume}")
    print(f"[info] in_place={args.in_place}")
    print(f"[info] workers={args.workers}")

    target_root = src_root if args.in_place else run_root

    if args.workers == 1:
        for idx, rs_file in enumerate(files, start=1):
            print(f"[file {idx}/{len(files)}] {rs_file.relative_to(src_root)}")
            result = process_one_file(
                rs_file=rs_file,
                src_root=src_root,
                out_root=target_root,
                api=api,
                rounds=args.rounds,
                allow_assume=args.allow_assume,
                vf_timeout=args.vf_timeout,
                llm_timeout=args.llm_timeout,
                in_place=args.in_place,
                sleep_sec=args.sleep,
            )
            results.append(result)
    else:
        with ThreadPoolExecutor(max_workers=args.workers) as executor:
            future_to_file = {
                executor.submit(
                    process_one_file,
                    rs_file=rs_file,
                    src_root=src_root,
                    out_root=target_root,
                    api=api,
                    rounds=args.rounds,
                    allow_assume=args.allow_assume,
                    vf_timeout=args.vf_timeout,
                    llm_timeout=args.llm_timeout,
                    in_place=args.in_place,
                    sleep_sec=args.sleep,
                ): rs_file
                for rs_file in files
            }

            done = 0
            total = len(files)
            for future in as_completed(future_to_file):
                rs_file = future_to_file[future]
                done += 1
                try:
                    result = future.result()
                    results.append(result)
                    status = "pass" if result.get("verified") else "fail"
                    print(f"[done {done}/{total}] {rs_file.relative_to(src_root)} -> {status}")
                except Exception as e:
                    print(f"[done {done}/{total}] {rs_file.relative_to(src_root)} -> worker_error: {e}")
                    results.append(
                        {
                            "file": str(rs_file.relative_to(src_root)),
                            "verified": False,
                            "used_rounds": 0,
                            "output_file": "",
                            "history": [
                                {
                                    "round": 0,
                                    "status": "worker_error",
                                    "error": str(e),
                                }
                            ],
                        }
                    )

    verified = sum(1 for r in results if r.get("verified"))
    failed = len(results) - verified

    report = {
        "time": time.strftime("%Y-%m-%d %H:%M:%S"),
        "project_root": str(project_root),
        "source_root": str(src_root),
        "output_root": str(src_root if args.in_place else run_root),
        "model": api.model,
        "rounds": args.rounds,
        "allow_assume": args.allow_assume,
        "in_place": args.in_place,
        "total": len(results),
        "verified": verified,
        "failed": failed,
        "results": results,
    }

    report_dir = out_root if args.in_place else run_root
    report_dir.mkdir(parents=True, exist_ok=True)
    report_path = report_dir / "rust_spec_repair_report.json"
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")

    print(f"[done] verified={verified}/{len(results)} failed={failed}")
    print(f"[done] report={report_path}")


if __name__ == "__main__":
    main()
