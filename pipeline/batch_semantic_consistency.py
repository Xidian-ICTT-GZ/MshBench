#!/usr/bin/env python3

from __future__ import annotations

import argparse
import csv
import json
import random
import re
import time
from dataclasses import dataclass
from difflib import SequenceMatcher
from pathlib import Path
from typing import Any, Dict, List, Tuple

import requests

import strip_annotations


ROOT_DIR = Path(__file__).resolve().parent.parent
ENV_FILE = ROOT_DIR / ".env"


def load_env_file(env_file: Path) -> Dict[str, str]:
    env: Dict[str, str] = {}
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
API_URL = ENV.get("API_URL", "https://api.linyinet.asia/v1/chat/completions")
API_KEY = ENV.get("API_KEY", "")
STRONG_MODEL = ENV.get("STRONG_MODEL", "claude-opus-4-5-20251101")
LLM_MAX_RETRIES = int(ENV.get("LLM_MAX_RETRIES", "3")) if ENV.get("LLM_MAX_RETRIES") else 3
LLM_BASE_BACKOFF = float(ENV.get("LLM_BASE_BACKOFF", "2.0")) if ENV.get("LLM_BASE_BACKOFF") else 2.0
LLM_MAX_BACKOFF = float(ENV.get("LLM_MAX_BACKOFF", "20.0")) if ENV.get("LLM_MAX_BACKOFF") else 20.0
LLM_JITTER = float(ENV.get("LLM_JITTER", "1.0")) if ENV.get("LLM_JITTER") else 1.0


RISK_PATTERNS = {
    "unsafe": re.compile(r"\bunsafe\b"),
    "raw_ptr": re.compile(r"\*mut\s+|\*const\s+|as\s+\*mut|as\s+\*const"),
    "threading": re.compile(r"\bthread::spawn\b|\bjoin\("),
    "sync": re.compile(r"\bMutex\b|\bRwLock\b|\bAtomic[A-Za-z0-9_]*\b"),
    "panic_like": re.compile(r"\bpanic!\b|\bunwrap\("),
    "ffi": re.compile(r"\bextern\s+\"C\"\b"),
}

FN_SIG = re.compile(r"\bfn\s+([A-Za-z0-9_]+)\s*\((.*?)\)\s*(?:->\s*([^\{]+))?\{", re.S)
STRUCT_SIG = re.compile(r"\bstruct\s+([A-Za-z0-9_]+)\s*\{", re.S)

RULES_TEXT = """Semantic Consistency Rules (ground_truth is gold):
1) Hard fail (inconsistent): function/struct signature changed, control-flow condition changed, side-effect semantics changed, concurrency semantics changed.
2) Allowed changes: comments/spec annotations/formatting/renaming without behavior impact.
3) Review-required risk: unsafe/raw pointers/threading/synchronization/panic/FFI present or changed.
Output JSON fields:
- verdict: consistent | inconsistent | review_required
- confidence: 0..1
- hard_fail_hits: string[]
- risk_hits: string[]
- semantic_diffs: string[]
- final_reason: string
"""

LLM_RULES_TEXT = """You are a strict semantic consistency judge for Rust code.

Goal:
Compare candidate against ground_truth (ground_truth is canonical) and decide whether candidate is highly semantically consistent and has no fundamental error.

Hard fundamental errors (any one => fundamental_error):
1) Function set changed, or function signature changed.
2) Struct field set changed for core data structures.
3) Control-flow boundary/condition changes that can alter behavior.
4) Side-effect semantics changed (writes, ownership/lifetime/resource handling).
5) Concurrency semantics changed (spawn/join ordering, lock scope, shared mutable access).

Allowed differences:
1) Comments/spec annotations/formatting.
2) Variable renaming without behavioral impact.

Output strictly JSON only with this schema:
{
    "verdict": "highly_consistent" | "needs_review" | "fundamental_error",
    "confidence": 0.0,
    "score": 0,
    "hard_fail_hits": [],
    "risk_hits": [],
    "semantic_diffs": [],
    "final_reason": "..."
}
"""


@dataclass
class TriageRecord:
    file: str
    verdict: str
    confidence: float
    exact_equal: bool
    stripped_equal: bool
    similarity: float
    hard_fail_hits: List[str]
    risk_hits: List[str]
    notes: str
    stage2_class: str = ""
    stage2_reason: str = ""
    llm_verdict: str = ""
    llm_confidence: float = 0.0
    llm_score: int = 0
    llm_hard_fail_hits: List[str] = None
    llm_risk_hits: List[str] = None
    llm_semantic_diffs: List[str] = None
    llm_final_reason: str = ""
    llm_error: str = ""
    final_verdict: str = ""

    def __post_init__(self) -> None:
        if self.llm_hard_fail_hits is None:
            self.llm_hard_fail_hits = []
        if self.llm_risk_hits is None:
            self.llm_risk_hits = []
        if self.llm_semantic_diffs is None:
            self.llm_semantic_diffs = []


def normalize_code(text: str) -> str:
    stripped = strip_annotations.strip_comments(text)
    stripped = re.sub(r"\s+", " ", stripped).strip()
    return stripped


def extract_fn_sigs(code: str) -> Dict[str, Tuple[str, str]]:
    sigs: Dict[str, Tuple[str, str]] = {}
    for m in FN_SIG.finditer(code):
        name = m.group(1)
        args = re.sub(r"\s+", " ", (m.group(2) or "")).strip()
        ret = re.sub(r"\s+", " ", (m.group(3) or "")).strip()
        sigs[name] = (args, ret)
    return sigs


def extract_structs(code: str) -> List[str]:
    return sorted({m.group(1) for m in STRUCT_SIG.finditer(code)})


def risk_hits(code_a: str, code_b: str) -> List[str]:
    hits = []
    merged = code_a + "\n" + code_b
    for name, pat in RISK_PATTERNS.items():
        if pat.search(merged):
            hits.append(name)
    return hits


def triage_one(rel: str, gt_code: str, cand_code: str) -> TriageRecord:
    exact_equal = gt_code == cand_code
    if exact_equal:
        return TriageRecord(rel, "consistent", 1.0, True, True, 1.0, [], [], "byte-identical")

    gt_norm = normalize_code(gt_code)
    cand_norm = normalize_code(cand_code)
    stripped_equal = gt_norm == cand_norm
    sim = SequenceMatcher(None, gt_norm, cand_norm).ratio()

    # User rule: similarity > 0.80 is directly considered successful.
    if sim > 0.80:
        return TriageRecord(
            rel,
            "consistent",
            0.80,
            False,
            stripped_equal,
            sim,
            [],
            risk_hits(gt_norm, cand_norm),
            "similarity threshold rule (>0.80)",
        )

    hard_fails: List[str] = []

    gt_fns = extract_fn_sigs(gt_norm)
    cand_fns = extract_fn_sigs(cand_norm)
    if set(gt_fns) != set(cand_fns):
        hard_fails.append("function_set_changed")
    else:
        for fn_name in gt_fns:
            if gt_fns[fn_name] != cand_fns[fn_name]:
                hard_fails.append("function_signature_changed")
                break

    if extract_structs(gt_norm) != extract_structs(cand_norm):
        hard_fails.append("struct_set_changed")

    risks = risk_hits(gt_norm, cand_norm)

    if stripped_equal and not risks:
        return TriageRecord(rel, "consistent", 0.95, False, True, sim, hard_fails, risks, "only comments/spec formatting differ")

    if hard_fails:
        return TriageRecord(rel, "inconsistent", 0.9, False, stripped_equal, sim, hard_fails, risks, "hard-fail rule triggered")

    if risks or sim < 0.98:
        return TriageRecord(rel, "review_required", 0.65, False, stripped_equal, sim, hard_fails, risks, "non-trivial semantic delta")

    return TriageRecord(rel, "review_required", 0.55, False, stripped_equal, sim, hard_fails, risks, "needs confirmation")


def stage2_review(record: TriageRecord) -> Tuple[str, str]:
    if record.verdict == "inconsistent" or record.hard_fail_hits:
        return "confirmed_inconsistent", "hard-fail rule triggered"

    risk_set = set(record.risk_hits)
    only_baseline_risks = risk_set.issubset({"unsafe", "raw_ptr", "panic_like"})
    has_concurrency_or_ffi = bool(risk_set.intersection({"threading", "sync", "ffi"}))

    if record.stripped_equal and record.similarity >= 0.9999 and only_baseline_risks:
        return "likely_consistent_need_spotcheck", "stripped code identical; only baseline rust risks"

    if record.stripped_equal and record.similarity >= 0.999 and not has_concurrency_or_ffi:
        return "likely_consistent_need_spotcheck", "near-identical stripped code without concurrency/ffi risk"

    if has_concurrency_or_ffi or record.similarity < 0.98 or not record.stripped_equal:
        return "high_risk_manual_review", "non-trivial delta or concurrency/sync/ffi risk"

    return "high_risk_manual_review", "needs manual confirmation"


def llm_task(record: TriageRecord, gt_code: str, cand_code: str) -> Dict[str, str]:
    prompt = (
        RULES_TEXT
        + "\nGround truth file: " + record.file
        + "\nCandidate file: " + record.file
        + "\n\n[Ground Truth]\n```rust\n"
        + gt_code
        + "\n```\n\n[Candidate]\n```rust\n"
        + cand_code
        + "\n```\n"
    )
    return {
        "file": record.file,
        "heuristic_verdict": record.verdict,
        "heuristic_confidence": f"{record.confidence:.2f}",
        "prompt": prompt,
    }


def should_run_llm(record: TriageRecord, llm_mode: str) -> bool:
    if llm_mode == "none":
        return False
    if llm_mode == "all":
        return True
    return record.verdict != "consistent" or record.stage2_class != "likely_consistent_need_spotcheck"


def extract_json_object(text: str) -> Dict[str, Any]:
    raw = text.strip()
    if raw.startswith("```"):
        raw = re.sub(r"^```[a-zA-Z]*\n?", "", raw)
        raw = re.sub(r"```$", "", raw).strip()

    try:
        obj = json.loads(raw)
        if isinstance(obj, dict):
            return obj
    except Exception:
        pass

    m = re.search(r"\{[\s\S]*\}", raw)
    if not m:
        raise ValueError("No JSON object found in LLM response")
    obj = json.loads(m.group(0))
    if not isinstance(obj, dict):
        raise ValueError("LLM JSON output is not an object")
    return obj


def call_strong_llm(prompt: str, model: str, api_url: str, api_key: str, timeout: float, max_retries: int) -> str:
    if not api_key:
        raise RuntimeError("Missing API_KEY in .env")

    auth_value = f"Bearer {api_key}"
    auth_value.encode("latin-1")

    retry = 0
    while True:
        try:
            resp = requests.post(
                api_url,
                headers={"Authorization": auth_value},
                json={
                    "model": model,
                    "messages": [
                        {"role": "system", "content": "You are a strict semantic equivalence judge."},
                        {"role": "user", "content": prompt},
                    ],
                    "temperature": 0,
                },
                timeout=timeout,
            )
            resp.raise_for_status()
            data = resp.json()
            return data["choices"][0]["message"]["content"]
        except Exception:
            if retry >= max_retries:
                raise
            retry += 1
            backoff = min(LLM_MAX_BACKOFF, LLM_BASE_BACKOFF * (2 ** retry)) + random.uniform(0, LLM_JITTER)
            time.sleep(backoff)


def build_llm_prompt(file_path: str, gt_code: str, cand_code: str) -> str:
    return (
        LLM_RULES_TEXT
        + "\nFile: "
        + file_path
        + "\n\n[Ground Truth]\n```rust\n"
        + gt_code
        + "\n```\n\n[Candidate]\n```rust\n"
        + cand_code
        + "\n```\n"
    )


def apply_llm_judgment(record: TriageRecord, gt_code: str, cand_code: str, model: str, api_url: str, api_key: str, timeout: float, max_retries: int) -> None:
    prompt = build_llm_prompt(record.file, gt_code, cand_code)
    raw = call_strong_llm(prompt, model=model, api_url=api_url, api_key=api_key, timeout=timeout, max_retries=max_retries)
    obj = extract_json_object(raw)

    verdict = str(obj.get("verdict", "needs_review"))
    if verdict not in {"highly_consistent", "needs_review", "fundamental_error"}:
        verdict = "needs_review"

    try:
        confidence = float(obj.get("confidence", 0.0))
    except Exception:
        confidence = 0.0
    confidence = max(0.0, min(1.0, confidence))

    try:
        score = int(obj.get("score", 0))
    except Exception:
        score = 0

    record.llm_verdict = verdict
    record.llm_confidence = confidence
    record.llm_score = score
    record.llm_hard_fail_hits = list(obj.get("hard_fail_hits", []) or [])
    record.llm_risk_hits = list(obj.get("risk_hits", []) or [])
    record.llm_semantic_diffs = list(obj.get("semantic_diffs", []) or [])
    record.llm_final_reason = str(obj.get("final_reason", ""))


def main() -> None:
    repo_root = Path(__file__).resolve().parent.parent

    parser = argparse.ArgumentParser(description="Batch semantic triage for Rust outputs")
    parser.add_argument("--ground-truth", default=str(repo_root / "ground_true" / "rust"), help="ground truth rust folder")
    parser.add_argument("--candidate", required=True, help="candidate rust folder")
    parser.add_argument("--out-dir", default=str(repo_root / "output" / "semantic_triage"), help="output folder")
    parser.add_argument("--llm-threshold", type=float, default=0.8, help="emit LLM task when confidence < threshold")
    parser.add_argument("--llm-mode", choices=["all", "review", "none"], default="review", help="files to send to strong LLM judge")
    parser.add_argument("--strong-model", default=STRONG_MODEL, help="strong model name for API judging")
    parser.add_argument("--api-url", default=API_URL, help="chat completions endpoint")
    parser.add_argument("--llm-timeout", type=float, default=180.0, help="LLM API timeout seconds")
    parser.add_argument("--llm-max-retries", type=int, default=LLM_MAX_RETRIES, help="max retries for LLM API call")
    parser.add_argument("--fail-on-llm-error", action="store_true", help="stop execution if one LLM call fails")
    args = parser.parse_args()

    gt_root = Path(args.ground_truth).resolve()
    cand_root = Path(args.candidate).resolve()
    out_dir = Path(args.out_dir).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    if not gt_root.exists() or not cand_root.exists():
        raise FileNotFoundError("ground-truth or candidate path does not exist")

    gt_files = sorted([p for p in gt_root.rglob("*.rs") if p.is_file()])
    cand_map = {p.relative_to(cand_root): p for p in cand_root.rglob("*.rs") if p.is_file()}

    records: List[TriageRecord] = []
    llm_tasks = []
    missing = []
    llm_judged = 0
    llm_errors = 0

    for gt_path in gt_files:
        rel = gt_path.relative_to(gt_root)
        cand_path = cand_map.get(rel)
        if cand_path is None:
            missing.append(str(rel))
            continue

        gt_code = gt_path.read_text(encoding="utf-8", errors="ignore")
        cand_code = cand_path.read_text(encoding="utf-8", errors="ignore")
        rec = triage_one(str(rel), gt_code, cand_code)
        rec.stage2_class, rec.stage2_reason = stage2_review(rec)

        if should_run_llm(rec, args.llm_mode):
            try:
                apply_llm_judgment(
                    rec,
                    gt_code,
                    cand_code,
                    model=args.strong_model,
                    api_url=args.api_url,
                    api_key=API_KEY,
                    timeout=max(1.0, args.llm_timeout),
                    max_retries=max(0, args.llm_max_retries),
                )
                llm_judged += 1
            except Exception as e:
                llm_errors += 1
                rec.llm_error = str(e)
                if args.fail_on_llm_error:
                    raise

        if rec.llm_verdict == "highly_consistent":
            rec.final_verdict = "consistent"
        elif rec.llm_verdict == "fundamental_error":
            rec.final_verdict = "inconsistent"
        elif rec.llm_verdict == "needs_review":
            rec.final_verdict = "review_required"
        else:
            rec.final_verdict = rec.verdict

        records.append(rec)

        if rec.verdict == "review_required" or rec.confidence < args.llm_threshold:
            llm_tasks.append(llm_task(rec, gt_code, cand_code))

    summary = {
        "total_gt_files": len(gt_files),
        "compared": len(records),
        "missing_in_candidate": missing,
        "verdict_count": {
            "consistent": sum(1 for r in records if r.verdict == "consistent"),
            "inconsistent": sum(1 for r in records if r.verdict == "inconsistent"),
            "review_required": sum(1 for r in records if r.verdict == "review_required"),
        },
        "stage2_count": {
            "confirmed_inconsistent": sum(1 for r in records if r.stage2_class == "confirmed_inconsistent"),
            "likely_consistent_need_spotcheck": sum(1 for r in records if r.stage2_class == "likely_consistent_need_spotcheck"),
            "high_risk_manual_review": sum(1 for r in records if r.stage2_class == "high_risk_manual_review"),
        },
        "final_verdict_count": {
            "consistent": sum(1 for r in records if r.final_verdict == "consistent"),
            "inconsistent": sum(1 for r in records if r.final_verdict == "inconsistent"),
            "review_required": sum(1 for r in records if r.final_verdict == "review_required"),
        },
        "llm": {
            "mode": args.llm_mode,
            "model": args.strong_model,
            "judged_files": llm_judged,
            "errors": llm_errors,
        },
    }

    triage_json = out_dir / "semantic_triage.json"
    triage_csv = out_dir / "semantic_triage.csv"
    llm_jsonl = out_dir / "semantic_llm_tasks.jsonl"

    triage_json.write_text(
        json.dumps(
            {
                "summary": summary,
                "records": [
                    {
                        "file": r.file,
                        "verdict": r.verdict,
                        "confidence": r.confidence,
                        "exact_equal": r.exact_equal,
                        "stripped_equal": r.stripped_equal,
                        "similarity": r.similarity,
                        "hard_fail_hits": r.hard_fail_hits,
                        "risk_hits": r.risk_hits,
                        "notes": r.notes,
                        "stage2_class": r.stage2_class,
                        "stage2_reason": r.stage2_reason,
                        "llm_verdict": r.llm_verdict,
                        "llm_confidence": r.llm_confidence,
                        "llm_score": r.llm_score,
                        "llm_hard_fail_hits": r.llm_hard_fail_hits,
                        "llm_risk_hits": r.llm_risk_hits,
                        "llm_semantic_diffs": r.llm_semantic_diffs,
                        "llm_final_reason": r.llm_final_reason,
                        "llm_error": r.llm_error,
                        "final_verdict": r.final_verdict,
                    }
                    for r in records
                ],
            },
            indent=2,
            ensure_ascii=False,
        ),
        encoding="utf-8",
    )

    with triage_csv.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow([
            "file",
            "verdict",
            "confidence",
            "exact_equal",
            "stripped_equal",
            "similarity",
            "hard_fail_hits",
            "risk_hits",
            "notes",
            "stage2_class",
            "stage2_reason",
            "llm_verdict",
            "llm_confidence",
            "llm_score",
            "llm_hard_fail_hits",
            "llm_risk_hits",
            "llm_semantic_diffs",
            "llm_final_reason",
            "llm_error",
            "final_verdict",
        ])
        for r in records:
            writer.writerow([
                r.file,
                r.verdict,
                f"{r.confidence:.2f}",
                str(r.exact_equal),
                str(r.stripped_equal),
                f"{r.similarity:.4f}",
                ";".join(r.hard_fail_hits),
                ";".join(r.risk_hits),
                r.notes,
                r.stage2_class,
                r.stage2_reason,
                r.llm_verdict,
                f"{r.llm_confidence:.2f}",
                str(r.llm_score),
                ";".join(r.llm_hard_fail_hits),
                ";".join(r.llm_risk_hits),
                " | ".join(r.llm_semantic_diffs),
                r.llm_final_reason,
                r.llm_error,
                r.final_verdict,
            ])

    with llm_jsonl.open("w", encoding="utf-8") as f:
        for task in llm_tasks:
            f.write(json.dumps(task, ensure_ascii=False) + "\n")

    print("triage json:", triage_json)
    print("triage csv:", triage_csv)
    print("llm tasks:", llm_jsonl)
    print("summary:", summary)


if __name__ == "__main__":
    main()
