#!/usr/bin/env python3
"""使用单一大模型对 Java 文件做数据结构分类。"""

import argparse
import hashlib
import json
import random
import re
import shutil
import time
from pathlib import Path
from typing import Dict, Iterable, Tuple

import requests

API_URL = "https://api.linyinet.asia/v1/chat/completions"
API_KEY = "sk-V0l0NYVekKSdryZPEzCcCIzBeSb6u0xgrqlMeZhO7WBi7Hqx"
MODEL_NAME = "gpt-5.2"
TEMPERATURE = 0

MAX_RETRIES = 6
BASE_BACKOFF = 2
MAX_BACKOFF = 120
JITTER = 1.0
MIN_API_INTERVAL = 3.0

DEFAULT_CATEGORIES = ["Arithmetic", "Arrays", "Linklist", "Stack", "Tree"]
DEFAULT_FALLBACK = "Other"
CACHE_FILE = Path("java_ds_classification_cache.json")

LAST_API_CALL_TS = 0.0


def default_paths() -> Tuple[Path, Path]:
    repo_root = Path(__file__).resolve().parent.parent
    src_dir = repo_root / "ground_true_java_pass"
    dest_dir = repo_root / "ground_true_java_pass_classified"
    return src_dir, dest_dir


def load_cache() -> Dict[str, str]:
    if CACHE_FILE.exists():
        try:
            return json.loads(CACHE_FILE.read_text(encoding="utf-8"))
        except Exception:
            return {}
    return {}


def save_cache(cache: Dict[str, str]) -> None:
    CACHE_FILE.write_text(json.dumps(cache, ensure_ascii=False, indent=2), encoding="utf-8")


def hash_content(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8", errors="ignore")).hexdigest()


def read_file_excerpt(path: Path, max_chars: int) -> str:
    text = path.read_text(encoding="utf-8", errors="ignore")
    return text if len(text) <= max_chars else text[:max_chars]


def build_prompt(filename: str, content: str, categories: Tuple[str, ...]) -> str:
    category_hint = ", ".join(categories) if categories else ", ".join(DEFAULT_CATEGORIES)
    return (
        "你是代码分类器。\n"
        "任务：根据 Java 文件内容判断其最主要的数据结构类别。\n"
        "可参考类别：" + category_hint + "。也允许输出其他合理类别。\n"
        "只返回 JSON，格式严格为：{\"category\": \"类别名\"}。\n\n"
        f"文件名:\n{filename}\n\n"
        f"代码:\n{content}\n"
    )


def parse_category(text: str, categories: Tuple[str, ...]) -> str:
    cleaned = text.strip()
    cleaned = re.sub(r"^```json\s*", "", cleaned)
    cleaned = re.sub(r"```$", "", cleaned).strip()

    category = ""
    try:
        obj = json.loads(cleaned)
        category = str(obj.get("category", "")).strip()
    except Exception:
        pass

    if not category:
        return DEFAULT_FALLBACK

    if categories:
        if category in categories:
            return category
        for cat in categories:
            if re.search(rf"\b{re.escape(cat)}\b", cleaned, re.IGNORECASE):
                return cat
        return DEFAULT_FALLBACK

    return category


def normalize_category(name: str) -> str:
    safe = re.sub(r"[^A-Za-z0-9._-]+", "_", (name or "").strip())
    return safe or DEFAULT_FALLBACK


def resolve_conflict_path(category_dir: Path, file_name: str) -> Path:
    candidate = category_dir / file_name
    if not candidate.exists():
        return candidate

    stem = Path(file_name).stem
    suffix = Path(file_name).suffix
    index = 2
    while True:
        candidate = category_dir / f"{stem}_{index}{suffix}"
        if not candidate.exists():
            return candidate
        index += 1


def heuristic_category(rel: Path, categories: Tuple[str, ...]) -> str:
    text = str(rel).lower()
    pool = categories if categories else tuple(DEFAULT_CATEGORIES)

    rules = [
        ("Arithmetic", ["arith", "math", "calc", "abs", "min", "max", "number"]),
        ("Arrays", ["array", "arr", "vector", "bag", "buffer"]),
        ("Linklist", ["link", "linked", "listnode", "dll", "sll"]),
        ("Stack", ["stack", "push", "pop", "lifo"]),
        ("Tree", ["tree", "bst", "heap", "trie", "binary"]),
    ]

    for cat in pool:
        if cat.lower() in text:
            return cat

    for cat, keys in rules:
        if cat in pool and any(k in text for k in keys):
            return cat

    return DEFAULT_FALLBACK


def call_llm(prompt: str, api_key: str) -> str:
    global LAST_API_CALL_TS

    retry = 0
    while True:
        try:
            now = time.time()
            wait = MIN_API_INTERVAL - (now - LAST_API_CALL_TS)
            if wait > 0:
                time.sleep(wait)

            resp = requests.post(
                API_URL,
                headers={"Authorization": f"Bearer {api_key}"},
                json={
                    "model": MODEL_NAME,
                    "messages": [{"role": "user", "content": prompt}],
                    "temperature": TEMPERATURE,
                },
                timeout=120,
            )
            LAST_API_CALL_TS = time.time()

            if resp.status_code == 429:
                retry_after = resp.headers.get("Retry-After")
                base_sleep = int(retry_after) if (retry_after and retry_after.isdigit()) else min(MAX_BACKOFF, BASE_BACKOFF * (2 ** (retry + 1)))
                sleep_secs = base_sleep + random.uniform(0, JITTER)
                raise RuntimeError(f"API 429, sleep {sleep_secs:.1f}s, body: {resp.text[:500]}")

            if resp.status_code != 200:
                raise RuntimeError(f"API {resp.status_code}: {resp.text[:800]}")

            data = resp.json()
            return data["choices"][0]["message"]["content"]

        except Exception as exc:
            if retry >= MAX_RETRIES:
                raise
            retry += 1
            backoff = min(MAX_BACKOFF, BASE_BACKOFF * (2 ** retry)) + random.uniform(0, JITTER)
            m = re.search(r"sleep\s+([0-9]+(?:\.[0-9]+)?)s", str(exc))
            if m:
                backoff = max(backoff, float(m.group(1)))
            print(f"[{MODEL_NAME}] Retry {retry}/{MAX_RETRIES} after {backoff:.1f}s: {exc}")
            time.sleep(backoff)


def ensure_destination(dest_dir: Path, overwrite: bool, resume: bool) -> None:
    if dest_dir.exists():
        if overwrite:
            shutil.rmtree(dest_dir)
            dest_dir.mkdir(parents=True, exist_ok=True)
            return
        if resume:
            print(f"Destination exists, resume mode: {dest_dir}")
            return
        raise FileExistsError(f"Destination exists: {dest_dir}. Use --overwrite or --resume.")
    dest_dir.mkdir(parents=True, exist_ok=True)


def iter_java_files(src_dir: Path) -> Iterable[Path]:
    return (p for p in src_dir.rglob("*.java") if p.is_file())


def classify_files(
    src_dir: Path,
    dest_dir: Path,
    api_key: str,
    max_chars: int,
    dry_run: bool,
    categories: Tuple[str, ...],
) -> None:
    cache = load_cache()
    processed = 0
    api_fallback = 0

    for java_file in sorted(iter_java_files(src_dir)):
        rel = java_file.relative_to(src_dir)

        content = read_file_excerpt(java_file, max_chars)
        content_hash = hash_content(content)

        category = cache.get(content_hash)
        if not category:
            prompt = build_prompt(str(rel), content, categories)
            try:
                raw = call_llm(prompt, api_key)
                category = parse_category(raw, categories)
            except Exception as exc:
                category = heuristic_category(rel, categories)
                api_fallback += 1
                print(f"[WARN] API failed for {rel}, use heuristic '{category}': {exc}")

            cache[content_hash] = category
            save_cache(cache)

        category_dir = normalize_category(category)
        target_root = dest_dir / category_dir
        target = resolve_conflict_path(target_root, java_file.name)

        if dry_run:
            print(f"[DRY-RUN] {rel} -> {category_dir}/{target.name}")
            processed += 1
            continue

        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(java_file, target)
        print(f"{rel} -> {category_dir}/{target.name}")
        processed += 1

    print(f"Model: {MODEL_NAME}")
    print(f"Total processed: {processed}")
    if api_fallback:
        print(f"Heuristic fallback used: {api_fallback}")


def parse_args() -> argparse.Namespace:
    src_default, dest_default = default_paths()
    parser = argparse.ArgumentParser(description="单模型 Java 数据结构分类脚本")
    parser.add_argument("--src", type=Path, default=src_default, help=f"源目录，默认: {src_default}")
    parser.add_argument("--dest", type=Path, default=dest_default, help=f"目标目录，默认: {dest_default}")
    parser.add_argument("--max-chars", type=int, default=8000, help="每个文件发送给模型的最大字符数")
    parser.add_argument("--overwrite", action="store_true", help="覆盖输出目录")
    parser.add_argument("--resume", action="store_true", default=True, help="续跑模式（默认开启）")
    parser.add_argument("--no-resume", action="store_false", dest="resume", help="关闭续跑模式")
    parser.add_argument("--dry-run", action="store_true", help="仅显示分类结果，不复制文件")
    parser.add_argument("--categories", type=str, default="", help="类别白名单，逗号分隔")
    return parser.parse_args()


def main() -> None:
    args = parse_args()

    if not API_KEY:
        raise RuntimeError("API_KEY 为空，请在脚本中填写。")
    if not args.src.exists():
        raise FileNotFoundError(f"源目录不存在: {args.src}")

    ensure_destination(args.dest, args.overwrite, args.resume)

    categories = tuple(c.strip() for c in args.categories.split(",") if c.strip())
    classify_files(
        src_dir=args.src,
        dest_dir=args.dest,
        api_key=API_KEY,
        max_chars=args.max_chars,
        dry_run=args.dry_run,
        categories=categories,
    )


if __name__ == "__main__":
    main()
