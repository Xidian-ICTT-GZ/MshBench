import requests
from pathlib import Path
import time
import re
import random
import argparse
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime

ROOT_DIR = Path(__file__).resolve().parent.parent
ENV_FILE = ROOT_DIR / ".env"


def normalize_env_value(value: str) -> str:
    # Remove common wrapping quotes, including smart quotes copied from rich text.
    value = value.strip()
    if len(value) >= 2:
        pairs = [
            ('"', '"'),
            ("'", "'"),
            ("\u201c", "\u201d"),
            ("\u2018", "\u2019"),
        ]
        for left, right in pairs:
            if value.startswith(left) and value.endswith(right):
                value = value[1:-1].strip()
                break
    return value


def load_env_file(env_file: Path):
    env = {}
    if not env_file.exists():
        return env

    for raw_line in env_file.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        env[key.strip()] = normalize_env_value(value)
    return env


ENV = load_env_file(ENV_FILE)
API_URL = ENV.get("API_URL", "")
API_KEY = ENV.get("API_KEY", "")

MAX_RETRIES = 6
BASE_BACKOFF = 2
MAX_BACKOFF = 120
JITTER = 1.0

MODELS = {
    "claude-opus": "claude-opus-4-5-20251101",
    "qwen3": "qwen3-max",
    "deepseek": "deepseek-v3.2",
    "gpt52": "gpt-5.2",
}

PROMPT_DIR = Path("/app/prompt")
MIN_API_INTERVAL = 0.2

REQ_LOCK = threading.Lock()
LAST_API_TS = 0.0

def load_prompts(prompt_dir: Path):
    prompts = {}
    for lang in ["c", "java", "rust"]:
        p = prompt_dir / f"{lang}.txt"
        if not p.exists():
            raise FileNotFoundError(f"Prompt file not found: {p}")
        prompts[lang] = p.read_text()
    return prompts

def detect_language(path: Path) -> str:
    ext = path.suffix.lower()
    if ext == ".c":
        return "c"
    if ext == ".rs":
        return "rust"
    if ext == ".java":
        return "java"
    return "unknown"


def extract_code_from_markdown(text: str) -> str:
    blocks = re.findall(r"```[a-zA-Z0-9_+-]*\n([\s\S]*?)```", text)
    if not blocks:
        return text
    return max(blocks, key=len)


def _is_escaped(text: str, idx: int) -> bool:
    backslashes = 0
    j = idx - 1
    while j >= 0 and text[j] == "\\":
        backslashes += 1
        j -= 1
    return backslashes % 2 == 1


def strip_non_spec_comments(code: str) -> str:
    res = []
    i = 0
    n = len(code)
    in_string = False
    string_char = ""

    while i < n:
        c = code[i]
        nxt = code[i + 1] if i + 1 < n else ""

        if in_string:
            res.append(c)
            if c == string_char and not _is_escaped(code, i):
                in_string = False
            i += 1
            continue

        if c in {'"', "'"}:
            in_string = True
            string_char = c
            res.append(c)
            i += 1
            continue

        if c == "/" and nxt == "/":
            line_end = code.find("\n", i)
            if line_end == -1:
                line_end = n
            rest = code[i + 2:line_end].lstrip()
            is_spec = rest.startswith("@") or rest.startswith("//@")
            is_verifast_options = rest.startswith("verifast_options{")
            if is_spec or is_verifast_options:
                res.append(code[i:line_end])
            if line_end < n:
                res.append("\n")
                i = line_end + 1
            else:
                i = line_end
            continue

        if c == "/" and nxt == "*":
            is_spec_block = (i + 2 < n and code[i + 2] == "@")
            end = code.find("*/", i + 2)
            if end == -1:
                end = n - 2
            segment = code[i:end + 2]
            if is_spec_block:
                res.append(segment)
            else:
                newline_count = segment.count("\n")
                if newline_count:
                    res.append("\n" * newline_count)
            i = end + 2
            continue

        res.append(c)
        i += 1

    return "".join(res)


def clean_output(text: str, lang: str, source_code: str) -> str:
    text = extract_code_from_markdown(text)
    text = re.sub(r"^\s*\d+\)\s.*$", "", text, flags=re.MULTILINE)
    text = re.sub(r"^\s*#+\s.*$", "", text, flags=re.MULTILINE)
    text = re.sub(
        r"^.*(Predicate definitions|Function contracts|Loop invariants|Lemmas).*$",
        "",
        text,
        flags=re.MULTILINE,
    )
    text = strip_non_spec_comments(text)

    if lang == "rust":
        # Preserve rust verifier options pragma if present in source.
        src_opts = re.findall(r"^\s*//\s*verifast_options\{[^\n]*\}", source_code, flags=re.MULTILINE)
        out_has_opts = re.search(r"^\s*//\s*verifast_options\{[^\n]*\}", text, flags=re.MULTILINE)
        if src_opts and not out_has_opts:
            text = src_opts[0] + "\n" + text

    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()

def call_llm(model, code, lang, prompts):
    global LAST_API_TS

    prompt_template = prompts.get(lang)
    if prompt_template is None:
        raise ValueError(f"Unsupported language: {lang}")

    prompt = prompt_template.replace("{CODE}", code)

    retry = 0
    while True:
        with REQ_LOCK:
            now = time.time()
            wait = MIN_API_INTERVAL - (now - LAST_API_TS)
            if wait > 0:
                time.sleep(wait)
            LAST_API_TS = time.time()

        resp = requests.post(
            API_URL,
            headers={"Authorization": f"Bearer {API_KEY}"},
            json={
                "model": model,
                "messages": [{"role": "user", "content": prompt}],
                "temperature": 0.2,
            },
            timeout=120,
        )

        if resp.status_code == 200:
            return resp.json()["choices"][0]["message"]["content"]

        if resp.status_code == 429:
            if retry >= MAX_RETRIES:
                raise RuntimeError(
                    f"429 after {MAX_RETRIES} retries: {resp.text[:300]}"
                )

            retry += 1
            retry_after = resp.headers.get("Retry-After")
            if retry_after and retry_after.isdigit():
                backoff = int(retry_after)
            else:
                backoff = min(MAX_BACKOFF, BASE_BACKOFF * (2 ** retry))
            backoff += random.uniform(0, JITTER)
            print(f"[429] {model} retry {retry}/{MAX_RETRIES}, sleep {backoff:.1f}s")
            time.sleep(backoff)
            continue

        resp.raise_for_status()


def collect_source_files(src_root: Path):
    files = []
    for path in src_root.rglob("*"):
        if not path.is_file():
            continue
        if detect_language(path) != "unknown":
            files.append(path)
    return files


def process_one_file(model_key, model_name, src_root, model_out_root, path, prompts):
    lang = detect_language(path)
    rel_path = path.relative_to(src_root)
    rel_parts = rel_path.parts
    if rel_parts and rel_parts[0] == lang:
        rel_path = Path(*rel_parts[1:]) if len(rel_parts) > 1 else Path(path.name)

    dst_file = model_out_root / lang / rel_path
    dst_file.parent.mkdir(parents=True, exist_ok=True)

    code = path.read_text(encoding="utf-8", errors="ignore")
    raw = call_llm(model_name, code, lang, prompts)
    cleaned = clean_output(raw, lang=lang, source_code=code)
    dst_file.write_text(cleaned, encoding="utf-8")
    return dst_file


def main(src_root, out_root, workers):
    if not API_KEY:
        raise RuntimeError("Missing API_KEY in .env at repo root")

    # Catch common copy/paste issue: API key wrapped by smart quotes.
    if API_KEY[0] in {"\u201c", "\u201d", "\u2018", "\u2019", '"', "'"}:
        raise RuntimeError("Invalid API_KEY format in .env: remove wrapping quotes")

    src_root = Path(src_root).resolve()
    out_root = Path(out_root).resolve()
    out_root.mkdir(parents=True, exist_ok=True)

    prompts = load_prompts(PROMPT_DIR)
    files = collect_source_files(src_root)
    print(f"待处理文件数: {len(files)}")

    for model_key, model_name in MODELS.items():
        print(f"\n=== 使用模型 {model_key} ===")
        model_out_root = out_root / model_key
        model_out_root.mkdir(parents=True, exist_ok=True)

        with ThreadPoolExecutor(max_workers=max(1, workers)) as executor:
            futures = {
                executor.submit(
                    process_one_file,
                    model_key,
                    model_name,
                    src_root,
                    model_out_root,
                    path,
                    prompts,
                ): path
                for path in files
            }

            for future in as_completed(futures):
                path = futures[future]
                try:
                    dst_file = future.result()
                    print(f"[OK] {dst_file}")
                except Exception as e:
                    print(f"[ERROR] {model_key} 处理 {path}: {e}")

if __name__ == "__main__":
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    parser = argparse.ArgumentParser(description="Generate VeriFast specs with optional concurrency")
    parser.add_argument("input_dir", nargs="?", default="/app/benchmark", help="输入目录")
    parser.add_argument("output_dir", nargs="?", default=f"/app/output_{ts}", help="输出目录")
    parser.add_argument("--workers", type=int, default=4, help="并发线程数")
    args = parser.parse_args()

    print(f"输入目录: {args.input_dir}")
    print(f"输出目录: {args.output_dir}")
    print(f"并发线程: {args.workers}")
    main(args.input_dir, args.output_dir, args.workers)
