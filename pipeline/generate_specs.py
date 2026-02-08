import requests
from pathlib import Path
import sys
import time
import re

API_URL = "https://api.linyinet.asia/v1/chat/completions"
API_KEY = ""

MODELS = {
    "claude-opus": "claude-opus-4-5-20251101",
    "qwen3": "qwen3-max",
    "deepseek": "deepseek-v3.2",
    "gpt52": "gpt-5.2",
}

PROMPT_DIR = Path("/app/prompt")

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

def clean_output(text: str) -> str:
    text = re.sub(r"```[a-zA-Z]*\n?", "", text)
    text = re.sub(r"```", "", text)
    text = re.sub(r"^\s*\d+\)\s.*$", "", text, flags=re.MULTILINE)
    text = re.sub(r"^\s*#+\s.*$", "", text, flags=re.MULTILINE)
    text = re.sub(
        r"^.*(Predicate definitions|Function contracts|Loop invariants|Lemmas).*$",
        "",
        text,
        flags=re.MULTILINE,
    )
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()

def call_llm(model, code, lang, prompts):
    prompt_template = prompts.get(lang)
    if prompt_template is None:
        raise ValueError(f"Unsupported language: {lang}")

    prompt = prompt_template.replace("{CODE}", code)

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
    resp.raise_for_status()
    return resp.json()["choices"][0]["message"]["content"]

def main(src_root, out_root):
    src_root = Path(src_root).resolve()
    out_root = Path(out_root).resolve()
    out_root.mkdir(parents=True, exist_ok=True)

    prompts = load_prompts(PROMPT_DIR)

    for model_key, model_name in MODELS.items():
        print(f"\n=== 使用模型 {model_key} ===")
        model_out_root = out_root / model_key
        model_out_root.mkdir(parents=True, exist_ok=True)

        for path in src_root.rglob("*"):
            if not path.is_file():
                continue

            lang = detect_language(path)
            if lang == "unknown":
                continue

            rel_path = path.relative_to(src_root)
            dst_file = model_out_root / lang / rel_path
            dst_file.parent.mkdir(parents=True, exist_ok=True)

            code = path.read_text()
            try:
                raw = call_llm(model_name, code, lang, prompts)
                cleaned = clean_output(raw)
            except Exception as e:
                print(f"[ERROR] {model_key} 处理 {path}: {e}")
                continue

            dst_file.write_text(cleaned)
            print(f"[OK] {dst_file}")
            time.sleep(2)

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("用法: python3 generate_specs.py <input_dir> <output_dir>")
        sys.exit(1)

    main(sys.argv[1], sys.argv[2])
