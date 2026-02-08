import requests
from pathlib import Path
import sys
import time
import re

API_URL = "https://api.linyinet.asia/v1/chat/completions"
API_KEY = "sk-pI1rFGsI8ea8K5jdjlAnL08GDEjtsx0m0y7ajuUuuuACp2Dx"

MODELS = {
    "claude-opus": "claude-opus-4-5-20251101",
    "qwen3": "qwen3-max",
    "deepseek": "deepseek-v3.2",
    "gpt52": "gpt-5.2",
}

PROMPTS = {
    "c": """You are an expert in verifying C programs using VeriFast
    with separation logic.

    Task:
    Given the following C source code, add VeriFast specifications so that
    the program is likely to PASS verification.

    Strict rules:
    - Output MUST be a single valid C source file.
    - Output MUST contain ONLY C code and VeriFast annotations.
    - DO NOT use Markdown or explanations.
    - Do NOT modify any existing C code.
    - You MAY insert:
      * /*@ predicate ... @*/
      * //@ requires / //@ ensures
      * //@ invariant
      * lemmas (only if necessary)

    Separation logic requirements (MANDATORY):
    - All specifications must be written in VeriFast-style separation logic.
    - Use `&*&` as the separating conjunction.
    - Do NOT use `&&` or other first-order logical conjunctions.
    - Use `||` for disjunction and `==>` for implication when needed.
    - Prefer predicates to describe memory ownership, permissions, and data
      structure shape.
    - Specifications should be as weak as possible while still sufficient
      for verification.

    Rules for preconditions and postconditions:
    - `//@ requires true;` and `//@ ensures true;` are ALLOWED when no
      meaningful non-trivial condition can be justified from the code.
    - When a non-trivial safety or functional condition is clearly implied
      by the code, it SHOULD be stated instead of using `true`.

    Anti-cheating rules for invariants (STRICTLY ENFORCED):
    - Loop invariants MUST NEVER be trivial.
    - The following are FORBIDDEN in loop invariants:
      * //@ invariant true;
      * logically equivalent forms such as `x == x`, `i >= i`, `A || !A`.

    - Every loop invariant MUST constrain the loop state in a meaningful way
      and MUST mention at least one variable that appears in the loop
      condition or is modified in the loop body.

    - If no meaningful loop invariant can be justified, the invariant MUST
      be OMITTED rather than replaced with a trivial one.

    The output MUST be directly verifiable by VeriFast.

    C source code:
    <<<CODE
    {CODE}
    CODE>>>""",

    "rust": """You are an expert in verifying Rust programs using VeriFast
with separation logic.

Target verifier: VeriFast (Rust frontend, separation logic).

Task:
Given the following Rust source code, add formal specifications so that
the program is likely to PASS verification with VeriFast.

Strict rules:
- Output MUST be a single valid Rust source file.
- Output MUST contain ONLY Rust code and VeriFast specification annotations.
- Do NOT use Markdown or explanations.
- Do NOT modify any existing Rust code.
- You MAY insert:
  * #[requires(...)]
  * #[ensures(...)]
  * #[invariant(...)]
  * predicates and lemmas supported by VeriFast for Rust

Separation logic requirements (MANDATORY):
- All specifications must be written in VeriFast-style separation logic,
  NOT in Prusti, Creusot, Viper, or Rust logical syntax.
- Specifications MUST describe heap ownership explicitly using predicates.
- Use separation logic conjunction to combine heap facts and pure facts.
- Do NOT use Rust boolean expressions as specifications
  (e.g., `result.is_null() == false`).
- Do NOT use type assertions such as `*result is Stack<T>`.
- Specifications must be expressible in VeriFast's assertion language only.

Specification style rules:
- Preconditions must state ownership of heap objects passed as raw pointers.
- Postconditions must describe:
  * returned ownership
  * preserved or transferred heap structure
- Use predicates to model linked data structures (e.g., stack, list, node).
- Avoid trivial specifications unless strictly necessary.
- Specifications should be as weak as possible while still sufficient
  for verification.

Loop invariant rules:
- Loop invariants must preserve ownership and data structure shape.
- Do NOT use trivial invariants such as `true`.
- Invariants must explain why the loop is safe and memory-correct.

Semantic rules:
- Preconditions must rule out undefined behavior
  (null dereference, use-after-free, invalid deallocation).
- Heap allocated objects must be matched with corresponding ownership
  predicates.
- Deallocation requires full ownership of the allocated object.

The output MUST be directly verifiable by VeriFast.

Rust source code:
<<<CODE
{CODE}
CODE>>>""",

    "java": """You are an expert in verifying Java programs using VeriFast
with separation logic.

Task:
Given the following Java source code, add VeriFast specifications so that
the program is likely to PASS verification.

Strict rules:
- Output MUST be a single valid Java source file.
- Output MUST contain ONLY Java code and VeriFast annotations.
- Do NOT use Markdown or explanations.
- Do NOT modify any existing Java code.
- You MAY insert:
  * //@ requires
  * //@ ensures
  * //@ invariant
  * /*@ predicate ... @*/
  * lemmas (only if necessary)

Separation logic requirements (MANDATORY):
- All specifications must be written in VeriFast-style separation logic
  following VeriFast Java semantics (NOT JML / OpenJML).
- Use `&*&` as the separating conjunction.
- Do NOT use `&&` or other first-order logical conjunctions.
- Use `||` for disjunction and `==>` for implication.
- Do NOT use conditional (ternary) expressions `?:` in specifications.
- Specifications MUST be expressed using conjunction, disjunction,
  and implication only.
- Prefer predicates to describe heap ownership, permissions, and object
  structure when relevant.
- It is allowed to combine arithmetic or value properties with separation
  logic using `&*&`.
- Specifications should be as weak as possible while still sufficient
  for verification.

Semantic rules:
- Use `result` to refer to the return value.
- Preconditions must rule out undefined behavior
  (e.g., arithmetic overflow, null dereference).
- Loop invariants must be strong enough to prove correctness:
  * Do NOT use trivially true invariants (e.g., `true`) unless no stronger
    invariant is required for verification.
  * Loop invariants must reflect the progress or preserved properties
    of the loop variables and heap state.
- Specifications must be acceptable to the VeriFast verifier and
  must not rely on Java-only expression features unsupported by VeriFast.

The output MUST be directly verifiable by VeriFast.

Java source code:
<<<CODE
{CODE}
CODE>>>""",
}

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

def call_llm(model, code, lang):
    prompt_template = PROMPTS.get(lang)
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
                raw = call_llm(model_name, code, lang)
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
