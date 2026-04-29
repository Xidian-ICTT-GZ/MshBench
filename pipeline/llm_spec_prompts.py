from __future__ import annotations

from pathlib import Path


PACKAGE_ROOT = Path(__file__).resolve().parent
PROMPT_DIR = PACKAGE_ROOT.parent / "prompt"


def load_prompt(language: str) -> str:
    prompt_path = PROMPT_DIR / f"{language}.txt"
    if not prompt_path.exists():
        raise FileNotFoundError(f"Missing prompt template: {prompt_path}")
    return prompt_path.read_text(encoding="utf-8")


def build_language_hints(language: str) -> str:
    if language == "c":
        return "Focus on contracts, loop invariants, and local predicates in C comments."
    if language == "java":
        return "Focus on class invariants, array bounds, and VeriFast Java comments."
    if language == "rust":
        return "Focus on line annotations, predicates, and simple ownership invariants in Rust comments."
    return "Use conservative VeriFast annotations only."


def build_prompt(language: str, benchmark_id: str, source_code: str, candidate_index: int, pass_k: int, decoding_settings: str) -> str:
    template = load_prompt(language)
    return template.replace("{benchmark_id}", benchmark_id) \
        .replace("{source_code}", source_code) \
        .replace("{CODE}", source_code) \
        .replace("{candidate_index}", str(candidate_index)) \
        .replace("{pass_k}", str(pass_k)) \
        .replace("{decoding_settings}", decoding_settings) \
        .replace("{language_hints}", build_language_hints(language))


def build_repair_prompt(base_prompt: str, verifast_error: str, language: str) -> str:
    prompt = base_prompt + "\n\nPrevious VeriFast error:\n" + verifast_error + "\n\nRevise only the VeriFast specifications."
    lower_error = verifast_error.lower()
    if language == "c" and ("contract required" in lower_error or "function type implementation check" in lower_error):
        prompt += (
            "\n\nC contract repair template:\n"
            "- Add a contract immediately above each function missing one.\n"
            "- Use the weakest correct contract that preserves runtime code.\n"
            "- Do not introduce module(mainModule, ...) or [_]argv(...) templates.\n"
            "- Keep all non-spec C code byte-for-byte unchanged.\n"
        )
    if language == "java":
        prompt += (
            "\n\nJava annotation placement rules (STRICT):\n"
            "- Annotations MUST be placed immediately after the method signature, before the opening brace '{'.\n"
            "- Example format:\n"
            "  public static void main(String[] args)\n"
            "    //@ requires true;\n"
            "    //@ ensures true;\n"
            "  {\n"
            "- Never place annotations before the method signature.\n"
            "- Keep all Java code (method signatures, bodies, statements) byte-for-byte unchanged.\n"
            "- Only add or revise VeriFast line comments (//@ ...) between method signature and body.\n"
        )
    return prompt
