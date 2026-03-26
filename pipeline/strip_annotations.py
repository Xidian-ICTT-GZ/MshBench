#!/usr/bin/env python3
"""Strip specification annotations and comments without changing executable code."""

import argparse
from datetime import datetime
from pathlib import Path

TARGET_SUFFIXES = {".c", ".h", ".java", ".rs"}


def _is_escaped(text: str, idx: int) -> bool:
    backslashes = 0
    j = idx - 1
    while j >= 0 and text[j] == "\\":
        backslashes += 1
        j -= 1
    return backslashes % 2 == 1


def _is_word_char(ch: str) -> bool:
    return ch.isalnum() or ch == "_"


def _needs_separator(prev_char: str, next_char: str) -> bool:
    if not prev_char or not next_char:
        return False
    return _is_word_char(prev_char) and _is_word_char(next_char)


def strip_comments(code: str) -> str:
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

        if c in {"\"", "'"}:
            in_string = True
            string_char = c
            res.append(c)
            i += 1
            continue

        if c == "/" and nxt == "/":
            i += 2
            while i < n and code[i] != "\n":
                i += 1
            if i < n and code[i] == "\n":
                res.append("\n")
                i += 1
            continue

        if c == "/" and nxt == "*":
            prev_char = res[-1] if res else ""
            i += 2
            newline_count = 0
            while i < n:
                if i + 1 < n and code[i] == "*" and code[i + 1] == "/":
                    i += 2
                    break
                if code[i] == "\n":
                    newline_count += 1
                i += 1

            if newline_count > 0:
                res.extend("\n" * newline_count)
            else:
                next_char = code[i] if i < n else ""
                if _needs_separator(prev_char, next_char):
                    res.append(" ")
            continue

        res.append(c)
        i += 1

    return "".join(res)


def process_file(src: Path, dst: Path) -> None:
    text = src.read_text(encoding="utf-8", errors="ignore")
    stripped = strip_comments(text)
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(stripped, encoding="utf-8")


def should_process(path: Path) -> bool:
    return path.is_file() and path.suffix in TARGET_SUFFIXES


def main() -> None:
    repo_root = Path(__file__).resolve().parent.parent
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    parser = argparse.ArgumentParser(
        description="去除 ground_true 中 C/Java/Rust 文件的规约注释与普通注释。"
    )
    parser.add_argument(
        "src_dir",
        nargs="?",
        default=str(repo_root / "ground_true"),
        help="输入目录，默认: <repo>/ground_true",
    )
    parser.add_argument(
        "dst_dir",
        nargs="?",
        default=str(repo_root / f"output_{timestamp}"),
        help="输出目录，默认: <repo>/output_<timestamp>",
    )
    args = parser.parse_args()

    src_root = Path(args.src_dir).resolve()
    dst_root = Path(args.dst_dir).resolve()

    if not src_root.exists() or not src_root.is_dir():
        raise FileNotFoundError(f"Source directory not found: {src_root}")

    processed = 0
    for path in src_root.rglob("*"):
        if not should_process(path):
            continue
        rel = path.relative_to(src_root)
        process_file(path, dst_root / rel)
        processed += 1

    print(f"Processed files: {processed}")
    print(f"Output directory: {dst_root}")


if __name__ == "__main__":
    main()
