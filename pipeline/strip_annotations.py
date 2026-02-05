#!/usr/bin/env python3
import sys
from pathlib import Path

def strip_comments(code: str) -> str:
    res = []
    i = 0
    n = len(code)

    in_string = False
    string_char = ''
    in_line_comment = False
    in_block_comment = False

    while i < n:
        c = code[i]
        nxt = code[i + 1] if i + 1 < n else ''

        if not in_line_comment and not in_block_comment:
            if not in_string and (c == '"' or c == "'"):
                in_string = True
                string_char = c
                res.append(c)
                i += 1
                continue

        if in_string:
            res.append(c)
            if c == string_char and code[i - 1] != '\\':
                in_string = False
            i += 1
            continue

        if not in_block_comment and c == '/' and nxt == '/':
            in_line_comment = True
            i += 2
            continue

        if not in_line_comment and c == '/' and nxt == '*':
            in_block_comment = True
            i += 2
            continue

        if in_line_comment:
            if c == '\n':
                in_line_comment = False
                res.append('\n')
            i += 1
            continue

        if in_block_comment:
            if c == '*' and nxt == '/':
                in_block_comment = False
                i += 2
            else:
                if c == '\n':
                    res.append('\n')
                i += 1
            continue

        res.append(c)
        i += 1

    return ''.join(res)


def process_file(src: Path, dst: Path):
    text = src.read_text(encoding="utf-8", errors="ignore")
    stripped = strip_comments(text)
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(stripped, encoding="utf-8")


def main(src_dir, dst_dir):
    for path in Path(src_dir).rglob("*"):
        if path.suffix in [".c", ".java", ".rs"]:
            rel = path.relative_to(src_dir)
            process_file(path, Path(dst_dir) / rel)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
