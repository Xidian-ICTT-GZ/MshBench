#!/usr/bin/env python3

import subprocess
from pathlib import Path
from collections import defaultdict
from difflib import SequenceMatcher

ROOT = Path("/app/output_at_5")

SUPPORTED = [".c", ".java", ".rs"]

MAX_REPAIR = 3


def detect_lang(p):
    s = p.suffix.lower()
    if s == ".c":
        return "c"
    if s == ".java":
        return "java"
    if s == ".rs":
        return "rust"
    return None


def run_verifast(p):

    lang = detect_lang(p)

    if lang == "c":
        cmd = ["verifast", "-shared", str(p)]
    else:
        cmd = ["verifast", str(p)]

    proc = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE
    )

    out = proc.stdout.decode() + proc.stderr.decode()

    return proc.returncode == 0, out


def token_edit(a, b):
    a = a.split()
    b = b.split()
    r = SequenceMatcher(None, a, b).ratio()
    return int((1 - r) * max(len(a), len(b)))


def repair_stub(code):
    """
    如果你不想调用LLM，这里只计算统计
    """
    return code


results = []

for model_dir in ROOT.iterdir():

    if not model_dir.is_dir():
        continue

    model = model_dir.name

    for file in model_dir.rglob("*"):

        if file.suffix.lower() not in SUPPORTED:
            continue

        code = file.read_text()

        ok, err = run_verifast(file)

        rounds = 0
        edits = []

        while not ok and rounds < MAX_REPAIR:

            new_code = repair_stub(code)

            edits.append(token_edit(code, new_code))

            file.write_text(new_code)

            code = new_code

            ok, err = run_verifast(file)

            rounds += 1

        results.append({
            "model": model,
            "success": ok,
            "rounds": rounds,
            "token_edit": sum(edits)/len(edits) if edits else 0
        })


stats = defaultdict(list)

for r in results:
    stats[r["model"]].append(r)


print("\n===== Table 6 Results =====")

for model, items in stats.items():

    rounds = [x["rounds"] for x in items]
    token = [x["token_edit"] for x in items]

    success = sum(1 for x in items if x["success"])
    total = len(items)

    print("\nModel:", model)
    print("Avg Repair Rounds:", sum(rounds)/total)
    print("Avg Token Edit:", sum(token)/total)
    print("Success after Repair %:", success/total*100)


print("\n===== LaTeX Table =====")

print("\\begin{tabular}{lccc}")
print("Model & Avg Repair Rounds & Avg Token Edit & Success (\\%) \\\\")

for model, items in stats.items():

    rounds = [x["rounds"] for x in items]
    token = [x["token_edit"] for x in items]

    success = sum(1 for x in items if x["success"])
    total = len(items)

    print(
        f"{model} & {sum(rounds)/total:.2f} & {sum(token)/total:.2f} & {success/total*100:.2f} \\\\"
    )

print("\\end{tabular}")