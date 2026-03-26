#!/usr/bin/env python3

import subprocess
import requests
import json
import re
from pathlib import Path
from difflib import SequenceMatcher
from collections import defaultdict


API_URL = "https://api.linyinet.asia/v1/chat/completions"
API_KEY = "sk-L02YqMYQV64Dyzl0stpksz12ta0PLX1CLA0jPmCmsMFkCOwW"

REPAIR_MODEL = "gpt-5.2"

MAX_REPAIR_ROUNDS = 3
TEMPERATURE = 0.2

ROOT_DIR = Path("/app/output_at_5")

MODELS = [
    "claude-opus",
    "qwen3",
    "deepseek",
    "gpt52"
]


def clean_output(text):

    blocks = re.findall(r"```(?:c|java|rust)?\n(.*?)```", text, re.S)

    if blocks:
        return blocks[0].strip()

    return text.strip()



def call_llm(prompt):

    response = requests.post(
        API_URL,
        headers={
            "Authorization": f"Bearer {API_KEY}"
        },
        json={
            "model": REPAIR_MODEL,
            "messages": [
                {"role": "user", "content": prompt}
            ],
            "temperature": TEMPERATURE
        },
        timeout=120
    )

    response.raise_for_status()

    return response.json()["choices"][0]["message"]["content"]

def detect_language(file_path):
    suffix = Path(file_path).suffix.lower()
    if suffix == ".c":
        return "c"
    elif suffix == ".java":
        return "java"
    elif suffix == ".rs":
        return "rust"
    else:
        return None


def run_verifast(file_path):
    language = detect_language(file_path)
    if language is None:
        return False, "Unsupported file type"
    if language == "c":
        cmd = ["verifast", "-shared", str(file_path)]
    elif language in ("java", "rust"):
        cmd = ["verifast", str(file_path)]

    print(f"Running VeriFast ({language}): {file_path}")

    try:
        proc = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60
        )
        output = proc.stdout.decode(errors="ignore") + proc.stderr.decode(errors="ignore")
        log_dir = Path("verifast_logs")
        log_dir.mkdir(exist_ok=True)
        log_file = log_dir / (Path(file_path).name + ".log")
        log_file.write_text(output)

        success = proc.returncode == 0
        return success, output

    except subprocess.TimeoutExpired:
        return False, "VeriFast timeout"



def token_edit(old, new):

    a = old.split()
    b = new.split()

    ratio = SequenceMatcher(None, a, b).ratio()

    edit = (1 - ratio) * max(len(a), len(b))

    return int(edit)



def repair_file(file_path):

    code = file_path.read_text()

    rounds = 0
    edits = []

    while rounds < MAX_REPAIR_ROUNDS:

        ok, error_msg = run_verifast(file_path)

        if ok:
            return True, rounds, edits

        prompt = f"""
The following program fails VeriFast verification.

Error message:

{error_msg}

Please repair the code so that it verifies successfully.

Return only the corrected code.

{code}
"""

        try:
            llm_output = call_llm(prompt)
        except Exception as e:
            print("LLM error:", e)
            return False, rounds, edits

        new_code = clean_output(llm_output)

        edit = token_edit(code, new_code)
        edits.append(edit)

        code = new_code
        file_path.write_text(code)

        rounds += 1

    return False, rounds, edits



def main():

    results = []

    print("Starting VeriFast Repair Pipeline\n")

    for model in MODELS:

        model_dir = ROOT_DIR / model

        if not model_dir.exists():
            continue

        print("Processing Model:", model)

        for sample in model_dir.glob("sample_*"):

            for file in sample.rglob("*"):

                if file.suffix not in [".c", ".java", ".rs"]:
                    continue

                print("Repairing:", file)

                ok, rounds, edits = repair_file(file)

                avg_edit = sum(edits)/len(edits) if edits else 0

                results.append({
                    "model": model,
                    "file": str(file),
                    "success": ok,
                    "rounds": rounds,
                    "token_edit": avg_edit
                })

    Path("repair_report.json").write_text(
        json.dumps(results, indent=2)
    )

    stats = defaultdict(list)

    for r in results:
        stats[r["model"]].append(r)

    print("\n===== Repair Metrics per Model =====")

    for model, items in stats.items():

        rounds = [x["rounds"] for x in items]
        token = [x["token_edit"] for x in items]

        success = sum(1 for x in items if x["success"])
        total = len(items)

        avg_round = sum(rounds) / total
        avg_token = sum(token) / total
        success_rate = success / total * 100

        print("\nModel:", model)
        print("Avg Repair Rounds:", round(avg_round, 2))
        print("Avg Token Edit:", round(avg_token, 2))
        print("Success after Repair %:", round(success_rate, 2), "%")


    print("\n===== LaTeX Table =====")

    print("\\begin{tabular}{lccc}")
    print("\\toprule")
    print("Model & Avg Repair Rounds & Avg Token Edit & Success (\\%) \\\\")
    print("\\midrule")

    for model, items in stats.items():

        rounds = [x["rounds"] for x in items]
        token = [x["token_edit"] for x in items]

        success = sum(1 for x in items if x["success"])
        total = len(items)

        avg_round = sum(rounds) / total
        avg_token = sum(token) / total
        success_rate = success / total * 100

        print(
            f"{model} & {avg_round:.2f} & {avg_token:.2f} & {success_rate:.2f} \\\\"
        )

    print("\\bottomrule")
    print("\\end{tabular}")

if __name__ == "__main__":
    main()