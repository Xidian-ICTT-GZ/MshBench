#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import json
import hashlib
import requests
from pathlib import Path
from collections import defaultdict
import re
import csv

API_URL = "https://api.linyinet.asia/v1/chat/completions"
API_KEY = "sk-L02YqMYQV64Dyzl0stpksz12ta0PLX1CLA0jPmCmsMFkCOwW"
MODEL_NAME = "gpt-5.2"
TEMPERATURE = 0

ROOT_DIR = Path("/app/output")

models = ["claude-opus", "qwen3", "deepseek", "gpt52"]
languages = ["c", "java", "rust"]

CACHE_FILE = "classification_cache.json"

SYSTEM_PROMPT = """
You are a formal verification expert.

Classify VeriFast error logs into exactly one of the six categories.

F1: Missing Ownership
F2: Incomplete Framing
F3: Weak Invariants
F4: Alias Mis-specification
F5: Over-Strong Specifications
F6: Unsound Assumptions

Return JSON only.
"""

USER_PROMPT_TEMPLATE = """
Classify the following VeriFast error log into one of:

F1: Missing Ownership
F2: Incomplete Framing
F3: Weak Invariants
F4: Alias Mis-specification
F5: Over-Strong Specifications
F6: Unsound Assumptions

Return JSON only:

{{
  "classification": "F1" | "F2" | "F3" | "F4" | "F5" | "F6",
  "reason": "short explanation"
}}

Error Log:
{}
"""

if os.path.exists(CACHE_FILE):
    with open(CACHE_FILE, "r") as f:
        cache = json.load(f)
else:
    cache = {}

def clean_json(content):
    content = content.strip()
    content = re.sub(r"^```json", "", content)
    content = re.sub(r"```$", "", content)
    return content.strip()


def classify_with_gpt(error_text):

    error_hash = hashlib.md5(error_text.encode()).hexdigest()

    if error_hash in cache:
        return cache[error_hash]

    prompt = USER_PROMPT_TEMPLATE.format(error_text[:6000])

    headers = {
        "Authorization": f"Bearer {API_KEY}",
        "Content-Type": "application/json"
    }

    payload = {
        "model": MODEL_NAME,
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": prompt}
        ],
        "temperature": TEMPERATURE
    }

    response = requests.post(API_URL, headers=headers, json=payload)

    if response.status_code != 200:
        print("API ERROR:", response.text)
        return None

    result = response.json()
    content = result["choices"][0]["message"]["content"]

    try:
        cleaned = clean_json(content)
        parsed = json.loads(cleaned)
        cache[error_hash] = parsed
        return parsed
    except Exception:
        print("JSON parse error:", content)
        return None


lang_stats = {lang: defaultdict(int) for lang in languages}

model_stats = {model: defaultdict(int) for model in models}

model_lang_stats = {
    model: {lang: defaultdict(int) for lang in languages}
    for model in models
}

print("Starting classification...\n")

for model in models:

    model_path = ROOT_DIR / model
    if not model_path.exists():
        continue

    for lang in languages:

        lang_path = model_path / lang
        if not lang_path.exists():
            continue

        for log_file in lang_path.rglob("*.log"):

            print(f"Classifying: {log_file}")

            error_text = log_file.read_text(errors="ignore")

            result = classify_with_gpt(error_text)

            if not result:
                continue

            ftype = result["classification"]
            reason = result["reason"]

            print(f" -> {ftype}: {reason}")

            lang_stats[lang][ftype] += 1

            model_stats[model][ftype] += 1

            model_lang_stats[model][lang][ftype] += 1




with open(CACHE_FILE, "w") as f:
    json.dump(cache, f, indent=2)




print("\n==============================")
print("Failure Mode Statistics by Language")
print("==============================")

for lang in languages:

    print(f"\nLanguage: {lang.upper()}")

    total = 0
    for f in ["F1","F2","F3","F4","F5","F6"]:
        count = lang_stats[lang][f]
        print(f"{f}: {count}")
        total += count

    print("Total:", total)



print("\n==============================")
print("Failure Mode Statistics by Model")
print("==============================")

for model in models:

    print(f"\nModel: {model}")

    total = 0
    for f in ["F1","F2","F3","F4","F5","F6"]:
        count = model_stats[model][f]
        print(f"{f}: {count}")
        total += count

    print("Total:", total)


print("\n==============================")
print("Failure Mode Statistics by Model and Language")
print("==============================")

for model in models:

    print(f"\nModel: {model}")

    for lang in languages:

        print(f"  Language: {lang}")

        total = 0
        for f in ["F1","F2","F3","F4","F5","F6"]:
            count = model_lang_stats[model][lang][f]
            print(f"    {f}: {count}")
            total += count

        print(f"    Total: {total}")


with open("model_language_failure.csv", "w", newline="") as f:

    writer = csv.writer(f)

    writer.writerow([
        "Model",
        "Language",
        "F1",
        "F2",
        "F3",
        "F4",
        "F5",
        "F6"
    ])

    for model in models:
        for lang in languages:

            row = [model, lang]

            for ftype in ["F1","F2","F3","F4","F5","F6"]:
                row.append(model_lang_stats[model][lang][ftype])

            writer.writerow(row)


print("\nCSV exported: model_language_failure.csv")