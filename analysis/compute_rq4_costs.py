#!/usr/bin/env python3
"""
RQ4: Cost analysis after verifier-guided repair.

Generates time and token cost tables (paper/):
- rq4_time_cost_by_language.csv
- rq4_token_cost_by_language.csv

Data sources:
- output_full_20260505_044701/initial_results.csv
- output_full_20260505_044701/repair_results.csv
"""
from __future__ import annotations

import csv
from collections import defaultdict
from pathlib import Path

import numpy as np


ROOT = Path('/Users/dijkstra/PycharmProjects/VeriC-Rt')
DATASET = ROOT / 'output_full_20260505_044701'
OUT_DIR = ROOT / 'paper'

LANG_ORDER = ['c', 'java', 'rust']
LANG_LABELS = {'c': 'C', 'java': 'Java', 'rust': 'Rust'}


def read_rows(path: Path):
    if not path.exists():
        return []
    with path.open() as f:
        return list(csv.DictReader(f))


def collect_costs(rows):
    data = defaultdict(lambda: {
        'latency': [],
        'tokens_in': [],
        'tokens_out': [],
    })
    for r in rows:
        lang = r.get('language', 'unknown')
        try:
            data[lang]['latency'].append(float(r.get('latency_sec') or 0.0))
        except Exception:
            pass
        try:
            data[lang]['tokens_in'].append(float(r.get('tokens_in') or 0.0))
        except Exception:
            pass
        try:
            data[lang]['tokens_out'].append(float(r.get('tokens_out') or 0.0))
        except Exception:
            pass
    return data


def summarize_costs(data):
    summary = {}
    for lang, values in data.items():
        latency = values['latency']
        tin = values['tokens_in']
        tout = values['tokens_out']
        summary[lang] = {
            'latency_total': sum(latency),
            'latency_avg': (sum(latency) / len(latency)) if latency else 0.0,
            'latency_n': len(latency),
            'tokens_in_total': sum(tin),
            'tokens_in_avg': (sum(tin) / len(tin)) if tin else 0.0,
            'tokens_out_total': sum(tout),
            'tokens_out_avg': (sum(tout) / len(tout)) if tout else 0.0,
        }
    return summary


def write_time_table(summary_gen, summary_rep, out_path: Path):
    with out_path.open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow([
            'language',
            'stage',
            'latency_total_sec',
            'latency_avg_sec',
            'num_calls',
        ])
        for lang in sorted(set(summary_gen) | set(summary_rep)):
            for stage, summary in [('generation', summary_gen), ('repair', summary_rep)]:
                s = summary.get(lang, {})
                writer.writerow([
                    lang,
                    stage,
                    f"{s.get('latency_total', 0.0):.4f}",
                    f"{s.get('latency_avg', 0.0):.4f}",
                    s.get('latency_n', 0),
                ])


def write_token_table(summary_gen, summary_rep, out_path: Path):
    with out_path.open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow([
            'language',
            'stage',
            'tokens_in_total',
            'tokens_out_total',
            'tokens_in_avg',
            'tokens_out_avg',
        ])
        for lang in sorted(set(summary_gen) | set(summary_rep)):
            for stage, summary in [('generation', summary_gen), ('repair', summary_rep)]:
                s = summary.get(lang, {})
                writer.writerow([
                    lang,
                    stage,
                    f"{s.get('tokens_in_total', 0.0):.1f}",
                    f"{s.get('tokens_out_total', 0.0):.1f}",
                    f"{s.get('tokens_in_avg', 0.0):.2f}",
                    f"{s.get('tokens_out_avg', 0.0):.2f}",
                ])





def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    gen_rows = read_rows(DATASET / 'initial_results.csv')
    rep_rows = read_rows(DATASET / 'repair_results.csv')

    gen_costs = collect_costs(gen_rows)
    rep_costs = collect_costs(rep_rows)
    gen_summary = summarize_costs(gen_costs)
    rep_summary = summarize_costs(rep_costs)

    write_time_table(gen_summary, rep_summary, OUT_DIR / 'rq4_time_cost_by_language.csv')
    write_token_table(gen_summary, rep_summary, OUT_DIR / 'rq4_token_cost_by_language.csv')

    print('Saved RQ4 outputs to paper/.')


if __name__ == '__main__':
    main()
