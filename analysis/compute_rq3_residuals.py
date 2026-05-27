#!/usr/bin/env python3
"""
Compute residual error categories after repair (RQ3).

Outputs (paper/):
- residual_errors_by_category.csv  -- aggregated counts per model/language/category
- residual_errors_by_language.csv -- aggregated counts per language/category
- error_transitions.csv -- counts from initial -> final categories (for repaired attempts)
- residual_errors_summary.txt -- short textual summary

Usage: run from repo root: python pipeline/compute_rq3_residuals.py
"""
from __future__ import annotations

import csv
from collections import Counter, defaultdict
from pathlib import Path
import argparse
import sys


ROOT = Path('/Users/dijkstra/PycharmProjects/VeriC-Rt')
DEFAULT_DATASET = ROOT / 'output_full_20260505_044701'


def read_csv(path: Path):
    if not path.exists():
        return []
    with path.open() as f:
        reader = csv.DictReader(f)
        return list(reader)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--datasets', nargs='*', default=[str(DEFAULT_DATASET)])
    args = parser.parse_args()

    datasets = [Path(p) for p in args.datasets]
    out_dir = ROOT / 'paper'
    out_dir.mkdir(parents=True, exist_ok=True)

    # Load initial rows indexed by (model, sample_id, attempt_id)
    initial_index = {}
    for ds in datasets:
        for row in read_csv(ds / 'initial_results.csv'):
            key = (row.get('model_name', ''), row.get('sample_id', ''), row.get('attempt_id', ''))
            initial_index[key] = row

    # Load repair rows and group by (model, sample_id)
    repair_rows = []
    for ds in datasets:
        repair_rows.extend(read_csv(ds / 'repair_results.csv'))

    grouped = defaultdict(list)
    for r in repair_rows:
        key = (r.get('model_name', ''), r.get('sample_id', ''))
        # normalize numeric fields
        try:
            r['repair_round'] = int(r.get('repair_round') or 0)
        except Exception:
            r['repair_round'] = 0
        grouped[key].append(r)

    residual_counts = Counter()
    residual_by_model_lang = defaultdict(Counter)
    residual_by_language = defaultdict(Counter)
    transitions = Counter()
    total_samples = 0
    residual_samples = 0

    for key, rows in grouped.items():
        model_name, sample_id = key
        total_samples += 1
        # if any repair round succeeded, consider sample fixed
        fixed = any(str(r.get('verify_success', '')).lower() == 'true' for r in rows)
        if fixed:
            continue
        residual_samples += 1
        # choose final row as one with max repair_round
        final = max(rows, key=lambda r: r.get('repair_round', 0))
        final_cat = final.get('failure_category', 'unknown') or 'unknown'
        lang = final.get('language', '') or 'unknown'
        residual_counts[final_cat] += 1
        residual_by_model_lang[(model_name, lang)][final_cat] += 1
        residual_by_language[lang][final_cat] += 1

        # try to find the corresponding initial row for transition
        attempt_id = final.get('attempt_id', '')
        init_key = (model_name, sample_id, attempt_id)
        init_row = initial_index.get(init_key)
        init_cat = init_row.get('failure_category') if init_row else 'unknown_initial'
        transitions[(init_cat or 'unknown_initial', final_cat)] += 1

    # write residual aggregation CSV (by model/language/category)
    out_csv = out_dir / 'residual_errors_by_category.csv'
    with out_csv.open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['model_name', 'language', 'failure_category', 'count', 'residual_total', 'ratio'])
        for (model, lang), counter in residual_by_model_lang.items():
            total = sum(counter.values())
            for cat, cnt in counter.most_common():
                writer.writerow([model, lang, cat, cnt, total, f'{cnt/total:.6f}'])

    # write overall residual CSV
    overall_csv = out_dir / 'residual_errors_overall.csv'
    with overall_csv.open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['failure_category', 'count', 'ratio_of_residuals'])
        total_res = sum(residual_counts.values())
        for cat, cnt in residual_counts.most_common():
            writer.writerow([cat, cnt, f'{cnt/total_res:.6f}'])

    # write language-wise residual CSV
    by_lang_csv = out_dir / 'residual_errors_by_language.csv'
    with by_lang_csv.open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['language', 'failure_category', 'count', 'language_residual_total', 'ratio_in_language', 'ratio_in_global_residual'])
        total_res = sum(residual_counts.values())
        languages = sorted(residual_by_language.keys())
        for lang in languages:
            lang_total = sum(residual_by_language[lang].values())
            for cat, cnt in residual_by_language[lang].most_common():
                ratio_lang = (cnt / lang_total) if lang_total else 0.0
                ratio_global = (cnt / total_res) if total_res else 0.0
                writer.writerow([lang, cat, cnt, lang_total, f'{ratio_lang:.6f}', f'{ratio_global:.6f}'])

    # write transitions
    trans_csv = out_dir / 'error_transitions.csv'
    with trans_csv.open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['initial_category', 'final_category', 'count'])
        for (init_cat, final_cat), cnt in transitions.most_common():
            writer.writerow([init_cat, final_cat, cnt])

    # summary
    summary = out_dir / 'residual_errors_summary.txt'
    with summary.open('w') as f:
        f.write('RQ3: Residual error summary after repair\n')
        f.write(f'Total samples tested for repair: {total_samples}\n')
        f.write(f'Total residual samples (not fixed): {residual_samples}\n')
        f.write('\nTop residual categories (overall):\n')
        for cat, cnt in residual_counts.most_common(20):
            f.write(f' - {cat}: {cnt} ({cnt/sum(residual_counts.values()):.2%})\n')
        f.write('\nResidual categories by language:\n')
        for lang in sorted(residual_by_language.keys()):
            lang_total = sum(residual_by_language[lang].values())
            f.write(f'\n{lang}: total_residual={lang_total}\n')
            for cat, cnt in residual_by_language[lang].most_common():
                f.write(f' - {cat}: {cnt} ({cnt/lang_total:.2%})\n')

    print(f'Wrote: {out_csv}')
    print(f'Wrote: {overall_csv}')
    print(f'Wrote: {by_lang_csv}')
    print(f'Wrote: {trans_csv}')
    print(f'Wrote: {summary}')


if __name__ == '__main__':
    main()
