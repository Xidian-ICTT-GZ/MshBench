# Benchmark manifest

This directory stores the explicit benchmark selection used by the experiment pipeline.

Use `benchmark_manifest.template.json` as a starting point and copy it to
`benchmark_manifest.json` when you are ready to run a concrete 116-program study.

Each manifest entry should contain:

- `benchmark_id`: stable identifier used in outputs and tables
- `language`: one of `c`, `java`, `rust`
- `source_path`: relative path under `benchmark/`
- `expected_spec_path`: relative path to the benchmark's expected specification file
