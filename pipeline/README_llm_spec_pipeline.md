# llm_spec_pipeline

This directory holds a structured, reproducible experiment pipeline for LLM-based
generation and repair of VeriFast specifications.

## Layout

- `configs/`: experiment settings, model settings, decoding parameters
- `prompts/`: language-specific prompt templates
- `manifests/`: explicit benchmark manifests for reproducible benchmark selection
- `results/`: generated specs, verification outputs, repair candidates
- `logs/`: run logs and summary reports
- `runs/`: optional run snapshots and per-run working files

## Intended workflow

1. Load one manifest describing the exact benchmark set.
2. Load one config describing model decoding settings and repair rounds.
3. Run the structured runner to generate k candidates per program.
4. Verify each candidate with VeriFast.
5. Apply verifier-guided repairs when verification fails.
6. Validate all reported counts against the expected total.
