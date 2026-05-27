# VeriC-Rt: LLM-Generated Formal Specifications with Verifier-Guided Repair

A structured, reproducible experiment pipeline for **LLM-based generation and repair of VeriFast formal specifications** across multiple programming languages (C, Java, Rust).

## Overview

This project investigates the ability of large language models (LLMs) to generate VeriFast-compatible formal specifications and applies **verifier-guided repair** to fix verification failures. It supports full experiment pipelines with configurable models, repair rounds, and pass@k evaluation.

**Supported languages:** C, Java, Rust
**Verification backend:** [VeriFast](https://github.com/verifast/verifast)
**Supported models:** Configurable via JSON (see config example below)  

## Project Structure

```
├── pipeline/                  # Core experiment pipeline
│   ├── configs/               # Experiment and model configuration (JSON)
│   ├── run_spec_experiment.py           # Main experiment entry point
│   ├── run_generation_stage.py          # Generation stage (LLM + VeriFast)
│   ├── run_repair_stage.py              # 3-round verifier-guided repair
│   ├── run_pass_at_5.py                 # Standalone pass@k + evaluation
│   ├── experiment_utils.py              # Shared utilities (call_llm, run_verifast, ...)
│   ├── llm_spec_config.py               # Configuration loader
│   ├── llm_spec_prompts.py              # Prompt template management
│   ├── error_taxonomy.py                # Failure classification taxonomy
│   ├── build_benchmark_metadata.py      # Benchmark metadata builder
│   ├── build_spec_free_dataset.py       # Spec-free dataset builder
│   ├── stat_ground_true_dataset.py      # Ground truth dataset statistics
│   ├── summarize_experiment_results.py  # Result summarization
│   └── summarize_extended_metrics.py    # Extended metric computation
├── analysis/                  # Standalone analysis & utility scripts
│   ├── compute_rq3_residuals.py         # RQ3: Residual error analysis
│   ├── compute_rq4_costs.py             # RQ4: Token/time cost analysis
│   ├── generate_specs.py                # Spec generation utilities
│   ├── analyze_sar_tcr_vsr.py           # SAR/TCR/VSR analysis
│   ├── batch_semantic_consistency.py    # Semantic consistency checks
│   ├── llm_spec_runner.py               # LLM spec generation runner
│   ├── repair_ground_true_rust_specs_gpt5.py  # Rust spec repair
│   └── run_llm_spec_pipeline.py         # Legacy pipeline wrapper
├── benchmark/                 # Benchmark source files (c/, java/, rust/)
├── data/                      # Benchmark metadata and dataset
├── ground_true/               # Ground truth specifications
├── prompt/                    # Language-specific prompt templates
│   ├── c.txt
│   ├── java.txt
│   └── rust.txt
├── output_*/                  # Experiment run outputs
├── paper/                     # Analysis outputs (CSV tables, summaries)
├── Dockerfile                 # Docker build (Ubuntu 22.04 + VeriFast + Rust)
└── README.md                  # This file
```

## Quick Start

### Prerequisites

- Python 3.10+
- [VeriFast](https://github.com/verifast/verifast) (v26.01+)
- Rust (nightly, for Rust verification)
- An LLM API endpoint (e.g., OpenAI-compatible)

### 1. Configuration

All model definitions live in a single JSON config file (default: `pipeline/configs/llm_spec_experiment.json`):

```json
{
  "models": {
    "gpt-5.5": {
      "api_url_env": "OPENAI_API_URL",
      "api_key_env": "OPENAI_API_KEY",
      "model_name": "gpt-5.5",
      "temperature": 0.0,
      "max_tokens": 4096,
      "sampling_mode": "prompt_perturbation"
    },
    "deepseek-v4-flash": { ... },
    "qwen3": { ... },
    "claude-opus": { ... }
  }
}
```

Each model entry specifies:
- `api_url_env` / `api_key_env` - environment variable names for API credentials
- `model_name` - the model identifier sent to the API
- Decoding parameters (temperature, top_p, max_tokens, seed, etc.)

Set API credentials via environment variables (e.g., in `.env` at project root):

```bash
# OpenAI (for gpt-5.5)
OPENAI_API_URL="https://api.openai.com/v1/chat/completions"
OPENAI_API_KEY="sk-..."

# OR DeepSeek (for deepseek-v4-flash)
DEEPSEEK_API_URL="..."
DEEPSEEK_API_KEY="..."
```

### 2. Run the Full Pipeline

```bash
# Run the complete pipeline (generation → repair → summarization) with one model:
python -m pipeline.run_spec_experiment \
  --benchmark-root ground_true \
  --metadata data/benchmark_metadata.csv \
  --data-dir data/benchmark \
  --config pipeline/configs/llm_spec_experiment.json \
  --model gpt-5.5 \
  --languages c,java \
  --pass-k 5 \
  --max-rounds 3 \
  --workers 4 \
  --run-prefix output_gpt55 \
  --progress-every 10
```

Run with different models by changing `--model`. Each pipeline invocation runs **one** model at a time.

### 3. Standalone pass@k Evaluation

```bash
# Run pass@5 with early stop for multiple models in one go:
python pipeline/run_pass_at_5.py \
  benchmark \
  output_my_passk \
  prompt \
  --config pipeline/configs/llm_spec_experiment.json \
  --models gpt-5.5,qwen3,claude-opus
```

Omit `--models` to run **all** models defined in the config.

## Pipeline Details

### Spec Generation

1. **Generation Stage** (`run_generation_stage.py`): For each benchmark program, the LLM generates `k` candidate specifications with prompt perturbation.
2. **Verification**: Each candidate is verified with VeriFast. Results are categorized using the failure taxonomy.
3. **Metrics computed**: SAR (Syntax Acceptance Rate), TCR (Type Checking Rate), VSR (Verification Success Rate), pass@k.

### Verifier-Guided Repair

1. **Repair Stage** (`run_repair_stage.py`): Failed verifications are fed back to the LLM along with VeriFast's error output for iterative repair.
2. Multiple repair rounds are attempted (configurable via `--max-rounds`).
3. After repair, residual failures are classified and analyzed.

### Failure Taxonomy

Errors are classified into categories including:
- `syntax_error` / `parse_error`
- `type_error`
- `ownership_framing_error`
- `wrong_precondition` / `wrong_postcondition`
- `wrong_predicate_definition`
- `wrong_lemma`
- `loop_invariant_error`
- `open_close_assert_leak_error`
- `other_semantic_error`

## Results

Aggregated experimental results are stored in `results/`:

| Directory | Content |
|-----------|---------|
| `results/<model>/` | Per-model pipeline experiment results (overall, language, structure metrics, failure distribution, repair rounds, costs) |
| `results/benchmark_stats/` | Ground truth dataset composition statistics |
| `results/passk_summary.*` | pass@k evaluation summary |

> Raw per-candidate results (`initial_results.csv`, `repair_results.csv`) are stored in `output_*/` directories and excluded from version control via `.gitignore`.

## Docker

A Docker image with VeriFast, LLVM/Clang 12, Java 11, and Rust nightly is provided:

```bash
docker build -t veric-rt .
docker run -it --rm \
  -v $(pwd):/workspace \
  -e API_URL="your-api-url" \
  -e API_KEY="your-api-key" \
  veric-rt
```

## Key Output Files

Each experiment run creates an `output_*/` directory containing:

| File | Description |
|------|-------------|
| `initial_results.csv` | Per-candidate generation + verification results |
| `repair_results.csv` | Per-round repair + verification results |
| `summary_report.txt` | Textual summary of all metrics |

Analysis scripts write CSV tables to the `paper/` directory.

## Requirements

- Python 3.10+
- Required packages: `requests`, `numpy`
- VeriFast v26.01+
- Rust nightly (for Rust benchmarks)
