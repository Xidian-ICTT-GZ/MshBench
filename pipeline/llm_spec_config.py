from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional


PACKAGE_ROOT = Path(__file__).resolve().parent
DEFAULT_CONFIG_PATH = PACKAGE_ROOT / "configs" / "experiment.json"


@dataclass(frozen=True)
class ModelConfig:
    name: str
    model_name: str
    api_url_env: str = "OPENAI_API_URL"
    api_key_env: str = "OPENAI_API_KEY"
    temperature: float = 0.0
    top_p: float = 1.0
    max_tokens: int = 4096
    seed: Optional[int] = None
    presence_penalty: float = 0.0
    frequency_penalty: float = 0.0
    sampling_mode: str = "prompt_perturbation"


@dataclass(frozen=True)
class ExperimentConfig:
    expected_total: int = 116
    benchmark_root: str = "benchmark"
    output_root: str = "pipeline/results"
    log_root: str = "pipeline/logs"
    manifest_path: str = "pipeline/manifests/llm_spec_benchmark_manifest.json"
    pass_k: int = 5
    max_rounds: int = 5
    verifast_args: Dict[str, List[str]] = field(default_factory=dict)
    models: Dict[str, ModelConfig] = field(default_factory=dict)


@dataclass(frozen=True)
class BenchmarkRecord:
    benchmark_id: str
    language: str
    source_path: Path
    expected_spec_path: Path


def _to_model_config(name: str, raw: Dict[str, Any]) -> ModelConfig:
    return ModelConfig(
        name=name,
        model_name=raw.get("model_name", name),
        api_url_env=raw.get("api_url_env", "OPENAI_API_URL"),
        api_key_env=raw.get("api_key_env", "OPENAI_API_KEY"),
        temperature=float(raw.get("temperature", 0.0)),
        top_p=float(raw.get("top_p", 1.0)),
        max_tokens=int(raw.get("max_tokens", 4096)),
        seed=raw.get("seed"),
        presence_penalty=float(raw.get("presence_penalty", 0.0)),
        frequency_penalty=float(raw.get("frequency_penalty", 0.0)),
        sampling_mode=raw.get("sampling_mode", "prompt_perturbation"),
    )


def load_config(path: Optional[Path] = None) -> ExperimentConfig:
    cfg_path = path or DEFAULT_CONFIG_PATH
    data = json.loads(cfg_path.read_text(encoding="utf-8"))
    models = {name: _to_model_config(name, raw) for name, raw in data.get("models", {}).items()}
    return ExperimentConfig(
        expected_total=int(data.get("expected_total", 116)),
        benchmark_root=data.get("benchmark_root", "benchmark"),
        output_root=data.get("output_root", "pipeline/results"),
        log_root=data.get("log_root", "pipeline/logs"),
        manifest_path=data.get("manifest_path", "pipeline/manifests/llm_spec_benchmark_manifest.json"),
        pass_k=int(data.get("pass_k", 5)),
        max_rounds=int(data.get("max_rounds", 5)),
        verifast_args={k: list(v) for k, v in data.get("verifast_args", {}).items()},
        models=models,
    )


def infer_language(path: Path) -> str:
    suffix = path.suffix.lower()
    if suffix == ".c":
        return "c"
    if suffix == ".java":
        return "java"
    if suffix == ".rs":
        return "rust"
    return "unknown"


def load_manifest(manifest_path: Path, benchmark_root: Path) -> List[BenchmarkRecord]:
    data = json.loads(manifest_path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise ValueError("Benchmark manifest must be a JSON list.")

    records: List[BenchmarkRecord] = []
    for item in data:
        benchmark_id = item["benchmark_id"]
        language = item.get("language") or infer_language(Path(item["source_path"]))
        source_path = (benchmark_root / Path(item["source_path"])).resolve()
        expected_spec_path = (benchmark_root / Path(item.get("expected_spec_path", item["source_path"]))).resolve()
        records.append(
            BenchmarkRecord(
                benchmark_id=benchmark_id,
                language=language,
                source_path=source_path,
                expected_spec_path=expected_spec_path,
            )
        )
    return records
