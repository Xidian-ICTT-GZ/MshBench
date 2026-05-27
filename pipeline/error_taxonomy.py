from __future__ import annotations

from dataclasses import dataclass
from typing import Tuple


@dataclass(frozen=True)
class FailureInfo:
    stage: str
    category: str


def classify_failure(output: str, verified: bool, parse_ok: bool, type_ok: bool) -> FailureInfo:
    if verified:
        return FailureInfo(stage="success", category="success")

    lower = output.lower()

    if not parse_ok:
        return FailureInfo(stage="parse", category=_classify_parse(lower))
    if not type_ok:
        return FailureInfo(stage="type", category=_classify_type(lower))

    return FailureInfo(stage="verify", category=_classify_verify(lower))


def _classify_parse(lower: str) -> str:
    if "spec" in lower and "position" in lower:
        return "spec_out_of_position"
    if "syntax error" in lower or "parse error" in lower:
        return "syntax_error"
    return "parse_error"


def _classify_type(lower: str) -> str:
    if "include" in lower and "not found" in lower:
        return "include_error"
    if "undefined" in lower or "unknown identifier" in lower or "not in scope" in lower:
        return "unknown_identifier_or_symbol"
    if "predicate" in lower and "not found" in lower:
        return "missing_predicate"
    return "type_error"


def _classify_verify(lower: str) -> str:
    if "precondition" in lower or "requires" in lower:
        return "wrong_precondition"
    if "postcondition" in lower or "ensures" in lower:
        return "wrong_postcondition"
    if "loop" in lower and "invariant" in lower:
        return "loop_invariant_error"
    if "open" in lower or "close" in lower or "assert" in lower or "leak" in lower or "resource" in lower:
        return "open_close_assert_leak_error"
    if "ownership" in lower or "framing" in lower or "frame" in lower or "permission" in lower or "alias" in lower:
        return "ownership_framing_error"
    if "predicate" in lower and ("definition" in lower or "defined" in lower or "missing" in lower):
        return "wrong_predicate_definition"
    if "lemma" in lower or "proof obligation" in lower or "theorem" in lower:
        return "wrong_lemma"
    return "other_semantic_error"
