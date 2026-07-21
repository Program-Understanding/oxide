from typing import Any, Dict, List, Tuple, TypedDict


class FunctionDiffEntry(TypedDict, total=False):
    pair: Tuple[str, str]
    features: Dict[str, Any]
    info: Dict[str, Any]


class FunctionClassification(TypedDict, total=False):
    unmatched_target: List[str]
    unmatched_baseline: List[str]
    matched: List[Tuple[str, str]]
    modified: List[FunctionDiffEntry]


class FileDiffRecord(TypedDict, total=False):
    filenames: Dict[str, Any]
    function_classification: FunctionClassification
