from typing import Any, Dict, List, Optional, TypedDict


class PromptConfig(TypedDict, total=False):
    name: str
    version: str
    system: str
    schema: Dict[str, Any]
    notes: List[str]


class AnalyzerResult(TypedDict, total=False):
    target: str
    baseline: str
    stats: Dict[str, Any]
    triage_index: List[Dict[str, Any]]
    per_function_results: List[Dict[str, Any]]
    file_pairs: List[Dict[str, Any]]
    artifact_root: Optional[str]


class AgentResult(TypedDict, total=False):
    label: str
    analysis_md: str
    final_md: str
    failure_reason: Optional[str]
    failure_detail: str
    llm_elapsed_s: float
    llm_input_tokens: int
    llm_output_tokens: int
    llm_total_tokens: int


class AnalyzeFunctionResult(TypedDict, total=False):
    label: str
    why: str
    flagged: bool
    verdict: str
    func_dir: str
    triage_ran: bool
    failure_reason: Optional[str]
    failure_detail: str
    diff_elapsed_s: float
    llm_elapsed_s: float
    llm_input_tokens: int
    llm_output_tokens: int
    llm_total_tokens: int
    callee_augmented: bool


class ComparisonStats(TypedDict, total=False):
    target: str
    baseline: str
    target_name: str
    baseline_name: str
    diff_mode: str
    filter_mode: str
    modified_files: int
    flagged_files: int
    modified_functions: int
    filtered_functions: int
    excluded_functions: int
    flagged_functions: int
    failed_functions: int
    callee_augmented_count: int
    gt_target_count: int
    gt_retained: int
    hit: int
    dismissed: int
    failed: int
    input_tokens: int
    output_tokens: int
    total_tokens: int
    avg_input_tokens: float
    avg_output_tokens: float
    avg_total_tokens: float
