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


class TriageState(TypedDict):
    diff: str
    fp_idx: int
    fp_total: int
    func_idx: int
    func_total: int
    notes: Dict[str, Any]
    trace_path: Optional[str]
    stage1_only: bool   # stop after Stage 1, never escalate to Stage 2
    stage2_only: bool   # skip Stage 1, go straight to Stage 2
    callee_texts: Dict[str, str]              # addr -> decomp of newly-added callees; non-empty forces Stage 2
    target_oid: str
    baseline_oid: str
    target_addr: str
    baseline_addr: str
    stage1_raw: Optional[str]
    stage1_json: Optional[Dict[str, Any]]     # {label, trigger, why}
    stage1_meta: Optional[Dict[str, Any]]     # {attempts, parsed_ok, duration_s, input_tokens, output_tokens, total_tokens}
    stage2_result: Optional[Dict[str, Any]]   # full result from nodes/stage2.py's agent run
    final_json: Optional[Dict[str, Any]]      # resolved {label} after Stage 1+2


class Stage1Result(TypedDict, total=False):
    label: str
    trigger: str
    why: str


class Stage2Result(TypedDict, total=False):
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
    trigger: str
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
    stage1_label: str
    stage1_why: str
    stage1_trigger: str
    stage1_input_tokens: int
    stage1_output_tokens: int
    stage1_tokens: int
    stage2_ran: bool
    routing_mode: str


class ComparisonStats(TypedDict, total=False):
    target: str
    baseline: str
    target_name: str
    baseline_name: str
    review_mode: str
    diff_mode: str
    filter_mode: str
    modified_files: int
    flagged_files: int
    modified_functions: int
    filtered_functions: int
    excluded_functions: int
    flagged_functions: int
    failed_functions: int
    direct_to_stage2_count: int
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
