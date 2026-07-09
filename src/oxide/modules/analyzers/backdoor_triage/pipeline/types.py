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
    target_oid: str                           # needed by Stage 3's binary-analysis MCP tools
    baseline_oid: str
    target_addr: str
    baseline_addr: str
    stage1_raw: Optional[str]
    stage1_json: Optional[Dict[str, Any]]     # {label, trigger, why}
    stage1_meta: Optional[Dict[str, Any]]     # {attempts, parsed_ok, duration_s, input_tokens, output_tokens, total_tokens}
    stage2_result: Optional[Dict[str, Any]]   # full result from nodes/stage2.py's agent run
    stage3_result: Optional[Dict[str, Any]]   # full result from nodes/stage3.py's investigation, if escalated
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


class Stage3Result(TypedDict, total=False):
    overall: str                       # "safe" | "backdoor" | "error"
    confirmed_functions: List[str]
    analysis_md: str
    final_md: str
    failure_reason: Optional[str]
    failure_detail: str
    elapsed_s: float
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
    stage3_ran: bool
    stage3_overall: Optional[str]
    stage3_confirmed_functions: List[str]
    stage3_failure_reason: Optional[str]
    stage3_elapsed_s: float
    stage3_input_tokens: int
    stage3_output_tokens: int
    stage3_total_tokens: int


class ComparisonStats(TypedDict, total=False):
    target: str
    baseline: str
    diff_raw: bool
    total_modified_functions: int
    filtered_functions: int
    safe_overall: int
    identified: int
    final_not_safe_filtered: int
    final_safe_filtered: int
    final_failed_filtered: int
    final_skipped_filtered: int
    failure_reason_counts: Dict[str, int]
    elapsed_s: float
    drift_elapsed_s: float
    triage_elapsed_s_excluding_drift: float
    diff_elapsed_s: float
    llm_elapsed_s: float
    other_elapsed_s: float
    llm_input_tokens: int
    llm_output_tokens: int
    llm_total_tokens: int
    stage1_flagged_count: int
    stage1_input_tokens: int
    stage1_output_tokens: int
    stage1_tokens: int
    stage2_ran_count: int
    stage2_input_tokens: int
    stage2_output_tokens: int
    stage2_tokens: int
    stage3_ran_count: int
    stage3_confirmed_count: int
    stage3_input_tokens: int
    stage3_output_tokens: int
    stage3_tokens: int
    gt_compromised_count: Optional[int]
    gt_targets: Optional[List[Dict[str, Any]]]
    gt_in_filtered: Optional[bool]
    hit_final: Optional[bool]
    tp_final: Optional[int]
    fp_final: Optional[int]
    fp_rate_final: Optional[float]
