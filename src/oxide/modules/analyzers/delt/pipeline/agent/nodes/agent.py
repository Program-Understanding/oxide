"""The triage agent: a file-backed local agent that reviews one modified-function
diff and decides whether the update inserted a backdoor. When the diff calls a
newly-added function, the callee decompilations are attached as extra evidence.
"""

import logging
import time
from typing import Any, Dict, Literal, Optional, Tuple

from oxide.modules.analyzers.delt.config import NAME
from oxide.modules.analyzers.delt.pipeline.agent import agent_runtime
from oxide.modules.analyzers.delt.pipeline.agent.telemetry.agent_trace import TraceLogger, append_trace_line
from oxide.modules.analyzers.delt.pipeline.utils.text_utils import _coerce_label, _coerce_str
from oxide.modules.analyzers.delt.pipeline.agent.telemetry.token_usage import collect_llm_usage_counts

try:
    from pydantic import BaseModel, Field
except ImportError:
    class BaseModel:  # type: ignore[no-redef]
        def __init__(self, **data: Any) -> None:
            for key, value in data.items():
                setattr(self, key, value)

    _FIELD_UNSET = object()

    def Field(default: Any = _FIELD_UNSET, **_kwargs: Any) -> Any:  # type: ignore[no-redef]
        return ... if default is _FIELD_UNSET else default

logger = logging.getLogger(NAME)


class AgentDecisionSchema(BaseModel):
    label: Literal["safe", "not_safe"] = Field(
        description="Final decision for the diff. Must be safe or not_safe.",
    )


def _normalize_decision_payload(payload: Dict[str, Any]) -> Tuple[Optional[Dict[str, Any]], bool]:
    label = _coerce_label(payload.get("label"))
    if label not in {"safe", "not_safe"}:
        return None, False
    return {"label": label}, True


def _error_result(why: str, *, failure_reason: str, failure_detail: str = "") -> Dict[str, Any]:
    return {
        "label": "failed",
        "why": _coerce_str(why),
        "analysis_md": "",
        "final_md": "",
        "failure_reason": failure_reason,
        "failure_detail": _coerce_str(failure_detail),
        "llm_elapsed_s": 0.0,
        "llm_input_tokens": 0,
        "llm_output_tokens": 0,
        "llm_total_tokens": 0,
    }


def run_agent(
    runtime: Any,
    diff_text: str,
    notes: Dict[str, Any],
    trace_path: Optional[str],
    callee_texts: Optional[Dict[str, str]] = None,
) -> Dict[str, Any]:
    """Run the triage agent on a pre-sanitized diff. Returns a result dict."""
    callee_texts = callee_texts or {}
    request_timeout_s = float(getattr(runtime, "agent_request_timeout_s", 150.0))

    if callee_texts:
        sys_prompt = runtime.agent_sys_callee
        prompt = (
            "Analyze /inputs/unified_diff.txt and the callee decompilations under /inputs/added_functions/.\n"
            "Write a provisional analysis to /work/analysis.md.\n"
            "Write your final decision to /work/final.md.\n"
            "After writing /work/final.md, call submit_decision.\n"
            "/work/final.md alone is not the final answer.\n"
            "LAST STEP: call submit_decision.\n"
            'Example final action: submit_decision(label="not_safe")\n'
            "Do not write another explanatory assistant message after /work/final.md.\n"
            "The run is not complete until submit_decision succeeds.\n"
        )
    else:
        sys_prompt = runtime.agent_sys
        prompt = (
            "Analyze /inputs/unified_diff.txt.\n"
            "Write a provisional analysis to /work/analysis.md.\n"
            "Write your final decision to /work/final.md.\n"
            "After writing /work/final.md, call submit_decision.\n"
            "/work/final.md alone is not the final answer.\n"
            "LAST STEP: call submit_decision.\n"
            'Example final action: submit_decision(label="not_safe")\n'
            "Do not write another explanatory assistant message after /work/final.md.\n"
            "The run is not complete until submit_decision succeeds.\n"
        )

    file_mirror: Dict[str, str] = {}
    final_holder: Dict[str, Any] = {}
    decision_tool = agent_runtime.make_decision_tool(
        "submit_decision",
        AgentDecisionSchema,
        final_holder,
        _normalize_decision_payload,
        doc="Submit the final triage decision after writing /work/final.md.",
    )
    agent = agent_runtime.build_triage_agent(
        main_model=runtime.agent_llm,
        file_mirror=file_mirror,
        decision_tool=decision_tool,
        system_prompt=sys_prompt,
    )

    out: Any = None
    invoke_elapsed_s = 0.0
    invoke_t0 = time.perf_counter()
    trace_logger = TraceLogger(trace_path)
    try:
        append_trace_line(trace_path, "[   0.00s] [agent] start", truncate=True)
        append_trace_line(trace_path, "[   0.00s] [agent] mode: astream (live trace + state collection)")
        config = {"configurable": {"thread_id": f"delt_agent_{time.time_ns()}"}}
        payload = agent_runtime.build_agent_payload(diff_text, prompt, callee_texts)
        out = agent_runtime.invoke_agent_with_timeout(
            agent, payload, config=config,
            timeout_s=request_timeout_s, trace_logger=trace_logger,
        )
        invoke_elapsed_s = time.perf_counter() - invoke_t0
    except TimeoutError as exc:
        msg = f"The agent timed out: {exc}."
        notes["observations"].append(msg)
        append_trace_line(trace_path, f"[{time.perf_counter() - invoke_t0:7.2f}s] [agent] error: timeout {exc}")
        return _error_result(
            f"The agent timed out after {request_timeout_s:g}s before reaching a final decision.",
            failure_reason="timeout", failure_detail=str(exc),
        )
    except agent_runtime.RepeatedToolCallError as exc:
        notes["observations"].append(f"Agent repeated tool call: {exc}")
        append_trace_line(trace_path, f"[{time.perf_counter() - invoke_t0:7.2f}s] [agent] error: repeated_tool_call {exc}")
        return _error_result(str(exc), failure_reason="repeated_tool_call")
    except Exception as exc:
        detail = str(exc)
        failure_reason = "timeout" if "timeout" in detail.lower() else "invoke_failed"
        notes["observations"].append(f"Agent invoke failed: {exc}.")
        why = ("The agent timed out before reaching a final decision."
               if failure_reason == "timeout"
               else "Agent triage pipeline failed before reaching a final decision.")
        append_trace_line(trace_path, f"[{time.perf_counter() - invoke_t0:7.2f}s] [agent] error: {failure_reason} {exc}")
        return _error_result(why, failure_reason=failure_reason, failure_detail=detail)

    analysis_md = _coerce_str(file_mirror.get("/work/analysis.md"))
    final_md = _coerce_str(file_mirror.get("/work/final.md"))
    messages = out.get("messages") if isinstance(out, dict) else getattr(out, "messages", None)
    llm_usage = collect_llm_usage_counts(messages)
    llm_input_tokens = int(llm_usage.get("input_tokens") or 0)
    llm_output_tokens = int(llm_usage.get("output_tokens") or 0)
    llm_total_tokens = int(llm_usage.get("total_tokens") or 0)
    final = final_holder.get("final")
    ok = isinstance(final, dict) and final.get("label") in {"safe", "not_safe"}

    if not ok or final is None:
        why = "The agent did not call submit_decision before the run ended."
        notes["observations"].append(why)
        append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] error: missing_final_answer")
        result = _error_result(why, failure_reason="missing_final_answer")
        result["analysis_md"] = analysis_md
        result["final_md"] = final_md
        result["llm_elapsed_s"] = invoke_elapsed_s
        result["llm_input_tokens"] = llm_input_tokens
        result["llm_output_tokens"] = llm_output_tokens
        result["llm_total_tokens"] = llm_total_tokens
        return result

    label = _coerce_label(final.get("label"))
    label = label if label in {"safe", "not_safe"} else "failed"
    append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] final: label={label}")
    if analysis_md.strip():
        append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] wrote /work/analysis.md")
    if final_md.strip():
        append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] wrote /work/final.md")

    return {
        "label": label,
        "analysis_md": analysis_md,
        "final_md": final_md,
        "failure_reason": None,
        "failure_detail": "",
        "llm_elapsed_s": invoke_elapsed_s,
        "llm_input_tokens": llm_input_tokens,
        "llm_output_tokens": llm_output_tokens,
        "llm_total_tokens": llm_total_tokens,
    }
