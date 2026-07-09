"""Stage 3: per-function binary-aware investigation using MCP-backed oxide tools.

Escalated to only when Stage 1+2's combined verdict is not_safe -- this stage
gets a real oxide MCP server subprocess (see agent/mcp_client.py) so the agent
can query the binary directly (decompile callees, follow xrefs, etc.) instead
of reasoning from the diff text alone.
"""

import json
import logging
import time
from typing import Any, Dict, List, Literal, Optional, Tuple

from oxide.modules.analyzers.backdoor_triage.config import NAME
from oxide.modules.analyzers.backdoor_triage.pipeline.types import TriageState
from oxide.modules.analyzers.backdoor_triage.pipeline.agent import agent_runtime, mcp_client
from oxide.modules.analyzers.backdoor_triage.pipeline.agent.telemetry.agent_trace import TraceLogger, append_trace_line
from oxide.modules.analyzers.backdoor_triage.pipeline.utils.text_utils import _coerce_str, progress_label as _progress_label_fmt
from oxide.modules.analyzers.backdoor_triage.pipeline.agent.telemetry.token_usage import collect_llm_usage_counts

try:
    from deepagents.backends.utils import create_file_data
except ImportError:  # pragma: no cover
    create_file_data = None

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


class Stage3DecisionSchema(BaseModel):
    overall: Literal["safe", "backdoor"] = Field(
        description="Final investigation verdict for this candidate function.",
    )


def _normalize_stage3_payload(payload: Dict[str, Any]) -> Tuple[Optional[Dict[str, Any]], bool]:
    overall = _coerce_str(payload.get("overall")).lower()
    if overall not in {"safe", "backdoor"}:
        return None, False
    return {"overall": overall}, True


def _failed_result(why: str, *, failure_reason: str, failure_detail: str = "") -> Dict[str, Any]:
    # Infrastructure failure (timeout, crash, missing verdict) -- NOT a model
    # decision. Kept distinct from the binary backdoor/safe verdict so a failed
    # run is never silently counted as "safe".
    return {
        "overall": "error",
        "confirmed_functions": [],
        "why": _coerce_str(why),
        "analysis_md": "",
        "final_md": "",
        "failure_reason": failure_reason,
        "failure_detail": _coerce_str(failure_detail),
        "elapsed_s": 0.0,
        "llm_input_tokens": 0,
        "llm_output_tokens": 0,
        "llm_total_tokens": 0,
    }


def _run_stage3_investigation(
    runtime: Any,
    *,
    diff_text: str,
    stage2_final_md: str,
    target_oid: str,
    baseline_oid: str,
    target_addr: str,
    baseline_addr: str,
    trigger_hint: str,
    stage1_label: str,
    notes: Dict[str, Any],
    trace_path: Optional[str],
    progress_label: str = "",
) -> Dict[str, Any]:
    """ Run the Stage 3 investigator inside a fresh MCP tool session. This is a
        plain sync entry point -- mcp_client.run_with_mcp_tools owns the event
        loop (via its own asyncio.Runner) and awaits the async run_agent closure
        defined below inside that loop; this function itself must not be async,
        or calling it would try to nest a second event loop inside the first.
    """
    candidate_manifest = {
        "target_oid": target_oid,
        "baseline_oid": baseline_oid,
        "target_addr": target_addr,
        "baseline_addr": baseline_addr,
        "trigger_hint": trigger_hint,
        "stage1_label": stage1_label,
    }
    files: Dict[str, Any] = {
        "/inputs/candidate.json": create_file_data(json.dumps(candidate_manifest, indent=2)),
        "/inputs/diff.txt": create_file_data(diff_text or ""),
    }
    if stage2_final_md.strip():
        files["/inputs/final.md"] = create_file_data(stage2_final_md)

    prompt = (
        "Investigate the candidate function described in /inputs/candidate.json.\n"
        f"Target binary OID: {target_oid}\n"
        f"Baseline binary OID: {baseline_oid}\n"
        f"Target function address: {target_addr}\n"
        "Review this one function, use binary analysis tools as needed, write notes to /work/analysis.md, "
        "write the final security report to /work/final.md, then call submit_stage3_decision.\n"
        "/work/final.md alone is not the final answer.\n"
        "LAST STEP: call submit_stage3_decision.\n"
        'Example final action: submit_stage3_decision(overall="backdoor")\n'
        "Do not write another explanatory assistant message after /work/final.md.\n"
        "The run is not complete until submit_stage3_decision succeeds.\n"
    )

    async def run_agent(tools: List[Any]) -> Dict[str, Any]:
        file_mirror: Dict[str, str] = {}
        final_holder: Dict[str, Any] = {}
        decision_tool = agent_runtime.make_decision_tool(
            "submit_stage3_decision",
            Stage3DecisionSchema,
            final_holder,
            _normalize_stage3_payload,
            doc="Submit the final Stage 3 investigation verdict after writing /work/final.md.",
        )
        agent = agent_runtime.build_triage_agent(
            main_model=runtime.stage3_llm,
            file_mirror=file_mirror,
            decision_tool=decision_tool,
            system_prompt=runtime.stage3_sys,
            extra_tools=tools,
            agent_name="backdoor_triage_stage3",
        )

        started_at = time.perf_counter()
        payload = {"messages": [{"role": "user", "content": prompt}], "files": files}
        config = {"configurable": {"thread_id": f"backdoor_triage_stage3_{time.time_ns()}"}}
        trace_logger = TraceLogger(trace_path)

        logger.info("%s stage3 start diff=%d chars tools=%d", progress_label, len(diff_text), len(tools))
        try:
            append_trace_line(trace_path, "[   0.00s] [stage3] start", truncate=True)
            out = await agent_runtime.ainvoke_agent_with_timeout(
                agent, payload, config=config,
                timeout_s=float(getattr(runtime, "stage3_request_timeout_s", 3600.0)),
                trace_logger=trace_logger,
                max_consecutive_repeated_tool_calls=int(
                    getattr(runtime, "stage3_max_repeated_tool_calls", agent_runtime.DEFAULT_MAX_CONSECUTIVE_REPEATED_TOOL_CALLS)
                ),
            )
        except TimeoutError as exc:
            elapsed = time.perf_counter() - started_at
            notes["observations"].append(f"Stage 3 timed out: {exc}.")
            append_trace_line(trace_path, f"[{elapsed:7.2f}s] [stage3] error: timeout {exc}")
            r = _failed_result(f"Stage 3 timed out after {elapsed:g}s.", failure_reason="timeout", failure_detail=str(exc))
            r["elapsed_s"] = elapsed
            return r
        except agent_runtime.RepeatedToolCallError as exc:
            elapsed = time.perf_counter() - started_at
            notes["observations"].append(f"Stage 3 repeated tool call: {exc}")
            append_trace_line(trace_path, f"[{elapsed:7.2f}s] [stage3] error: repeated_tool_call {exc}")
            r = _failed_result(str(exc), failure_reason="repeated_tool_call")
            r["elapsed_s"] = elapsed
            return r
        except Exception as exc:
            elapsed = time.perf_counter() - started_at
            notes["observations"].append(f"Stage 3 invoke failed: {exc}.")
            append_trace_line(trace_path, f"[{elapsed:7.2f}s] [stage3] error: invoke_failed {exc}")
            r = _failed_result(str(exc), failure_reason="invoke_failed", failure_detail=str(exc))
            r["elapsed_s"] = elapsed
            return r

        # Rescue: if the model ended its turn with prose but no submit call,
        # continue the same thread with a direct re-prompt once.
        if not final_holder.get("final"):
            elapsed_now = time.perf_counter() - started_at
            remaining = float(getattr(runtime, "stage3_request_timeout_s", 3600.0)) - elapsed_now
            if remaining > 30:
                rescue_msg = (
                    "Write /work/final.md now (the full security report), "
                    "then immediately call submit_stage3_decision. "
                    "Do not write any more analysis -- write the report and call the tool now."
                )
                append_trace_line(trace_path, f"[{elapsed_now:7.2f}s] [stage3] rescue: no submit detected -- re-prompting")
                try:
                    out = await agent_runtime.ainvoke_agent_with_timeout(
                        agent,
                        {"messages": [{"role": "user", "content": rescue_msg}]},
                        config=config, timeout_s=min(180.0, remaining), trace_logger=trace_logger,
                        max_consecutive_repeated_tool_calls=int(
                            getattr(runtime, "stage3_max_repeated_tool_calls", agent_runtime.DEFAULT_MAX_CONSECUTIVE_REPEATED_TOOL_CALLS)
                        ),
                    )
                except TimeoutError:
                    append_trace_line(trace_path, f"[{time.perf_counter() - started_at:7.2f}s] [stage3] rescue timeout")
                except agent_runtime.RepeatedToolCallError as exc:
                    elapsed = time.perf_counter() - started_at
                    append_trace_line(trace_path, f"[{elapsed:7.2f}s] [stage3] rescue error: repeated_tool_call {exc}")
                    r = _failed_result(str(exc), failure_reason="repeated_tool_call")
                    r["elapsed_s"] = elapsed
                    return r
                except Exception as exc:
                    append_trace_line(trace_path, f"[{time.perf_counter() - started_at:7.2f}s] [stage3] rescue error: {exc}")

        elapsed = time.perf_counter() - started_at
        analysis_md = _coerce_str(file_mirror.get("/work/analysis.md"))
        final_md = _coerce_str(file_mirror.get("/work/final.md"))
        messages = out.get("messages") if isinstance(out, dict) else getattr(out, "messages", None)
        llm_usage = collect_llm_usage_counts(messages)

        final = final_holder.get("final")
        if not isinstance(final, dict) or final.get("overall") not in {"safe", "backdoor"}:
            why = "Stage 3 did not call submit_stage3_decision before the run ended."
            notes["observations"].append(why)
            append_trace_line(trace_path, f"[{elapsed:7.2f}s] [stage3] error: missing_verdict")
            r = _failed_result(why, failure_reason="missing_verdict")
            r["elapsed_s"] = elapsed
            r["analysis_md"] = analysis_md
            r["final_md"] = final_md
            r["llm_input_tokens"] = int(llm_usage.get("input_tokens") or 0)
            r["llm_output_tokens"] = int(llm_usage.get("output_tokens") or 0)
            r["llm_total_tokens"] = int(llm_usage.get("total_tokens") or 0)
            return r

        overall = final["overall"]
        append_trace_line(trace_path, f"[{elapsed:7.2f}s] [stage3] final: overall={overall}")
        return {
            "overall": overall,
            "confirmed_functions": [target_addr] if overall == "backdoor" else [],
            "analysis_md": analysis_md,
            "final_md": final_md,
            "failure_reason": None,
            "failure_detail": "",
            "elapsed_s": elapsed,
            "llm_input_tokens": int(llm_usage.get("input_tokens") or 0),
            "llm_output_tokens": int(llm_usage.get("output_tokens") or 0),
            "llm_total_tokens": int(llm_usage.get("total_tokens") or 0),
        }

    try:
        return mcp_client.run_with_mcp_tools(run_agent, trace_path=trace_path)
    except Exception as exc:
        notes["observations"].append(f"Stage 3 MCP session failed: {exc}")
        r = _failed_result(str(exc), failure_reason="mcp_subprocess_failed", failure_detail=str(exc))
        return r


def build_stage3_node(runtime: Any):
    def _stage3_node(state: TriageState) -> Dict[str, Any]:
        progress_label = _progress_label_fmt(
            fp_idx=state["fp_idx"], fp_total=state.get("fp_total", 0),
            func_idx=state["func_idx"], func_total=state.get("func_total", 0),
        )
        stage1_json = state.get("stage1_json") or {}
        stage2_result = state.get("stage2_result") or {}
        result = _run_stage3_investigation(
            runtime,
            diff_text=state["diff"],
            stage2_final_md=_coerce_str(stage2_result.get("final_md")),
            target_oid=state.get("target_oid", ""),
            baseline_oid=state.get("baseline_oid", ""),
            target_addr=state.get("target_addr", ""),
            baseline_addr=state.get("baseline_addr", ""),
            trigger_hint=stage1_json.get("trigger", ""),
            stage1_label=stage1_json.get("label", "not_safe"),
            notes=state["notes"],
            trace_path=state.get("trace_path"),
            progress_label=progress_label,
        )
        return {"stage3_result": result}

    return _stage3_node
