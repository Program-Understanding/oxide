"""Unbounded: whole-binary investigation of one bounded candidate.

Bounded reviews a candidate from its diff alone (plus any newly-added callees).
Unbounded takes that candidate's bounded report and re-investigates it with live
binary analysis tools over the whole target binary, loaded over MCP from
oxide_mcp_server.py. Each escalated candidate gets its own investigation; there
is no cross-candidate aggregation.
"""

import json
import os
import sys
import tempfile
import time
from typing import Any, Dict, Optional, Tuple

from deepagents.backends.utils import create_file_data

from oxide.modules.analyzers.delt_verification.pipeline.agents import deepagent_runtime
from oxide.modules.analyzers.delt_verification.pipeline.tools.binary_pair import (
    build_scoped_pair_tools,
)
from oxide.modules.analyzers.delt_verification.pipeline.agents.telemetry.agent_trace import (
    TraceLogger,
    append_trace_line,
)
from oxide.modules.analyzers.delt_verification.pipeline.agents.telemetry.token_usage import (
    collect_llm_usage_counts,
)
from oxide.modules.analyzers.delt_verification.pipeline.utils.resolve import resolve_mcp_server_path
from oxide.modules.analyzers.delt_verification.pipeline.utils.text_utils import (
    _coerce_label,
    _coerce_str,
    read_text,
)

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


class UnboundedDecisionSchema(BaseModel):
    # Optional so an omitted or misspelled label reaches the tool body and fails the run
    # by name. A schema rejection is handed back to the model as text instead, which is
    # how a call with no arguments used to end as a generic missing_final_answer.
    label: Optional[str] = Field(
        default=None,
        description='Final unbounded decision for this candidate. Must be exactly "safe" or "not_safe".',
    )


def _normalize_decision_payload(payload: Dict[str, Any]) -> Tuple[Optional[Dict[str, Any]], bool]:
    label = _coerce_label(payload.get("label"))
    if label not in {"safe", "not_safe"}:
        return None, False
    return {"label": label}, True


def _error_result(
    why: str,
    *,
    failure_reason: str,
    failure_detail: str = "",
    elapsed_s: float = 0.0,
    usage: Optional[Dict[str, int]] = None,
) -> Dict[str, Any]:
    usage = usage or {}
    return {
        "label": "failed",
        "summary": _coerce_str(why),
        "final_md": "",
        "failure_reason": failure_reason,
        "failure_detail": _coerce_str(failure_detail),
        "llm_elapsed_s": elapsed_s,
        "llm_input_tokens": int(usage.get("input_tokens") or 0),
        "llm_output_tokens": int(usage.get("output_tokens") or 0),
        "llm_total_tokens": int(usage.get("total_tokens") or 0),
    }


def _build_payload(
    prompt: str,
    report: str,
    *,
    candidate_manifest: Dict[str, Any],
    diff_text: str = "",
    callee_texts: Optional[Dict[str, str]] = None,
) -> Dict[str, Any]:
    files = {"/inputs/candidate.json": create_file_data(json.dumps(candidate_manifest, indent=2))}
    if report.strip():
        files["/inputs/report.md"] = create_file_data(report)
    if diff_text.strip():
        files["/inputs/diff.txt"] = create_file_data(diff_text)
    for addr, text in (callee_texts or {}).items():
        if text.strip():
            files[f"/inputs/added_functions/{addr}.c"] = create_file_data(text)
    return {
        "messages": [{"role": "user", "content": prompt}],
        "files": files,
    }


def _build_prompt(*, has_report: bool, has_diff: bool, has_callees: bool = False) -> str:
    evidence = []
    if has_report:
        evidence.append("the claim under /inputs/report.md")
    if has_diff:
        evidence.append("the diff under /inputs/diff.txt")
    if has_callees:
        evidence.append("the added functions under /inputs/added_functions/")
    evidence.append("the candidate manifest under /inputs/candidate.json")
    return (
        f"Review {', '.join(evidence)}, then use the binary analysis tools to verify "
        "independently whether this candidate is a backdoor.\n"
        "The tools are already scoped to this update pair. Refer to binaries only as "
        "'target' or 'baseline'; do not invent or request OIDs.\n"
        "Write your report to /work/final.md only if you decide not_safe, then call submit_decision.\n"
        'Example: submit_decision(label="not_safe")\n'
        "Call submit_decision to end the run.\n"
    )


def _select_system_prompt(runtime: Any, *, has_report: bool) -> str:
    """Pick the prompt whose evidence list matches the files the agent will actually get.

    The report is optional and naming an absent one sends the agent looking for a file that
    was never written, so there is one prompt for each case.
    """
    return runtime.unbounded_sys if has_report else runtime.unbounded_no_report_sys


def run_unbounded_agent(
    runtime: Any,
    report: str,
    *,
    candidate: Dict[str, Any],
    diff_text: str = "",
    callee_texts: Optional[Dict[str, str]] = None,
    trace_path: Optional[str] = None,
) -> Dict[str, Any]:
    """Investigate one escalated candidate with binary analysis tools; return its result dict."""
    request_timeout_s = runtime.unbounded_request_timeout_s
    prompt = _build_prompt(
        has_report=bool(report.strip()),
        has_diff=bool(diff_text.strip()),
        has_callees=bool(callee_texts),
    )

    file_mirror: Dict[str, str] = {}
    final_holder: Dict[str, Any] = {}
    candidate_manifest = {
        "binaries": {
            "target": {
                "role": "updated binary under investigation",
                "candidate_function_addr": _coerce_str(candidate.get("target_addr")),
            },
            "baseline": {
                "role": "trusted prior-version binary for comparison",
                "candidate_function_addr": _coerce_str(candidate.get("baseline_addr")),
            },
        },
    }
    decision_tool = deepagent_runtime.make_decision_tool(
        "submit_decision",
        UnboundedDecisionSchema,
        final_holder,
        _normalize_decision_payload,
        doc="Submit the final unbounded decision as your last action",
        precondition=deepagent_runtime.require_report_before_not_safe(file_mirror),
    )
    oxide_server_path = resolve_mcp_server_path()
    if not os.path.isfile(oxide_server_path):
        return _error_result(
            f"oxide_mcp_server.py not found at {oxide_server_path}",
            failure_reason="mcp_subprocess_failed",
        )
    oxide_root = os.path.dirname(oxide_server_path)

    if trace_path:
        stderr_path = os.path.join(os.path.dirname(os.path.abspath(trace_path)), "mcp_server.stderr.log")
        try:
            os.makedirs(os.path.dirname(stderr_path), exist_ok=True)
        except OSError:
            stderr_path = os.path.join(tempfile.gettempdir(), "oxide_mcp_server.stderr.log")
    else:
        stderr_path = os.path.join(tempfile.gettempdir(), "oxide_mcp_server.stderr.log")

    # Holds the agent output so a stdio teardown race -- BrokenResourceError raised
    # while the MCP session closes -- doesn't discard an already-finished investigation.
    holder: Dict[str, Any] = {}
    # Set once the MCP session is up and its tools are loaded. The server's stderr is
    # always non-empty (Oxide logs import warnings), so stderr content cannot be used to
    # tell a server crash from an agent-side failure -- this flag can.
    session_ready: Dict[str, bool] = {"ok": False}

    async def _run() -> Dict[str, Any]:
        from mcp import ClientSession, StdioServerParameters
        from mcp.client.stdio import stdio_client
        from langchain_mcp_adapters.tools import load_mcp_tools

        params = StdioServerParameters(
            command=sys.executable,
            args=[oxide_server_path, f"--oxidepath={oxide_root}"],
            cwd=oxide_root,
        )
        with open(stderr_path, "w", encoding="utf-8") as errlog:
            # One persistent ClientSession is deliberate: MultiServerMCPClient without
            # explicit session management opens a fresh session per tool call, which
            # re-imports Oxide every call and hides subprocess stderr.
            async with stdio_client(params, errlog=errlog) as (read, write):
                async with ClientSession(read, write) as session:
                    await session.initialize()
                    lc_tools = await load_mcp_tools(session)
                    scoped_tools = build_scoped_pair_tools(
                        mcp_tools=lc_tools,
                        target_oid=_coerce_str(candidate.get("target_oid")),
                        baseline_oid=_coerce_str(candidate.get("baseline_oid")),
                    )
                    session_ready["ok"] = True
                    agent = deepagent_runtime.build_bounded_agent(
                        main_model=runtime.unbounded_llm,
                        file_mirror=file_mirror,
                        decision_tool=decision_tool,
                        system_prompt=_select_system_prompt(
                            runtime, has_report=bool(report.strip())
                        ),
                        final_holder=final_holder,
                        extra_tools=scoped_tools,
                        agent_name="delt_verification_unbounded_agent",
                    )
                    trace_logger = TraceLogger(trace_path)
                    append_trace_line(trace_path, "[   0.00s] [agent] start", truncate=True)
                    append_trace_line(
                        trace_path,
                        f"[   0.00s] [agent] scoped tools: {len(scoped_tools)} | run budget "
                        f"{request_timeout_s:g}s, model call "
                        f"{runtime.unbounded_model_call_timeout_s:g}s",
                    )
                    payload = _build_payload(
                        prompt,
                        report,
                        candidate_manifest=candidate_manifest,
                        callee_texts=callee_texts,
                        diff_text=diff_text,
                    )
                    holder["out"] = await deepagent_runtime.ainvoke_agent_with_timeout(
                        agent,
                        payload,
                        config={},
                        timeout_s=request_timeout_s,
                        trace_logger=trace_logger,
                    )
                    return holder["out"]

    invoke_t0 = time.perf_counter()
    try:
        out = deepagent_runtime.get_async_runner().run(_run())
    except BaseException as exc:  # noqa: BLE001 -- surface subprocess/teardown failures cleanly
        invoke_elapsed_s = time.perf_counter() - invoke_t0
        if "out" in holder:
            # The agent finished and the exception came from session teardown. Keep the
            # completed investigation rather than throwing away a real verdict.
            append_trace_line(
                trace_path,
                f"[{invoke_elapsed_s:7.2f}s] [agent] mcp teardown raised after completion; keeping result",
            )
            out = holder["out"]
        else:
            if not session_ready["ok"]:
                # Never got a usable MCP session, so the server itself is the suspect.
                detail = read_text(stderr_path, tail_chars=4000) or repr(exc)
                failure_reason, why = "mcp_subprocess_failed", (
                    "The unbounded MCP server subprocess failed before the investigation could run. "
                    f"Interpreter: {sys.executable}. Server stderr captured at {stderr_path}."
                )
            else:
                detail = repr(exc)
                failure_reason, why = deepagent_runtime.classify_agent_failure(
                    exc,
                    request_timeout_s=request_timeout_s,
                    model_call_timeout_s=runtime.unbounded_model_call_timeout_s,
                )
            append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] error: {failure_reason}")
            return _error_result(
                why,
                failure_reason=failure_reason,
                failure_detail=detail,
                elapsed_s=invoke_elapsed_s,
                usage=collect_llm_usage_counts(deepagent_runtime.partial_messages(exc)),
            )
    invoke_elapsed_s = time.perf_counter() - invoke_t0

    final_md = _coerce_str(file_mirror.get("/work/final.md"))
    messages = deepagent_runtime.agent_messages(out)
    usage = collect_llm_usage_counts(messages)
    final = final_holder.get("final")

    if not isinstance(final, dict) or final.get("label") not in {"safe", "not_safe"}:
        append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] error: missing_final_answer")
        result = _error_result(
            "The unbounded agent did not call submit_decision before the run ended.",
            failure_reason="missing_final_answer",
            elapsed_s=invoke_elapsed_s,
            usage=usage,
        )
        result["final_md"] = final_md
        return result

    label = _coerce_label(final.get("label"))
    append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] final: label={label}")

    if label == "not_safe" and not final_md.strip():
        append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] error: missing_final_md")
        return _error_result(
            "The unbounded agent labeled the candidate not_safe but did not write /work/final.md.",
            failure_reason="missing_final_md",
            elapsed_s=invoke_elapsed_s,
            usage=usage,
        )
    if final_md.strip():
        append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] wrote /work/final.md")

    summary = "Unbounded decision completed."
    if final_md.strip():
        summary = final_md.splitlines()[0].strip() or summary

    return {
        "label": label,
        "summary": summary,
        "final_md": final_md,
        "failure_reason": None,
        "failure_detail": "",
        "llm_elapsed_s": invoke_elapsed_s,
        "llm_input_tokens": int(usage.get("input_tokens") or 0),
        "llm_output_tokens": int(usage.get("output_tokens") or 0),
        "llm_total_tokens": int(usage.get("total_tokens") or 0),
    }
