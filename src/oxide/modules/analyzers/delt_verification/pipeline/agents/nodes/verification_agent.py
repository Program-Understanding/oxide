"""Verification: whole-binary investigation of one triage candidate.

Triage reviews a candidate from its diff alone (plus any newly-added callees).
Verification takes that candidate's triage report and re-investigates it with live
binary analysis tools over the whole target binary, loaded over MCP from
oxide_mcp_server.py. Each escalated candidate gets its own investigation; there
is no cross-candidate aggregation.
"""

import json
import os
import sys
import tempfile
import time
from typing import Any, Dict, Literal, Optional, Tuple

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
from oxide.modules.analyzers.delt_verification.pipeline.utils.text_utils import _coerce_label, _coerce_str

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


class VerificationDecisionSchema(BaseModel):
    label: Literal["safe", "not_safe"] = Field(
        description="Final verification decision for this candidate. Must be safe or not_safe.",
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
    binary_context_md: str = "",
    diff_text: str = "",
) -> Dict[str, Any]:
    files = {"/inputs/candidate.json": create_file_data(json.dumps(candidate_manifest, indent=2))}
    if binary_context_md.strip():
        files["/inputs/binary_context.md"] = create_file_data(binary_context_md)
    if report.strip():
        files["/inputs/report.md"] = create_file_data(report)
    if diff_text.strip():
        files["/inputs/diff.txt"] = create_file_data(diff_text)
    return {
        "messages": [{"role": "user", "content": prompt}],
        "files": files,
    }


def _build_prompt(*, has_report: bool, has_diff: bool, has_binary_context: bool) -> str:
    evidence = []
    if has_binary_context:
        evidence.append("the binary context under /inputs/binary_context.md")
    if has_report:
        evidence.append("the claim under /inputs/report.md")
    if has_diff:
        evidence.append("the diff under /inputs/diff.txt")
    evidence.append("the candidate manifest under /inputs/candidate.json")
    return (
        f"Review {', '.join(evidence)}, then use the binary analysis tools to verify "
        "independently whether this candidate is a backdoor.\n"
        "The tools are already scoped to this update pair. Refer to binaries only as "
        "'target' or 'baseline'; do not invent or request OIDs.\n"
        "Write your report to /work/final.md only if you decide not_safe, then call submit_decision.\n"
        'Example: submit_decision(label="not_safe")\n'
        "The run is not complete until you call submit_decision.\n"
    )


def _read_tail(path: str, max_chars: int = 4000) -> str:
    try:
        with open(path, encoding="utf-8", errors="replace") as fh:
            text = fh.read()
    except OSError:
        return ""
    text = text.strip()
    return text[-max_chars:] if len(text) > max_chars else text


def run_verification_agent(
    runtime: Any,
    report: str,
    *,
    candidate: Dict[str, Any],
    binary_context_md: str = "",
    diff_text: str = "",
    trace_path: Optional[str] = None,
) -> Dict[str, Any]:
    """Investigate one escalated candidate with binary analysis tools; return its result dict."""
    request_timeout_s = float(
        getattr(runtime, "verification_request_timeout_s", None)
        or getattr(runtime, "triage_request_timeout_s", 600.0)
    )
    prompt = _build_prompt(
        has_binary_context=bool(binary_context_md.strip()),
        has_report=bool(report.strip()),
        has_diff=bool(diff_text.strip()),
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
        VerificationDecisionSchema,
        final_holder,
        _normalize_decision_payload,
        doc="Submit the final verification decision as your last action",
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
                    agent = deepagent_runtime.build_triage_agent(
                        main_model=getattr(runtime, "verification_llm", None) or runtime.triage_llm,
                        file_mirror=file_mirror,
                        decision_tool=decision_tool,
                        system_prompt=runtime.verification_sys,
                        extra_tools=scoped_tools,
                        agent_name="delt_verification_verification_agent",
                    )
                    trace_logger = TraceLogger(trace_path)
                    append_trace_line(trace_path, "[   0.00s] [agent] start", truncate=True)
                    append_trace_line(
                        trace_path,
                        f"[   0.00s] [agent] scoped tools: {len(scoped_tools)} | run budget "
                        f"{request_timeout_s:g}s, model call "
                        f"{getattr(runtime, 'verification_model_call_timeout_s', 0.0):g}s",
                    )
                    config = {"configurable": {"thread_id": f"delt_verification_verification_{time.time_ns()}"}}
                    payload = _build_payload(
                        prompt,
                        report,
                        candidate_manifest=candidate_manifest,
                        binary_context_md=binary_context_md,
                        diff_text=diff_text,
                    )
                    holder["out"] = await deepagent_runtime.ainvoke_agent_with_timeout(
                        agent,
                        payload,
                        config=config,
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
        elif not session_ready["ok"]:
            # Never got a usable MCP session, so the server itself is the suspect.
            detail = _read_tail(stderr_path) or repr(exc)
            failure_reason, why = "mcp_subprocess_failed", (
                "The verification MCP server subprocess failed before the investigation could run. "
                f"Interpreter: {sys.executable}. Server stderr captured at {stderr_path}."
            )
        else:
            # Session was up, so this is an agent-side failure. ChatOllama surfaces a
            # per-request timeout as an httpx error, not TimeoutError, so match on text too.
            detail = repr(exc)
            if deepagent_runtime.is_repeated_tool_call_error(exc):
                failure_reason, why = "repeated_tool_call", str(exc)
            elif deepagent_runtime.is_malformed_model_response_error(exc):
                failure_reason, why = "malformed_model_response", (
                    "The model emitted a response the provider could not parse, so verification "
                    "stopped before reaching a final decision."
                )
            elif isinstance(exc, TimeoutError) or "timeout" in detail.lower():
                failure_reason, why = "timeout", (
                    f"Verification timed out after {request_timeout_s:g}s before reaching a final decision."
                )
            else:
                failure_reason, why = "invoke_failed", "Verification failed before reaching a final decision."
        if "out" not in holder:
            append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] error: {failure_reason}")
            return _error_result(
                why,
                failure_reason=failure_reason,
                failure_detail=detail,
                elapsed_s=invoke_elapsed_s,
            )
    invoke_elapsed_s = time.perf_counter() - invoke_t0

    final_md = _coerce_str(file_mirror.get("/work/final.md"))
    messages = out.get("messages") if isinstance(out, dict) else getattr(out, "messages", None)
    usage = collect_llm_usage_counts(messages)
    final = final_holder.get("final")

    if not isinstance(final, dict) or final.get("label") not in {"safe", "not_safe"}:
        append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] error: missing_final_answer")
        result = _error_result(
            "The verification agent did not call submit_decision before the run ended.",
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
            "The verification agent labeled the candidate not_safe but did not write /work/final.md.",
            failure_reason="missing_final_md",
            elapsed_s=invoke_elapsed_s,
            usage=usage,
        )
    if final_md.strip():
        append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] wrote /work/final.md")

    summary = "Verification decision completed."
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
