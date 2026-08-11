"""Single-binary context generation agent."""

import json
import os
import sys
import tempfile
import time
from typing import Any, Dict, Literal, Optional, Tuple

from deepagents.backends.utils import create_file_data

from oxide.modules.analyzers.delt_verification.pipeline.agents import deepagent_runtime
from oxide.modules.analyzers.delt_verification.pipeline.tools.single_binary import (
    build_binary_context_tools,
)
from oxide.modules.analyzers.delt_verification.pipeline.agents.telemetry.agent_trace import (
    TraceLogger,
    append_trace_line,
)
from oxide.modules.analyzers.delt_verification.pipeline.agents.telemetry.token_usage import (
    collect_llm_usage_counts,
)
from oxide.modules.analyzers.delt_verification.pipeline.utils.resolve import resolve_mcp_server_path
from oxide.modules.analyzers.delt_verification.pipeline.utils.text_utils import _coerce_str

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


class BinaryContextDecisionSchema(BaseModel):
    status: Literal["complete"] = Field(
        description="Call this only after writing /work/binary_context.md",
    )


def _normalize_binary_context_payload(payload: Dict[str, Any]) -> Tuple[Optional[Dict[str, Any]], bool]:
    status = _coerce_str(payload.get("status")).strip().lower()
    if status != "complete":
        return None, False
    return {"status": "complete"}, True


def _binary_context_precondition(file_mirror: Dict[str, str]) -> Any:
    def _check(_final: Dict[str, Any]) -> Optional[str]:
        md_text = _coerce_str(file_mirror.get("/work/binary_context.md"))
        if not md_text.strip():
            return "Rejected: write /work/binary_context.md before submitting."
        return None

    return _check


def _build_payload(prompt: str, binary_manifest: Dict[str, Any]) -> Dict[str, Any]:
    return {
        "messages": [{"role": "user", "content": prompt}],
        "files": {"/inputs/binary.json": create_file_data(json.dumps(binary_manifest, indent=2))},
    }


def run_binary_context_agent(
    runtime: Any,
    *,
    binary_oid: str,
    trace_path: Optional[str] = None,
) -> Dict[str, Any]:
    request_timeout_s = float(
        getattr(runtime, "binary_context_request_timeout_s", None)
        or getattr(runtime, "triage_request_timeout_s", 450.0)
    )
    prompt = (
        "Investigate the binary described in /inputs/binary.json. "
        "Build a concise binary context report, write /work/binary_context.md, then call "
        "submit_context(status=\"complete\")."
    )

    file_mirror: Dict[str, str] = {}
    final_holder: Dict[str, Any] = {}
    decision_tool = deepagent_runtime.make_decision_tool(
        "submit_context",
        BinaryContextDecisionSchema,
        final_holder,
        _normalize_binary_context_payload,
        doc="Submit when the binary context artifact is complete",
        precondition=_binary_context_precondition(file_mirror),
    )
    oxide_server_path = resolve_mcp_server_path()
    if not os.path.isfile(oxide_server_path):
        return {
            "status": "failed",
            "failure_reason": "mcp_subprocess_failed",
            "failure_detail": f"oxide_mcp_server.py not found at {oxide_server_path}",
            "llm_elapsed_s": 0.0,
            "llm_input_tokens": 0,
            "llm_output_tokens": 0,
            "llm_total_tokens": 0,
            "binary_context_md": "",
        }
    oxide_root = os.path.dirname(oxide_server_path)
    stderr_path = (
        os.path.join(os.path.dirname(os.path.abspath(trace_path)), "mcp_server.stderr.log")
        if trace_path
        else os.path.join(tempfile.gettempdir(), "oxide_mcp_server.stderr.log")
    )

    holder: Dict[str, Any] = {}
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
            async with stdio_client(params, errlog=errlog) as (read, write):
                async with ClientSession(read, write) as session:
                    await session.initialize()
                    lc_tools = await load_mcp_tools(session)
                    scoped_tools = build_binary_context_tools(
                        mcp_tools=lc_tools,
                        binary_oid=binary_oid,
                    )
                    session_ready["ok"] = True
                    agent = deepagent_runtime.build_triage_agent(
                        main_model=getattr(runtime, "binary_context_llm", None) or runtime.triage_llm,
                        file_mirror=file_mirror,
                        decision_tool=decision_tool,
                        system_prompt=runtime.binary_context_sys,
                        extra_tools=scoped_tools,
                        agent_name="delt_verification_binary_context_agent",
                    )
                    trace_logger = TraceLogger(trace_path)
                    append_trace_line(trace_path, "[   0.00s] [agent] start", truncate=True)
                    append_trace_line(
                        trace_path,
                        f"[   0.00s] [agent] single-binary scoped tools: {len(scoped_tools)} | run budget "
                        f"{request_timeout_s:g}s, model call "
                        f"{getattr(runtime, 'binary_context_model_call_timeout_s', 0.0):g}s",
                    )
                    config = {"configurable": {"thread_id": f"delt_verification_binary_context_{time.time_ns()}"}}
                    payload = _build_payload(
                        prompt,
                        {"binary": {"oid": _coerce_str(binary_oid)}},
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
    except BaseException as exc:  # noqa: BLE001
        elapsed = time.perf_counter() - invoke_t0
        if "out" in holder:
            out = holder["out"]
        else:
            partial_messages = None
            if not session_ready["ok"]:
                failure_reason = "mcp_subprocess_failed"
            elif deepagent_runtime.is_repeated_tool_call_error(exc):
                failure_reason = "repeated_tool_call"
            elif deepagent_runtime.is_malformed_model_response_error(exc):
                failure_reason = "malformed_model_response"
                partial_messages = getattr(exc, "partial", {}).get("messages")
            elif isinstance(exc, TimeoutError) or "timeout" in repr(exc).lower():
                failure_reason = "timeout"
            else:
                failure_reason = "invoke_failed"
            # The agent is told to write its draft early and refine it, so a run that
            # times out or gets cut off mid-investigation usually still has a usable
            # report in the mirror. Salvage it rather than discarding the whole run.
            salvaged = _coerce_str(file_mirror.get("/work/binary_context.md"))
            # A run cut short still burned tokens, so count what it accumulated
            # where the error carries it rather than reporting a spurious zero.
            partial_usage = collect_llm_usage_counts(partial_messages) if partial_messages else {}
            return {
                "status": "partial" if salvaged.strip() else "failed",
                "failure_reason": failure_reason,
                "failure_detail": repr(exc),
                "llm_elapsed_s": elapsed,
                "llm_input_tokens": int(partial_usage.get("input_tokens") or 0),
                "llm_output_tokens": int(partial_usage.get("output_tokens") or 0),
                "llm_total_tokens": int(partial_usage.get("total_tokens") or 0),
                "binary_context_md": salvaged,
            }
    elapsed = time.perf_counter() - invoke_t0
    messages = out.get("messages") if isinstance(out, dict) else getattr(out, "messages", None)
    usage = collect_llm_usage_counts(messages)
    md_text = _coerce_str(file_mirror.get("/work/binary_context.md"))
    return {
        "status": "complete" if final_holder.get("final", {}).get("status") == "complete" else "failed",
        "failure_reason": None,
        "failure_detail": "",
        "llm_elapsed_s": elapsed,
        "llm_input_tokens": int(usage.get("input_tokens") or 0),
        "llm_output_tokens": int(usage.get("output_tokens") or 0),
        "llm_total_tokens": int(usage.get("total_tokens") or 0),
        "binary_context_md": md_text,
    }
