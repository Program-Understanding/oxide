"""Isolated deepagents construction and invocation surface.

Validated against: deepagents==0.6.10, langgraph==1.2.5, langchain-ollama==1.1.0.
If a future upstream release breaks GuardedStateBackend's constructor contract,
create_deep_agent's kwargs, or agent.astream's stream_mode/version behavior,
this file is the single, obvious place to fix it. graph.py builds the outer
triage StateGraph using the stable, public langgraph.graph API (StateGraph,
START, END, MemorySaver) -- that is not the fragile surface isolated here;
this file owns everything deepagents-specific (create_deep_agent, the custom
StateBackend, and driving agent.astream).
"""

import asyncio
import atexit
import json
import time
from typing import Any, Callable, Dict, Optional, Tuple

from deepagents import create_deep_agent
from deepagents.backends import StateBackend
from deepagents.backends.protocol import EditResult, WriteResult
from deepagents.backends.utils import create_file_data
from langchain_ollama import ChatOllama
from langgraph.checkpoint.memory import MemorySaver
from langchain_core.tools import tool

_ASYNC_RUNNER: Optional[asyncio.Runner] = None

DEFAULT_MAX_CONSECUTIVE_REPEATED_TOOL_CALLS = 10


class RepeatedToolCallError(Exception):
    """Raised when the agent calls the same tool with identical arguments too many times in a row."""


class GuardedStateBackend(StateBackend):
    """Block modifications to seeded input files and mirror writes to local state."""

    def __init__(self, mirror: Optional[Dict[str, str]] = None) -> None:
        super().__init__()
        self._mirror = mirror if isinstance(mirror, dict) else None

    def write(self, file_path: str, content: str) -> WriteResult:
        if file_path.startswith("/inputs/"):
            return WriteResult(error="Read-only: /inputs/")
        result = super().write(file_path, content)
        if not getattr(result, "error", None) and self._mirror is not None:
            self._mirror[file_path] = content
        return result

    def edit(self, file_path: str, *args: Any, **kwargs: Any) -> EditResult:
        if file_path.startswith("/inputs/"):
            return EditResult(error="Read-only: /inputs/")
        return super().edit(file_path, *args, **kwargs)


def make_decision_tool(
    tool_name: str,
    schema_cls: type,
    final_holder: Dict[str, Any],
    normalize: Callable[[Dict[str, Any]], Tuple[Optional[Dict[str, Any]], bool]],
    *,
    doc: str,
) -> Any:
    """ Build a single-shot deepagents tool: validates its arguments via normalize()
        (which should return (payload, ok)), raising if invalid, and records the
        normalized payload into final_holder["final"] so the caller can read it
        back after the agent run completes. Each stage owns its own schema/normalize
        function -- this factory just wires the common "validate, record, confirm"
        pattern once instead of duplicating it per stage.
    """

    @tool(tool_name, args_schema=schema_cls, description=doc)
    def _submit(**kwargs: Any) -> str:
        final, ok = normalize(kwargs)
        if not ok or final is None:
            raise ValueError(f"invalid arguments for {tool_name}: {kwargs!r}")
        final_holder["final"] = final
        return f"recorded {final}"

    return _submit


def make_agent_model(model: str, *, request_timeout_s: float) -> ChatOllama:
    kwargs: Dict[str, Any] = {
        "model": model,
        "temperature": 0.0,
        "keep_alive": "10m",
        "profile": {"max_input_tokens": 262144},
    }
    if request_timeout_s > 0:
        kwargs["client_kwargs"] = {"timeout": request_timeout_s}
    return ChatOllama(**kwargs)


def build_triage_agent(
    *,
    main_model: ChatOllama,
    file_mirror: Dict[str, str],
    decision_tool: Any,
    system_prompt: str,
    extra_tools: Optional[list] = None,
    agent_name: str = "backdoor_triage_agent",
) -> Any:
    """ Build a deepagents agent sandboxed to file_mirror, with decision_tool (this
        stage's own submit-decision tool, from make_decision_tool) plus any
        extra_tools (e.g. MCP-backed binary-analysis tools for Stage 3).
    """
    return create_deep_agent(
        model=main_model,
        tools=[decision_tool] + list(extra_tools or []),
        system_prompt=system_prompt,
        checkpointer=MemorySaver(),
        subagents=[],
        backend=GuardedStateBackend(mirror=file_mirror),
        debug=False,
        name=agent_name,
    )


def build_agent_payload(diff_text: str, prompt: str, callee_texts: Optional[Dict[str, str]] = None) -> Dict[str, Any]:
    files: Dict[str, Any] = {"/inputs/unified_diff.txt": create_file_data(diff_text)}
    for addr, text in (callee_texts or {}).items():
        if text.strip():
            files[f"/inputs/added_functions/{addr}.c"] = create_file_data(text)
    return {
        "messages": [{"role": "user", "content": prompt}],
        "files": files,
    }


async def _stream_agent_core(
    agent: Any,
    payload: Dict[str, Any],
    *,
    config: Dict[str, Any],
    timeout_s: float,
    trace_logger: Any = None,
    max_consecutive_repeated_tool_calls: int = DEFAULT_MAX_CONSECUTIVE_REPEATED_TOOL_CALLS,
) -> Any:
    """ Stream the agent to completion and return an object exposing .messages
        accumulated from "updates" events.

        trace_logger, if given, is a duck-typed object (see agent_trace.TraceLogger)
        with on_chunk(chunk, elapsed_s) called per stream item and flush(elapsed_s)
        called once after the stream ends, forcing out any buffered trace text.

        Raises RepeatedToolCallError if the same tool is called with identical
        arguments max_consecutive_repeated_tool_calls times in a row -- a stuck
        agent should fail fast rather than burn the whole timeout looping.

        This is a plain coroutine (no event-loop management of its own) so it can
        be awaited either from a fresh asyncio.Runner (invoke_agent_with_timeout,
        for Stage 1/2 called from sync code) or from within an already-running
        loop (ainvoke_agent_with_timeout, for Stage 3, which must share its event
        loop with the MCP client session its tools are bound to).
    """
    started_at = time.perf_counter()

    async def _stream_then_collect_state() -> Any:
        accumulated: Dict[str, Any] = {"messages": []}
        last_tool_call_fp: Optional[str] = None
        repeated_tool_call_count = 0

        async for item in agent.astream(
            payload,
            config=config,
            stream_mode=["updates", "messages", "tasks"],
            subgraphs=True,
            version="v2",
        ):
            elapsed_s = time.perf_counter() - started_at
            if trace_logger is not None:
                from oxide.modules.analyzers.backdoor_triage.pipeline.agent.telemetry.agent_trace import normalize_stream_item

                chunk = normalize_stream_item(item)
                trace_logger.on_chunk(chunk, elapsed_s)
                if chunk.get("type") == "updates":
                    data = chunk.get("data")
                    if isinstance(data, dict):
                        for node_update in data.values():
                            if not isinstance(node_update, dict):
                                continue
                            msgs = node_update.get("messages")
                            if isinstance(msgs, list):
                                accumulated["messages"] = accumulated["messages"] + msgs
                                for msg in msgs:
                                    for tool_call in (getattr(msg, "tool_calls", None) or []):
                                        name = tool_call.get("name") if isinstance(tool_call, dict) else None
                                        if not name:
                                            continue
                                        args = tool_call.get("args") if isinstance(tool_call, dict) else None
                                        fp = json.dumps({"name": name, "args": args}, sort_keys=True, default=str)
                                        if fp == last_tool_call_fp:
                                            repeated_tool_call_count += 1
                                        else:
                                            last_tool_call_fp = fp
                                            repeated_tool_call_count = 1
                                        if repeated_tool_call_count >= max_consecutive_repeated_tool_calls:
                                            if trace_logger is not None:
                                                trace_logger.flush(elapsed_s)
                                            raise RepeatedToolCallError(
                                                f"Tool call {name!r} with identical arguments was repeated "
                                                f"{repeated_tool_call_count} times consecutively; aborting."
                                            )

        if trace_logger is not None:
            trace_logger.flush(time.perf_counter() - started_at)

        return accumulated

    if timeout_s > 0:
        async with asyncio.timeout(timeout_s):
            return await _stream_then_collect_state()
    return await _stream_then_collect_state()


def invoke_agent_with_timeout(
    agent: Any,
    payload: Dict[str, Any],
    *,
    config: Dict[str, Any],
    timeout_s: float,
    trace_logger: Any = None,
    max_consecutive_repeated_tool_calls: int = DEFAULT_MAX_CONSECUTIVE_REPEATED_TOOL_CALLS,
) -> Any:
    """ Sync entry point for Stage 1/2 (called from plain sync code): runs
        _stream_agent_core in a dedicated, reused asyncio.Runner.
    """
    global _ASYNC_RUNNER
    if _ASYNC_RUNNER is None:
        _ASYNC_RUNNER = asyncio.Runner()
    return _ASYNC_RUNNER.run(
        _stream_agent_core(
            agent, payload, config=config, timeout_s=timeout_s, trace_logger=trace_logger,
            max_consecutive_repeated_tool_calls=max_consecutive_repeated_tool_calls,
        )
    )


async def ainvoke_agent_with_timeout(
    agent: Any,
    payload: Dict[str, Any],
    *,
    config: Dict[str, Any],
    timeout_s: float,
    trace_logger: Any = None,
    max_consecutive_repeated_tool_calls: int = DEFAULT_MAX_CONSECUTIVE_REPEATED_TOOL_CALLS,
) -> Any:
    """ Async-native entry point for Stage 3: awaits _stream_agent_core directly
        in the caller's own running event loop, since Stage 3's agent must share
        a loop with the MCP client session its tools are bound to.
    """
    return await _stream_agent_core(
        agent, payload, config=config, timeout_s=timeout_s, trace_logger=trace_logger,
        max_consecutive_repeated_tool_calls=max_consecutive_repeated_tool_calls,
    )


def _close_async_runner() -> None:
    global _ASYNC_RUNNER
    if _ASYNC_RUNNER is not None:
        _ASYNC_RUNNER.close()
        _ASYNC_RUNNER = None


atexit.register(_close_async_runner)
