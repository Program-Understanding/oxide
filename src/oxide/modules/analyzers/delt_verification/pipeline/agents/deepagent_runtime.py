"""Isolated deepagents construction and invocation surface.

Validated against: deepagents==0.6.10, langgraph==1.2.5, langchain-ollama==1.1.0.
If a future upstream release breaks GuardedStateBackend's constructor contract,
create_deep_agent's kwargs, or agent.astream's stream_mode/version behavior,
this file is the single, obvious place to fix it. It owns everything
deepagents-specific (create_deep_agent, the custom StateBackend, and driving
agent.astream).
"""

import asyncio
import atexit
import json
import threading
import time
from typing import Any, Callable, Dict, Optional, Tuple

from deepagents import create_deep_agent
from deepagents.backends import StateBackend
from deepagents.middleware._tool_exclusion import _ToolExclusionMiddleware
from deepagents.backends.protocol import EditResult, WriteResult
from deepagents.backends.utils import create_file_data
from langchain_ollama import ChatOllama
from langgraph.checkpoint.memory import MemorySaver
from langchain_core.tools import tool

_thread_local = threading.local()

DEFAULT_MAX_CONSECUTIVE_REPEATED_TOOL_CALLS = 10


class RepeatedToolCallError(Exception):
    """Raised when the agent calls the same tool with identical arguments too many times in a row."""


class MalformedModelResponseError(Exception):
    """Raised when the provider rejects the model's own output mid-run.

    Local models occasionally emit tool-call syntax the provider cannot parse
    (e.g. a <function> block closed by </parameter>), and Ollama surfaces that
    as a ResponseError. That is a spoiled response, not a broken pipeline, so it
    is typed separately instead of landing in the generic invoke_failed bucket.
    Whatever the run accumulated before the bad response is carried on .partial
    so callers can still count token usage.
    """

    def __init__(self, message: str, *, partial: Optional[Dict[str, Any]] = None) -> None:
        super().__init__(message)
        self.partial: Dict[str, Any] = partial if isinstance(partial, dict) else {"messages": []}


def is_repeated_tool_call_error(exc: BaseException) -> bool:
    """True if exc is, or nests, a RepeatedToolCallError.

    The agent runs under anyio task groups, so the error surfaces to callers wrapped in
    one or more ExceptionGroups rather than as itself.
    """
    if isinstance(exc, RepeatedToolCallError):
        return True
    nested = getattr(exc, "exceptions", None)
    if isinstance(nested, (list, tuple)):
        return any(is_repeated_tool_call_error(inner) for inner in nested)
    return False


def is_malformed_model_response_error(exc: BaseException) -> bool:
    """True if exc is, or nests, a MalformedModelResponseError."""
    if isinstance(exc, MalformedModelResponseError):
        return True
    nested = getattr(exc, "exceptions", None)
    if isinstance(nested, (list, tuple)):
        return any(is_malformed_model_response_error(inner) for inner in nested)
    return False


def _find_provider_response_error(exc: BaseException) -> Optional[BaseException]:
    """Return the ollama ResponseError exc is, or nests, else None.

    Matched on class name so this module keeps no direct ollama import, and
    recursively because the error reaches us wrapped in anyio ExceptionGroups.
    Returns the error itself rather than a bool: an ExceptionGroup stringifies
    to "unhandled errors in a TaskGroup", so the inner one is the only thing
    that names what actually went wrong.
    """
    if type(exc).__name__ == "ResponseError":
        return exc
    for inner in (getattr(exc, "exceptions", None) or ()):
        found = _find_provider_response_error(inner)
        if found is not None:
            return found
    return None


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
    precondition: Optional[Callable[[Dict[str, Any]], Optional[str]]] = None,
) -> Any:
    """ Build a single-shot deepagents tool: validates its arguments via normalize()
        (which should return (payload, ok)), raising if invalid, and records the
        normalized payload into final_holder["final"] so the caller can read it
        back after the agent run completes. Each stage owns its own schema/normalize
        function -- this factory just wires the common "validate, record, confirm"
        pattern once instead of duplicating it per stage.

        return_direct ends the agent run as soon as this tool is called, so the
        verdict cannot be lost to a stuck loop after it has been recorded. The tool
        result needs no further reasoning, and create_agent routes straight to the
        graph's exit once every tool call in the turn is return_direct.
    """

    @tool(tool_name, args_schema=schema_cls, description=doc, return_direct=True)
    def _submit(**kwargs: Any) -> str:
        final, ok = normalize(kwargs)
        if not ok or final is None:
            raise ValueError(f"invalid arguments for {tool_name}: {kwargs!r}")
        if precondition is not None:
            complaint = precondition(final)
            if complaint:
                # Reject without recording. A rejected submission must not end the run,
                # but langchain's tools->model edge routes to the graph exit whenever every
                # tool called in the turn has return_direct set, and it reads that flag off
                # the tool object *after* the call. So clear it to send the complaint back
                # to the model for another attempt.
                _submit.return_direct = False
                return complaint
        _submit.return_direct = True
        final_holder["final"] = final
        return f"recorded {final}"

    return _submit


def require_report_before_not_safe(
    file_mirror: Dict[str, str], report_path: str = "/work/final.md"
) -> Callable[[Dict[str, Any]], Optional[str]]:
    """Precondition for make_decision_tool: a not_safe verdict must carry a written report.

    Agents sometimes put the analysis in an assistant message and submit without ever
    writing the report file. The next stage is fed that file, so an unwritten report
    silently strips the evidence out of a positive detection.
    """

    def _check(final: Dict[str, Any]) -> Optional[str]:
        if final.get("label") != "not_safe":
            return None
        if (file_mirror.get(report_path) or "").strip():
            return None
        return (
            f"Rejected: a not_safe verdict requires a report. Write your analysis to "
            f"{report_path}, identifying the specific trigger and the payoff it enables, "
            "then call this tool again."
        )

    return _check


class WallClockChatOllama(ChatOllama):
    """ChatOllama that bounds how long one model call may run.

    The HTTP timeout in ``client_kwargs`` is a per-read timeout. The agents consume the
    model by streaming, so it bounds the gap between chunks rather than the length of the
    call: a model that keeps emitting tokens slowly never trips it, and a single
    generation can run past the caller's whole budget. ``call_timeout_s`` bounds the call
    itself, so a stalled generation gives the budget back to the agent instead of
    consuming it.
    """

    call_timeout_s: float = 0.0

    async def _agenerate(self, *args: Any, **kwargs: Any) -> Any:
        if self.call_timeout_s <= 0:
            return await super()._agenerate(*args, **kwargs)
        return await asyncio.wait_for(
            super()._agenerate(*args, **kwargs), self.call_timeout_s
        )

    async def _astream(self, *args: Any, **kwargs: Any) -> Any:
        if self.call_timeout_s <= 0:
            async for chunk in super()._astream(*args, **kwargs):
                yield chunk
            return

        loop = asyncio.get_running_loop()
        deadline = loop.time() + self.call_timeout_s
        chunks = super()._astream(*args, **kwargs).__aiter__()
        try:
            while True:
                remaining = deadline - loop.time()
                if remaining <= 0:
                    raise asyncio.TimeoutError(
                        f"model call exceeded {self.call_timeout_s:g}s"
                    )
                try:
                    # Bounded by whatever is left of the call's budget, not by the gap
                    # between chunks, so slow-but-steady output still hits the deadline.
                    chunk = await asyncio.wait_for(chunks.__anext__(), remaining)
                except StopAsyncIteration:
                    return
                except asyncio.TimeoutError:
                    # Name the cap that fired; the caller's run budget raises this too.
                    raise asyncio.TimeoutError(
                        f"model call exceeded {self.call_timeout_s:g}s"
                    ) from None
                yield chunk
        finally:
            # Abandoning a stream mid-response leaves the HTTP response open, and a run
            # makes hundreds of these calls.
            aclose = getattr(chunks, "aclose", None)
            if aclose is not None:
                await aclose()


def make_agent_model(
    model: str, *, request_timeout_s: float, base_url: Optional[str] = None
) -> ChatOllama:
    kwargs: Dict[str, Any] = {
        "model": model,
        "keep_alive": "10m",
        "profile": {"max_input_tokens": 262144},
    }
    if base_url:
        kwargs["base_url"] = base_url
    if request_timeout_s > 0:
        kwargs["client_kwargs"] = {"timeout": request_timeout_s}
        kwargs["call_timeout_s"] = request_timeout_s
    return WallClockChatOllama(**kwargs)


def build_triage_agent(
    *,
    main_model: ChatOllama,
    file_mirror: Dict[str, str],
    decision_tool: Any,
    system_prompt: str,
    extra_tools: Optional[list] = None,
    agent_name: str = "delt_agent",
) -> Any:
    """Build a deepagents agent sandboxed to file_mirror with this stage's decision tool.

    Subagents are disabled. deepagents auto-registers a general-purpose `task` subagent
    even when subagents=[], and that subagent inherits this agent's tools -- including the
    decision tool. A subagent that calls it writes straight into final_holder, hijacking
    the run's verdict while the main agent keeps investigating unaware (return_direct only
    ends the subagent's own graph). Its token usage also escapes the usage counted off the
    main message list, and its work never reaches the trace. _ToolExclusionMiddleware runs
    late in the stack and strips `task` from the model request, so nothing can call it.
    """
    return create_deep_agent(
        model=main_model,
        tools=[decision_tool] + list(extra_tools or []),
        system_prompt=system_prompt,
        checkpointer=MemorySaver(),
        subagents=[],
        middleware=[_ToolExclusionMiddleware(excluded=frozenset({"task"}))],
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
        be awaited either from a fresh asyncio.Runner or from within an already-running loop.
    """
    started_at = time.perf_counter()
    # Held out here, not inside the streaming coroutine, so a mid-run provider
    # rejection can still hand back whatever the agent produced before it.
    accumulated: Dict[str, Any] = {"messages": []}

    async def _stream_then_collect_state() -> Any:
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
                from oxide.modules.analyzers.delt_verification.pipeline.agents.telemetry.agent_trace import normalize_stream_item

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

    async def _stream_guarding_response_errors() -> Any:
        try:
            return await _stream_then_collect_state()
        except BaseException as exc:  # noqa: BLE001
            response_error = _find_provider_response_error(exc)
            if response_error is None:
                raise
            # The stream dies where it stands, so flush the trace here; otherwise
            # the log ends mid-run with no record of why.
            if trace_logger is not None:
                trace_logger.flush(time.perf_counter() - started_at)
            raise MalformedModelResponseError(
                f"Provider rejected the model's response: {response_error}",
                partial=accumulated,
            ) from exc

    if timeout_s > 0:
        async with asyncio.timeout(timeout_s):
            return await _stream_guarding_response_errors()
    return await _stream_guarding_response_errors()


def invoke_agent_with_timeout(
    agent: Any,
    payload: Dict[str, Any],
    *,
    config: Dict[str, Any],
    timeout_s: float,
    trace_logger: Any = None,
    max_consecutive_repeated_tool_calls: int = DEFAULT_MAX_CONSECUTIVE_REPEATED_TOOL_CALLS,
) -> Any:
    """ Sync entry point for the triage agent (called from plain sync code): runs
        _stream_agent_core in a dedicated, reused asyncio.Runner.
    """
    return get_async_runner().run(
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
    """Async-native entry point: awaits _stream_agent_core directly in the caller's event loop."""
    return await _stream_agent_core(
        agent, payload, config=config, timeout_s=timeout_s, trace_logger=trace_logger,
        max_consecutive_repeated_tool_calls=max_consecutive_repeated_tool_calls,
    )


def get_async_runner() -> asyncio.Runner:
    """One asyncio.Runner per thread, reused across invocations.

    Building a Runner per call tears down and rebuilds an event loop every time,
    which when comparisons run concurrently in threads also races the MCP stdio
    transport's own cleanup. Keeping one loop per thread avoids both.
    """
    runner = getattr(_thread_local, "runner", None)
    if runner is None:
        runner = asyncio.Runner()
        _thread_local.runner = runner
    return runner


def _close_async_runner() -> None:
    runner = getattr(_thread_local, "runner", None)
    if runner is not None:
        runner.close()
        _thread_local.runner = None


atexit.register(_close_async_runner)
