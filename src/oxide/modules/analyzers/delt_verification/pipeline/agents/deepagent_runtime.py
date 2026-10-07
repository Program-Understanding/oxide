"""Isolated deepagents construction and invocation surface.

Validated against: deepagents==0.7.15, langchain==1.4.1, langgraph==1.2.11,
langchain-ollama==1.1.0.
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
from deepagents.middleware.filesystem import FilesystemPermission
from deepagents.backends.protocol import EditResult, WriteResult
from deepagents.backends.utils import create_file_data
from langchain_ollama import ChatOllama
from pydantic import Field
from langchain_core.messages import HumanMessage
from langchain_core.tools import tool
from langchain.agents.middleware import after_model

_thread_local = threading.local()

DEFAULT_MAX_CONSECUTIVE_REPEATED_TOOL_CALLS = 10


class PartialRunError(Exception):
    """Base for failures that cut a run mid-flight.

    Carries whatever the run accumulated on .partial so callers can still count the tokens
    the run spent before it was cut.
    """

    def __init__(self, message: str, *, partial: Optional[Dict[str, Any]] = None) -> None:
        super().__init__(message)
        self.partial: Dict[str, Any] = partial if isinstance(partial, dict) else {"messages": []}


class RepeatedToolCallError(PartialRunError):
    """Raised when the agent calls the same tool with identical arguments too many times in a row."""


class AgentRunTimeout(PartialRunError, TimeoutError):
    """A run cut by the wall-clock budget.

    Subclasses TimeoutError so existing timeout handling still matches it.
    """


class ModelCallTimeout(AgentRunTimeout):
    """A run cut because one model call outlived the per-call cap.

    Typed rather than distinguished by message text: which of the two caps fired decides
    the failure_reason every stage records, and that must not depend on how the message
    happens to be worded or formatted.
    """


class MalformedModelResponseError(PartialRunError):
    """Raised when the provider rejects the model's own output mid-run.

    Local models occasionally emit tool-call syntax the provider cannot parse
    (e.g. a <function> block closed by </parameter>), and Ollama surfaces that
    as a ResponseError. That is a spoiled response, not a broken pipeline, so it
    is typed separately instead of landing in the generic invoke_failed bucket.
    """


def find_nested(exc: BaseException, predicate: Callable[[BaseException], bool]) -> Optional[BaseException]:
    """Return exc, or the first exception it nests, satisfying predicate; else None.

    Failures raised inside the agent's task groups reach callers wrapped in one or more
    ExceptionGroups, so anything that distinguishes them is only reachable by unwrapping.
    """
    if predicate(exc):
        return exc
    nested = getattr(exc, "exceptions", None)
    if isinstance(nested, (list, tuple)):
        for inner in nested:
            found = find_nested(inner, predicate)
            if found is not None:
                return found
    return None


def find_timeout_error(exc: BaseException) -> Optional[BaseException]:
    """Return the TimeoutError exc is, or nests, else None."""
    return find_nested(exc, lambda e: isinstance(e, TimeoutError))


def attach_partial(exc: BaseException, accumulated: Dict[str, Any]) -> None:
    carriers = []

    def collect(e: BaseException) -> None:
        if isinstance(e, PartialRunError):
            carriers.append(e)
        for inner in getattr(e, "exceptions", None) or ():
            collect(inner)

    collect(exc)
    for carrier in carriers:
        if not carrier.partial.get("messages"):
            carrier.partial = accumulated
    if not carriers:
        try:
            exc.partial = accumulated
        except AttributeError:
            pass


def partial_messages(exc: BaseException) -> list:
    """Messages accumulated before exc cut the run, for token accounting.

    The unbounded stage runs the agent inside the MCP session's task group, which rewraps
    its failures, so the payload is only reachable by unwrapping.
    """
    carrier = find_nested(exc, lambda e: isinstance(getattr(e, "partial", None), dict))
    partial = getattr(carrier, "partial", None) if carrier is not None else None
    msgs = partial.get("messages") if isinstance(partial, dict) else None
    return msgs if isinstance(msgs, list) else []


def classify_agent_failure(
    exc: BaseException, *, request_timeout_s: float, model_call_timeout_s: float
) -> Tuple[str, str]:
    """Map an agent-side failure onto its (failure_reason, human-readable why).

    Both stages record the same failure_reason vocabulary, so the mapping lives here next
    to the exceptions it dispatches on rather than being re-derived per stage -- the two
    ladders this replaces disagreed, and a nested timeout was reported as model_call_timeout
    by one stage and plain timeout by the other.
    """
    if find_nested(exc, lambda e: isinstance(e, RepeatedToolCallError)) is not None:
        return "repeated_tool_call", str(exc)
    if find_nested(exc, lambda e: isinstance(e, MalformedModelResponseError)) is not None:
        return "malformed_model_response", (
            "The model emitted a response the provider could not parse, so the run stopped "
            "before reaching a final decision."
        )
    if find_nested(exc, lambda e: isinstance(e, ModelCallTimeout)) is not None:
        return "model_call_timeout", (
            f"A single model call exceeded {model_call_timeout_s:g}s, so the run stopped "
            "before reaching a final decision."
        )
    if find_timeout_error(exc) is not None:
        return "timeout", (
            f"The run timed out after {request_timeout_s:g}s before reaching a final decision."
        )
    return "invoke_failed", "The run failed before reaching a final decision."


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
        (which should return (payload, ok)), and records the normalized payload into
        final_holder["final"] so the caller can read it back after the agent run
        completes. An unusable label is handed back to the model to retry rather than
        raising, so a single malformed call does not cost the whole investigation. Each stage owns its own schema/normalize
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
        complaint: Optional[str] = None
        if not ok or final is None:
            complaint = (
                f"Rejected: {tool_name} requires a label of exactly \"safe\" or \"not_safe\", "
                f"and was called with {kwargs!r}. Call it again with the label argument set."
            )
        elif precondition is not None:
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
    # Ollama options ChatOllama exposes no field for (min_p, presence_penalty). _chat_params
    # builds its options dict from named fields only, so these are merged in afterwards.
    extra_options: Dict[str, Any] = Field(default_factory=dict)

    def _chat_params(self, *args: Any, **kwargs: Any) -> Dict[str, Any]:
        params = super()._chat_params(*args, **kwargs)
        if self.extra_options:
            options = dict(params.get("options") or {})
            options.update(self.extra_options)
            params["options"] = options
        return params

    async def _agenerate(self, *args: Any, **kwargs: Any) -> Any:
        if self.call_timeout_s <= 0:
            return await super()._agenerate(*args, **kwargs)
        try:
            return await asyncio.wait_for(
                super()._agenerate(*args, **kwargs), self.call_timeout_s
            )
        except asyncio.TimeoutError:
            raise ModelCallTimeout(
                f"model call exceeded {self.call_timeout_s:g}s"
            ) from None

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
                    raise ModelCallTimeout(
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
                    raise ModelCallTimeout(
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
    model: str,
    *,
    request_timeout_s: float,
    base_url: Optional[str] = None,
    temperature: Optional[float] = None,
    seed: Optional[int] = None,
    top_p: Optional[float] = None,
    top_k: Optional[int] = None,
    min_p: Optional[float] = None,
    presence_penalty: Optional[float] = None,
    repeat_penalty: Optional[float] = None,
    max_output_tokens: Optional[int] = None,
) -> ChatOllama:
    """Build the stage's chat client with the run's sampling configuration.

    An option that is None here is absent from the request, so the model's own Modelfile
    value stands. Anything passed pins that one option and nothing else.
    """
    kwargs: Dict[str, Any] = {
        "model": model,
        # Never unload. A request's keep_alive overrides the server's OLLAMA_KEEP_ALIVE, so
        # a finite value here silently defeats the launcher's -1: a worker that spends
        # longer than it on diffing or decompilation comes back to an unloaded model, and
        # the next call blocks on reloading tens of GB. That reload is counted against
        # call_timeout_s, so it surfaces as a model_call_timeout with no tokens.
        "keep_alive": -1,
        # Sets deepagents' summarization threshold. Present, it triggers at a 0.85 fraction
        # of this value and keeps 10% of history; absent, it triggers at 170000 tokens and
        # keeps 6 messages. A turn may emit max_output_tokens, so the wider margin is what
        # keeps a long investigation from having its history replaced by a summary the same
        # model generates, which would also add tokens to the run's totals.
        "profile": {"max_input_tokens": 262144},
    }
    for name, value, cast in (
        ("temperature", temperature, float),
        ("seed", seed, int),
        ("top_p", top_p, float),
        ("top_k", top_k, int),
        ("repeat_penalty", repeat_penalty, float),
        ("num_predict", max_output_tokens, int),
    ):
        if value is not None:
            kwargs[name] = cast(value)
    extra = {
        name: float(value)
        for name, value in (("min_p", min_p), ("presence_penalty", presence_penalty))
        if value is not None
    }
    if extra:
        kwargs["extra_options"] = extra
    if base_url:
        kwargs["base_url"] = base_url
    if request_timeout_s > 0:
        kwargs["client_kwargs"] = {"timeout": request_timeout_s}
        kwargs["call_timeout_s"] = request_timeout_s
    return WallClockChatOllama(**kwargs)


def build_bounded_agent(
    *,
    main_model: ChatOllama,
    file_mirror: Dict[str, str],
    decision_tool: Any,
    system_prompt: str,
    final_holder: Optional[Dict[str, Any]] = None,
    decision_tool_name: str = "submit_decision",
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
        # GuardedStateBackend below intercepts write and edit but not delete, so without
        # this rule an agent can delete the evidence its investigation is scoped to. The
        # framework classifies delete as a write, so one deny rule closes that path.
        permissions=[
            FilesystemPermission(operations=["write"], paths=["/inputs", "/inputs/**"], mode="deny")
        ],
        tools=[decision_tool] + list(extra_tools or []),
        system_prompt=system_prompt,
        middleware=(
            [_ToolExclusionMiddleware(excluded=frozenset({"task"}))]
            + ([require_decision_middleware(final_holder, decision_tool_name)]
               if final_holder is not None else [])
        ),
        backend=GuardedStateBackend(mirror=file_mirror),
        name=agent_name,
    )


def build_agent_payload(diff_text: str, prompt: str, callee_texts: Optional[Dict[str, str]] = None) -> Dict[str, Any]:
    files: Dict[str, Any] = {"/inputs/diff.txt": create_file_data(diff_text)}
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
        from oxide.modules.analyzers.delt_verification.pipeline.agents.telemetry.agent_trace import (
            normalize_stream_item,
        )

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
            # State collection and the repeat guard run whether or not tracing is on. They
            # were once nested under the trace_logger check, which made token accounting and
            # loop detection silently depend on logging being enabled.
            chunk = normalize_stream_item(item)
            if trace_logger is not None:
                trace_logger.on_chunk(chunk, elapsed_s)
            if chunk.get("type") == "updates":
                data = chunk.get("data")
                if isinstance(data, dict):
                    for node_update in data.values():
                        if not isinstance(node_update, dict):
                            continue
                        msgs = node_update.get("messages")
                        if not isinstance(msgs, list):
                            continue
                        accumulated["messages"].extend(msgs)
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
                                        f"{repeated_tool_call_count} times consecutively; aborting.",
                                        partial=accumulated,
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
                timed_out = find_timeout_error(exc)
                if timed_out is not None and not isinstance(exc, AgentRunTimeout):
                    if trace_logger is not None:
                        trace_logger.flush(time.perf_counter() - started_at)
                    rewrapped = ModelCallTimeout if isinstance(timed_out, ModelCallTimeout) else AgentRunTimeout
                    raise rewrapped(str(timed_out), partial=accumulated) from exc
                attach_partial(exc, accumulated)
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
        try:
            async with asyncio.timeout(timeout_s):
                return await _stream_guarding_response_errors()
        except TimeoutError as exc:
            if isinstance(exc, AgentRunTimeout):
                attach_partial(exc, accumulated)
                raise
            raise AgentRunTimeout(
                f"run exceeded {timeout_s:g}s", partial=accumulated
            ) from exc
    return await _stream_guarding_response_errors()


def agent_messages(out: Any) -> list:
    """The message list off an agent state, however the caller's version exposes it."""
    msgs = out.get("messages") if isinstance(out, dict) else getattr(out, "messages", None)
    return msgs if isinstance(msgs, list) else []


DECISION_REQUIRED_CUT = (
    "Your last turn was cut off at the output limit before you could act on it. Do not "
    "restate that analysis. On the evidence you have already gathered, write your report to "
    "/work/final.md if your verdict is not_safe, then call {tool}."
)

DECISION_REQUIRED_STOPPED = (
    "You ended a turn without calling a tool, which ends the run. Do not open new lines of "
    "inquiry. On the evidence you have already gathered, write your report to /work/final.md "
    "if your verdict is not_safe, then call {tool}."
)


def require_decision_middleware(
    final_holder: Dict[str, Any], tool_name: str, *, max_prompts: int = 2
) -> Any:
    """after_model hook that sends a run back to the model when it ends undecided.

    An assistant message carrying no tool call ends the agent graph, which discards an
    investigation that may already have reached a verdict. Two causes produce it, a turn cut
    at the output cap and a turn the model completed while only describing its next step, and
    both are recoverable from the state the run already holds. Recovering in the graph rather
    than by a second invoke keeps every message in one run, so no checkpointer is needed and
    token usage stays countable off the single message list.

    max_prompts bounds the loop. Past it the hook stops intervening and the run ends
    undecided, which the stage records as missing_final_answer.
    """
    prompts = {"n": 0}

    def _hook(state: Any, runtime: Any) -> Optional[Dict[str, Any]]:
        if isinstance(final_holder.get("final"), dict):
            return None
        messages = state.get("messages") if isinstance(state, dict) else getattr(state, "messages", None)
        if not messages:
            return None
        last = messages[-1]
        if getattr(last, "tool_calls", None) or prompts["n"] >= max_prompts:
            return None
        prompts["n"] += 1
        metadata = getattr(last, "response_metadata", None)
        reason = metadata.get("done_reason") if isinstance(metadata, dict) else None
        template = DECISION_REQUIRED_CUT if reason == "length" else DECISION_REQUIRED_STOPPED
        return {
            "messages": [HumanMessage(content=template.format(tool=tool_name))],
            "jump_to": "model",
        }

    return after_model(_hook, can_jump_to=["model"], name="require_decision")


def invoke_agent_with_timeout(
    agent: Any,
    payload: Dict[str, Any],
    *,
    config: Dict[str, Any],
    timeout_s: float,
    trace_logger: Any = None,
    max_consecutive_repeated_tool_calls: int = DEFAULT_MAX_CONSECUTIVE_REPEATED_TOOL_CALLS,
) -> Any:
    """ Sync entry point for the bounded agent (called from plain sync code): runs
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
