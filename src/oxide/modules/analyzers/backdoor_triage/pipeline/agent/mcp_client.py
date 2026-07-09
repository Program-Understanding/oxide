"""MCP subprocess/session lifecycle for Stage 3's binary-analysis tools.

Launches oxide's MCP server (oxide_mcp_server.py) as a stdio subprocess and
loads its tools for a single Stage 3 investigation. A single, dedicated
ClientSession (rather than a per-tool-call client) is used deliberately: it
avoids re-importing oxide on every tool call and lets subprocess stderr be
captured to a log file instead of silently disappearing on a startup crash.
"""

import asyncio
import atexit
import os
import sys
import tempfile
import threading
from typing import Any, Awaitable, Callable, Dict, List, Optional

_ASYNC_RUNNER: Optional[asyncio.Runner] = None
_RUNNER_LOCK = threading.Lock()


def _get_async_runner() -> asyncio.Runner:
    global _ASYNC_RUNNER
    with _RUNNER_LOCK:
        if _ASYNC_RUNNER is None:
            _ASYNC_RUNNER = asyncio.Runner()
        return _ASYNC_RUNNER


def _close_async_runner() -> None:
    global _ASYNC_RUNNER
    with _RUNNER_LOCK:
        if _ASYNC_RUNNER is not None:
            _ASYNC_RUNNER.close()
            _ASYNC_RUNNER = None


atexit.register(_close_async_runner)


def resolve_oxide_server_path() -> str:
    """ Locate oxide_mcp_server.py at the oxide project root (the same file
        oxide's own MCP-based tooling elsewhere in this repo resolves to).
    """
    # This file lives at src/oxide/modules/analyzers/backdoor_triage/pipeline/agent/
    # -- eight directory levels below the project root where oxide_mcp_server.py lives.
    project_root = os.path.abspath(__file__)
    for _ in range(8):
        project_root = os.path.dirname(project_root)
    return os.path.join(project_root, "oxide_mcp_server.py")


def _read_tail(path: str, limit: int = 4000) -> str:
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as handle:
            text = handle.read()
    except OSError:
        return ""
    return text[-limit:]


def run_with_mcp_tools(
    run_agent: Callable[[List[Any]], Awaitable[Dict[str, Any]]],
    *,
    trace_path: Optional[str] = None,
    server_path: Optional[str] = None,
) -> Dict[str, Any]:
    """ Launch oxide's MCP server as a subprocess, load its tools, and call
        await run_agent(tools) inside that session. run_agent is an async
        callable taking the loaded LangChain tool list and returning a result
        dict. Returns whatever run_agent returns, or a failure result (see
        below) if the subprocess/session itself never got that far.
    """
    resolved_server_path = server_path or resolve_oxide_server_path()
    if not os.path.isfile(resolved_server_path):
        raise FileNotFoundError(f"oxide_mcp_server.py not found at {resolved_server_path}")
    oxide_root = os.path.dirname(resolved_server_path)

    if trace_path:
        stderr_path = os.path.join(os.path.dirname(os.path.abspath(trace_path)), "mcp_server.stderr.log")
    else:
        stderr_path = os.path.join(tempfile.gettempdir(), "oxide_mcp_server.stderr.log")
    try:
        os.makedirs(os.path.dirname(stderr_path), exist_ok=True)
    except OSError:
        stderr_path = os.path.join(tempfile.gettempdir(), "oxide_mcp_server.stderr.log")

    # Holds the agent result so a stdio teardown race (an exception raised while
    # the session closes) doesn't discard an already-completed investigation.
    result_holder: Dict[str, Any] = {}

    async def _run() -> Dict[str, Any]:
        from mcp import ClientSession, StdioServerParameters
        from mcp.client.stdio import stdio_client
        from langchain_mcp_adapters.tools import load_mcp_tools

        params = StdioServerParameters(
            command=sys.executable,
            args=[resolved_server_path, f"--oxidepath={oxide_root}"],
            cwd=oxide_root,
        )
        with open(stderr_path, "w", encoding="utf-8") as errlog:
            async with stdio_client(params, errlog=errlog) as (read, write):
                async with ClientSession(read, write) as session:
                    await session.initialize()
                    lc_tools = await load_mcp_tools(session)
                    result_holder["result"] = await run_agent(lc_tools)
                    return result_holder["result"]

    try:
        return _get_async_runner().run(_run())
    except BaseException as exc:  # noqa: BLE001 -- surface subprocess/teardown failures cleanly
        if "result" in result_holder:
            # Agent finished; this is the known stdio-teardown race on session
            # close. Keep the completed investigation rather than failing it.
            return result_holder["result"]
        detail = _read_tail(stderr_path)
        msg = (
            "MCP server subprocess failed before the investigation could run. "
            f"Interpreter: {sys.executable}. Check that this Python has oxide, "
            f"mcp, and networkx installed. Server stderr captured at {stderr_path}."
        )
        if detail:
            msg = f"{msg}\n--- server stderr (tail) ---\n{detail}"
        raise RuntimeError(msg) from exc
