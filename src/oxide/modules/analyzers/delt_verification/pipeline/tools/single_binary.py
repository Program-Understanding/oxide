"""Scoped single-binary MCP tool surface for the binary-context phase."""

from __future__ import annotations

from typing import Any, Iterable

from langchain_core.tools import BaseTool

from oxide.modules.analyzers.delt_verification.pipeline.tools.scoped import Bind, scope_tools

BINARY_CONTEXT_TOOLS = (
    "get_binary_metadata",
    "get_function_list",
    "search_symbols_by_name",
    "search_strings",
    "decompile_function",
    "disassemble",
    "get_call_graph",
    "list_xrefs",
    "list_imports",
    "list_exports",
    "get_control_flow_graph",
)


def build_binary_context_tools(*, mcp_tools: Iterable[Any], binary_oid: str) -> list[BaseTool]:
    """Expose the analysis tools, all pinned to the one binary under investigation."""
    return scope_tools(
        mcp_tools=mcp_tools,
        allow=BINARY_CONTEXT_TOOLS,
        rules={"oid_or_name": Bind(str(binary_oid))},
    )
