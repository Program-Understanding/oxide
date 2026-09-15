"""Scoped unbounded tool surface for one target/baseline binary pair.

Unbounded should investigate only the current binary pair and should not see raw OIDs,
so every tool addresses binaries as `target` or `baseline`.
"""

from __future__ import annotations

from typing import Any, Iterable

from langchain_core.tools import BaseTool

from oxide.modules.analyzers.delt_verification.pipeline.tools.scoped import (
    Bind,
    Choose,
    scope_tools,
)

PAIR_TOOLS = (
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
    "function_decomp_diff",
    "function_call_diff",
    "get_matched_function",
)


def build_scoped_pair_tools(
    *,
    mcp_tools: Iterable[Any],
    target_oid: str,
    baseline_oid: str,
) -> list[BaseTool]:
    """Expose the analysis tools over the current update pair only.

    Single-binary tools take `binary`; the diff tools are fixed to compare target against
    baseline; `get_matched_function` maps a function in one direction across the pair.
    """
    pair = {"target": str(target_oid), "baseline": str(baseline_oid)}
    return scope_tools(
        mcp_tools=mcp_tools,
        allow=PAIR_TOOLS,
        rules={
            "oid_or_name": Choose("binary", pair, "Which binary of the update pair to read."),
            "target_oid_or_name": Bind(pair["target"]),
            "baseline_oid_or_name": Bind(pair["baseline"]),
            "source_oid_or_name": Choose(
                "source_binary", pair, "Binary the given function offset belongs to."
            ),
            "destination_oid_or_name": Choose(
                "destination_binary", pair, "Binary to resolve the matched function in."
            ),
        },
    )
