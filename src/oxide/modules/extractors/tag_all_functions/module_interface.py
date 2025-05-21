import logging
from typing import Any, Dict, Optional, List
from collections import deque

import networkx as nx
try:
    from llm_service import runner
    llm_enabled = True
except ImportError:
    llm_enabled = False

from oxide.core import api, progress
import textwrap
import math

logger = logging.getLogger(__name__)

# Module metadata
DESC = """Uses an LLM to generate high-level tags for a file by analysing its
call-graph and summarising the *influential* functions only."""
NAME = "tag_all_functions"
CATEGORY = ""

# Options documentation
opts_doc: Dict[str, Dict[str, str]] = {}


def documentation() -> Dict[str, Any]:
    """Return module documentation understood by the Oxide plug-in loader."""
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
        "category": CATEGORY,
    }


# ────────────────────────────────────────────────────────────────────────────
# Main entry‑point
# ────────────────────────────────────────────────────────────────────────────

def process(oid: str, opts: Dict[str, Any]) -> bool:
    """Populate *only* the **influential functions** for *oid* and store it."""
    logger.debug("Starting tag‑file process for %s", oid)

    call_graph: nx.DiGraph = api.get_field("call_graph", oid, oid)
    if call_graph.number_of_nodes() == 0:
        results = "FAILED"
        api.store(NAME, oid, results, opts)
        return False

    scc_dag = _build_scc_dag(call_graph)
    bottom_up_sccs = reversed(list(nx.topological_sort(scc_dag)))

    # We now keep *one* output bucket only
    results = {}

    # Ensure decompilation is available before we begin
    decmap = api.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if decmap is None:
        results = "FAILED"
        api.store(NAME, oid, results, opts)
        return False

    p = progress.Progress(call_graph.number_of_nodes())

    # Walk the SCCs bottom‑up.  Skip early if node is *not* influential.
    for scc in bottom_up_sccs:
        for node in sorted(scc):
            p.tick()
            if not _is_valid_function(oid, node):
                continue

            name = _get_function_name(oid, node) or f"sub_{node:x}"
            entry = {"offset": node}

            tag = api.retrieve("tag_function", oid, {"func_name": name})
            tag_context = api.retrieve("tag_function_context", oid, {"func_name": name})
            if tag:
                entry["tag"] = tag
            if tag_context:
                entry["tag_context"] = tag_context

            results[name] = entry

    api.store(NAME, oid, results, opts)
    logger.debug("Finished tag‑file process for %s", oid)
    return True


# ────────────────────────────────────────────────────────────────────────────
# Helper functions (identical to previous version unless noted)              │
# ────────────────────────────────────────────────────────────────────────────


def _get_function_name(oid: str, offset: Any) -> Optional[str]:
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    return funcs.get(offset, {}).get("name")


def _is_valid_function(oid: str, offset: Any, *, min_instructions: int = 5) -> bool:
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    orig_blocks = api.get_field("ghidra_disasm", oid, "original_blocks") or {}
    blk_ids = funcs.get(offset, {}).get("blocks", [])
    total_instr = sum(len(orig_blocks.get(bid, [])) for bid in blk_ids)
    return total_instr >= min_instructions

def _build_scc_dag(g: nx.DiGraph) -> nx.DiGraph:
    sccs = [frozenset(c) for c in nx.strongly_connected_components(g)]
    f2s = {n: s for s in sccs for n in s}
    dag = nx.DiGraph()
    dag.add_nodes_from(sccs)
    for u, v in g.edges():
        su, sv = f2s[u], f2s[v]
        if su != sv:
            dag.add_edge(su, sv)
    return dag


def _compute_depth_cache(g: nx.DiGraph) -> Dict[Any, int]:
    roots = [n for n, d in g.in_degree() if d == 0]
    depth: Dict[Any, int] = {r: 0 for r in roots}
    q = deque(roots)
    while q:
        u = q.popleft()
        for v in g.successors(u):
            if v not in depth:
                depth[v] = depth[u] + 1
                q.append(v)
    return depth