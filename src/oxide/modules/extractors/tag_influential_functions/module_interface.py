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
DESC = """Uses an LLM to generate high‑level tags for a file by analysing its
call‑graph and summarising the *influential* functions only."""
NAME = "tag_influential_functions"
CATEGORY = ""

# Options documentation
opts_doc: Dict[str, Dict[str, str]] = {}


def documentation() -> Dict[str, Any]:
    """Return module documentation understood by the Oxide plug‑in loader."""
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

    depth_cache = _compute_depth_cache(call_graph)
    scc_dag = _build_scc_dag(call_graph)
    bottom_up_sccs = reversed(list(nx.topological_sort(scc_dag)))

    desired_count = _pick_k_sqrt(len(call_graph))
    influential = _get_influential_nodes(call_graph, depth_cache, desired_count)

    # We now keep *one* output bucket only
    results: Dict[str, Dict[str, Any]] = {}
    influential_tags: List[str] = []

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
            if not _is_valid_function(oid, node) or node not in influential:
                continue

            name = _get_function_name(oid, node) or f"sub_{node:x}"
            entry = {"offset": node, **_metrics(call_graph, depth_cache, node)}

            tag = api.retrieve("tag_function_context", oid, {"func_name": name})
            entry["tag"] = tag if tag else "FAILED"

            results[name] = entry
            if tag:
                influential_tags.append(tag)

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


def _metrics(g: nx.DiGraph, depth: Dict[Any, int], n: Any) -> Dict[str, Any]:
    fi = g.in_degree(n)
    fo = g.out_degree(n)
    ratio = (fo + 1) / (fi + 1)
    score = fo * ratio
    return {
        "fan-in": fi,
        "fan-out": fo,
        "ratio": ratio,
        "depth": depth.get(n),
        "score": score,
    }


def _get_influential_nodes(
        g: nx.DiGraph,
        depth: Dict[Any, int],
        desired_count: int,
        max_depth: int = 4
) -> Dict[Any, Dict[str, Any]]:

    desired_count = min(desired_count, g.number_of_nodes())

    all_metrics = {n: _metrics(g, depth, n) for n in g.nodes}
    # treat None as ∞
    shallow = [
        n for n, m in all_metrics.items()
        if (m_depth := (m["depth"] if m["depth"] is not None else math.inf)) <= max_depth
    ]

    key_fn = lambda n: (-all_metrics[n]["score"], all_metrics[n]["depth"] or math.inf, n)
    ranked = sorted(shallow, key=key_fn)

    selected, selected_set = [], set()
    for n in ranked:
        selected.append(n); selected_set.add(n)
        if len(selected) == desired_count:
            break

    if len(selected) < desired_count:
        for n in sorted(all_metrics, key=key_fn):
            if n not in selected_set:
                selected.append(n)
                if len(selected) == desired_count:
                    break

    return {n: all_metrics[n] for n in selected}

def _pick_k_sqrt(num_funcs: int, *, scale: float = 1.0, min_k: int = 10, max_k: int = 50) -> int:
    k = int(math.sqrt(num_funcs) * scale)
    return max(min_k, min(k, max_k, num_funcs))

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