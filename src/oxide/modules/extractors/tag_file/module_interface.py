import logging
from typing import Any, Dict, Optional, List
from collections import deque

import networkx as nx
from llm_service import runner
from oxide.core import api, progress
import textwrap

logger = logging.getLogger(__name__)

# Module metadata
DESC = """Uses an LLM to generate a tag for a given file"""
NAME = "tag_file"
CATEGORY = ""

# Options documentation
opts_doc = {}


def documentation() -> Dict[str, Any]:
    """
    Returns module documentation including description, available options, and flags.
    """
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
        "category": CATEGORY,
    }


def process(oid: str, opts: Dict[str, Any]) -> bool:
    """
    Extracts call-graph, finds influential functions, generates tags via LLM, and stores results.
    """
    logger.debug("Starting process for OID: %s", oid)

    call_graph: nx.DiGraph = api.get_field("call_graph", oid, oid)
    depth_cache = _compute_depth_cache(call_graph)
    scc_dag = _build_scc_dag(call_graph)
    bottom_up_sccs = reversed(list(nx.topological_sort(scc_dag)))
    influential = _get_influential_nodes(call_graph, depth_cache)

    results: Dict[str, Dict[str, Any]] = {"functions": {}, "influential functions": {}}
    influential_tags = []

    # Make sure we can get decompilation for the file
    decmap = api.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if decmap is None:
        results['functions'] = None
        results["influential functions"] = None
        api.store(NAME, oid, results, opts)
        return False
    
    p = progress.Progress(call_graph.number_of_nodes())

    for scc in bottom_up_sccs:
        for node in sorted(scc):
            if not _is_valid_function(oid, node):
                p.tick(); continue

            name = _get_function_name(oid, node)
            entry = {"offset": node}
            entry.update(_metrics(call_graph, depth_cache, node))
            tag = api.retrieve("tag_function_context", oid, {"func_name": name})
            if tag:
                entry["tag"] = tag
            else:
                results['functions'][name] = "FAILED"
                p.tick(); continue

            if node in influential:
                results["influential functions"][name] = entry
                influential_tags.append(entry["tag"])
            else:
                results["functions"][name] = entry
            p.tick()

    results['file overview'] = tag_file_summary(influential_tags)
    api.store(NAME, oid, results, opts)
    logger.debug("Finished processing OID: %s", oid)
    return True


def _get_function_name(oid: str, offset: Any) -> Optional[str]:
    """
    Retrieves the human-readable name of a function from disassembly metadata.
    """
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    return funcs.get(offset, {}).get("name")


def _is_valid_function(oid: str, offset: Any, min_instructions: int = 5) -> bool:
    """
    Determines if a function has at least min_instructions instructions.
    """
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    orig_blocks = api.get_field("ghidra_disasm", oid, "original_blocks") or {}
    block_ids = funcs.get(offset, {}).get("blocks", [])
    total_instrs = sum(len(orig_blocks.get(bid, [])) for bid in block_ids)
    return total_instrs >= min_instructions


def _metrics(
    graph: nx.DiGraph,
    depth_cache: Dict[Any, int],
    node: Any,
    min_out: int = 8,
    min_ratio: float = 7.0,
    max_depth: Optional[int] = 4,
) -> Dict[str, Any]:
    """
    Computes fan-in, fan-out, ratio, depth, and score for a given node.
    """
    fi = graph.in_degree(node)
    fo = graph.out_degree(node)
    ratio = (fo + 1) / (fi + 1)
    depth = depth_cache.get(node)
    score = fo * ratio

    return {"fan-in": fi, "fan-out": fo, "ratio": ratio, "depth": depth, "score": score}


def _get_influential_nodes(
    graph: nx.DiGraph,
    depth_cache: Dict[Any, int],
    min_out: int = 8,
    min_ratio: float = 7.0,
    max_depth: Optional[int] = 4,
    top: Optional[int] = None,
) -> Dict[Any, Dict[str, Any]]:
    """
    Returns nodes exceeding thresholds on fan-out, ratio, and depth, optionally returning top N by score.
    """
    candidates = {}
    for node in graph.nodes:
        metrics = _metrics(graph, depth_cache, node)
        if metrics["fan-out"] < min_out or metrics["ratio"] < min_ratio:
            continue
        if max_depth is not None and metrics["depth"] is not None and metrics["depth"] > max_depth:
            continue
        candidates[node] = metrics

    if top and len(candidates) > top:
        ranked = sorted(candidates, key=lambda n: (-candidates[n]["score"], -candidates[n]["fan-out"]))[:top]
        candidates = {n: candidates[n] for n in ranked}

    return candidates


def _build_scc_dag(graph: nx.DiGraph) -> nx.DiGraph:
    """
    Builds a DAG of strongly-connected components for topological traversal.
    """
    sccs = [frozenset(c) for c in nx.strongly_connected_components(graph)]
    func_to_scc = {node: scc for scc in sccs for node in scc}
    dag = nx.DiGraph()
    dag.add_nodes_from(sccs)

    for u, v in graph.edges():
        su, sv = func_to_scc[u], func_to_scc[v]
        if su != sv:
            dag.add_edge(su, sv)
    return dag


def _compute_depth_cache(graph: nx.DiGraph) -> Dict[Any, int]:
    """
    Computes shortest-path depth from root nodes in a directed graph.
    """
    roots = [n for n, d in graph.in_degree() if d == 0]
    depth_cache: Dict[Any, int] = {r: 0 for r in roots}
    queue = deque(roots)

    while queue:
        u = queue.popleft()
        for v in graph.successors(u):
            if v not in depth_cache:
                depth_cache[v] = depth_cache[u] + 1
                queue.append(v)
    return depth_cache


def tag_file_summary(excl_tags: List, temperature: float = 0.1, max_new_tokens: int = 1000) -> str:
    """
    Prompt LLM with root decomp and descendant tags; generate N candidate tags (tag, justification) by sampling the model.
    """
    tag_block = "\n".join(sorted(excl_tags)) or "<no exclusive descendants>"
    prompt = textwrap.dedent(f"""
FUNCTION TAGS:
{tag_block}

─────────────────────────────────────────────────────────
TASK:
1. Group tags into highly specific buckets capturing firmware capabilities.
    • Avoid broad, generic labels (e.g., \"General\", \"Miscellaneous\").
    • Aim for granular buckets focusing on distinct firmware tasks or functionality.
    • **Preserve each tag exactly as provided; do not extract or abbreviate tags.**
    • **Sort each full tag verbatim into the appropriate bucket.**
2. For each bucket:
   a. Provide a precise, action-oriented title (2-6 words, Title Case).
   b. List all member tags exactly as provided.
   c. Write a concise, detailed rationale (≤ 15 words) clearly explaining the commonality among tags.
3. After the buckets, provide a one-sentence, detailed summary explicitly stating the firmware's main role 
   based on the identified bucket functionalities.

─────────────────────────────────────────────────────────
OUTPUT FORMAT:
Follow this JSON-like schema (valid JSON not required):

  buckets:
      "name": "<Specific Bucket 1 Title>",
      "tags": ["<tag>", "<tag>", ...],
      "rationale": "<detailed sentence>"
    ...
      "name": "<Specific Bucket n Title>",
      "tags": ["<tag>", "<tag>", ...],
      "rationale": "<detailed sentence>"
  file_summary: "<detailed one-sentence summary>"

""").strip()
    # Call the model
    response = runner.generate(
        user_input=prompt,
        temperature=temperature,
        max_new_tokens=max_new_tokens
    )

    return response