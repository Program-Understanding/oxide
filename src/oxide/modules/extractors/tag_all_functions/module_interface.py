import logging
from typing import Any, Dict, Optional, List
from collections import deque

import networkx as nx

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
    """Populate only the influential functions for oid and store it."""
    logger.debug("Starting tag-file process for %s", oid)

    call_graph: nx.DiGraph = api.get_field("call_graph", oid, oid)
    if call_graph is None or call_graph.number_of_nodes() == 0:
        return False

    # Ensure decompilation is available before we begin
    decmap = api.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if decmap is None:
        return False

    # Prepare to collect tags
    results: Dict[str, Any] = {'func_tags': {}, "total_gpu_time_sec": 0}
    p = progress.Progress(call_graph.number_of_nodes())

    # Walk the call-graph bottom-up (post-order: callees before callers)
    for node in nx.dfs_postorder_nodes(call_graph):
        p.tick()

        # Skip very small functions, if desired
        if not _is_valid_function(oid, node):
            continue

        # Resolve a human-readable name
        func_result = api.retrieve("llm_function_analysis", oid, {"func_offset": node, "prompt": "tag"})
        results['func_tags'][node] = func_result['tag']
        results['total_gpu_time_sec'] += func_result['gpu_time_sec']

    # Store all collected tags in one shot
    api.store(NAME, oid, results, opts)
    logger.debug("Finished tag-file process for %s", oid)
    return True

def _is_valid_function(oid: str, offset: Any, min_instructions: int = 5) -> bool:
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    orig_blocks = api.get_field("ghidra_disasm", oid, "original_blocks") or {}
    blk_ids = funcs.get(offset, {}).get("blocks", [])
    total_instr = sum(len(orig_blocks.get(bid, [])) for bid in blk_ids)
    return total_instr >= min_instructions