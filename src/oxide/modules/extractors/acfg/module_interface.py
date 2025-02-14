DESC = ""
NAME = "acfg"
CATEGORY = ""

import logging

from typing import Dict, Any

from oxide.core import api

import networkx as nx
import numpy as np

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY}

def process(oid: str, opts: dict) -> bool:
    """
    Process the given object identifier (oid) to generate a feature vector for each function.
    
    The final feature vector for each function is the concatenation of:
      - The averaged basic block (node) features.
      - The graph-level features computed from the control flow graph (CFG).
    """
    logger.debug("process()")
    result = {}

    # Retrieve the required fields from the API
    basic_blocks = api.get_field("ghidra_disasm", oid, "original_blocks")
    functions = api.get_field("ghidra_disasm", oid, "functions")
    function_calls = api.retrieve("function_calls", oid)

    # Define the order for node and graph features
    node_feature_keys = ["num_successors", "num_predecessors", "betweenness", "num_function_calls", "num_instructions"]
    graph_feature_keys = ["density", "avg_degree", "avg_betweenness", "num_blocks", "num_edges"]

    for func_addr, func_data in functions.items():
        # Get the CFG for the function; skip if not available.
        cfg = get_func_cfg(oid, func_addr)
        if cfg is None:
            continue

        # Compute betweenness centrality for the CFG nodes (re-use later)
        betweenness = nx.betweenness_centrality(cfg, normalized=True, endpoints=True)

        # Gather basic block features for the function
        bb_features_dict = {}
        for bb in func_data.get('blocks', []):
            bb_data = basic_blocks.get(bb, {})
            bb_features_dict[bb] = {
                "num_successors": len(bb_data.get('dests', [])),
                "num_predecessors": len(bb_data.get('dests_prev', [])),
                "betweenness": betweenness.get(bb, 0),
                "num_function_calls": _num_function_calls(function_calls, bb_data),
                "num_instructions": bb_data.get('num_insts', 0)
            }
        logger.debug("Block features for function %s: %s", func_addr, bb_features_dict)

        # Skip functions that have no basic blocks
        if not bb_features_dict:
            continue

        # Convert the dictionary of basic block features into a 2D NumPy array.
        # Each row corresponds to a block's features, ordered by `node_feature_keys`.
        node_feature_list = [
            [features[key] for key in node_feature_keys]
            for features in bb_features_dict.values()
        ]
        node_feature_array = np.array(node_feature_list)

        # Compute the average of node features (i.e. a 1D vector)
        flattened_node_features = np.mean(node_feature_array, axis=0)

        # Compute graph-level features from the CFG
        graph_features = {
            "density": nx.density(cfg),
            "avg_degree": np.mean([cfg.in_degree(n) + cfg.out_degree(n) for n in cfg.nodes]),
            "avg_betweenness": np.mean(list(betweenness.values())),
            "num_blocks": cfg.number_of_nodes(),
            "num_edges": cfg.number_of_edges()
        }
        # Convert graph features into a 1D NumPy array (using a fixed order)
        graph_feature_array = np.array([graph_features[key] for key in graph_feature_keys])

        # Concatenate the averaged node features with the graph-level features
        final_feature_vector = np.concatenate((flattened_node_features, graph_feature_array))
        result[func_addr] = final_feature_vector
    if not result:
        return False

    api.store(NAME, oid, result, opts)
    return True

def cfg_to_networkx(block_map: dict, bb_features: dict = None) -> nx.DiGraph:
    """
    Convert a canonical basic block graph into a NetworkX directed graph.

    Args:
        block_map (dict): Mapping of block identifiers to their data.
        bb_features (dict, optional): Mapping of block identifiers to feature dictionaries.

    Returns:
        nx.DiGraph: Directed graph representing the control flow graph.
    """
    bb_graph = nx.DiGraph()

    # Add nodes for each basic block
    for block in block_map:
        bb_graph.add_node(block)

    # Add edges between basic blocks
    for block, data in block_map.items():
        if block == "meta":  # Skip metadata if present
            continue
        for dest in data.get("dests", []):
            bb_graph.add_edge(block, dest)

    # If provided, set node attributes for each block
    if bb_features:
        nx.set_node_attributes(bb_graph, bb_features)

    return bb_graph

def _get_function_blocks(oid: str, func_addr: str) -> dict:
    basic_blocks = api.get_field('ghidra_disasm', oid, "original_blocks")
    functions = api.get_field('ghidra_disasm', oid, "functions")
    func = functions.get(func_addr)
    if not func:
        return {}

    blocks = {}
    for bb in func.get('blocks', []):
        if bb in basic_blocks:
            blocks[bb] = basic_blocks[bb]
        # else:
        #     # Optionally, log a warning or handle the missing block as needed.
        #     print(f"Warning: Block ID {bb} not found in basic_blocks.")
    return blocks


def get_func_cfg(oid: str, func_addr: str):
    """
    Generate the control flow graph (CFG) for a given function.

    Args:
        oid (str): The object identifier.
        func_addr (str): The function address.

    Returns:
        nx.DiGraph or None: The CFG as a NetworkX graph, or None if no nodes exist.
    """
    function_bbs = _get_function_blocks(oid, func_addr)
    if not function_bbs:
        return None
    bb_graph = cfg_to_networkx(function_bbs)
    return bb_graph if bb_graph.number_of_nodes() > 0 else None

def get_func_acfg(oid: str, func_addr: str, bb_features: dict):
    """
    Generate the annotated control flow graph (ACFG) for a given function using provided basic block features.

    Args:
        oid (str): The object identifier.
        func_addr (str): The function address.
        bb_features (dict): Features for each basic block.

    Returns:
        nx.DiGraph or None: The ACFG as a NetworkX graph, or None if no nodes exist.
    """
    function_bbs = _get_function_blocks(oid, func_addr)
    if not function_bbs:
        return None
    bb_graph = cfg_to_networkx(function_bbs, bb_features)
    return bb_graph if bb_graph.number_of_nodes() > 0 else None

def _num_function_calls(function_calls: dict, bb: dict) -> int:
    """
    Count the number of function calls within a basic block.

    Args:
        function_calls (dict): A mapping of instructions that are function calls.
        bb (dict): Basic block data containing a list of instructions under the key 'members'.

    Returns:
        int: The number of function calls in the basic block.
    """
    return sum(1 for insr in bb.get('members', []) if insr[0] in function_calls)