DESC = ""
NAME = "mcp_control_flow_graph"
CATEGORY = ""

import logging

from typing import Dict, Any

from oxide.core import api

import networkx as nx
import json
from collections import defaultdict

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {'function_name': {'type': str, 'mangle': True, 'default': 'None'},
            'function_offset': {'type': str, 'mangle': True, 'default': 'None'}}

def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY}

def process(oid: str, opts: dict) -> bool:
    logger.debug("process()")
    result = {}
    functions = api.get_field("ghidra_disasm", oid, "functions")

    if functions is None: return False

    function_name = opts['function_name']
    function_offset = opts['function_offset']

    if function_offset != 'None':
        func_addr = function_offset
        func_data = functions[func_addr]
        func_name = func_data['name']
        cfg = get_func_cfg(oid, func_addr)
        # Get the CFG for the function; skip if not available.
        if cfg:
            cfg = cfg_to_llm_json(cfg, func_name)
            result = cfg

    elif function_name != 'None':
        for func_addr, func_data in functions.items():
            if func_data['name'] == function_name:
                func_name = func_data['name']
                cfg = get_func_cfg(oid, func_addr)
                # Get the CFG for the function; skip if not available.
                if cfg:
                    cfg = cfg_to_llm_json(cfg, func_name)
                    result = cfg
    
    else:
        for func_addr, func_data in functions.items():
            # Get the CFG for the function; skip if not available.
            cfg = get_func_cfg(oid, func_addr)
            if cfg:
                cfg = cfg_to_llm_json(cfg, func_name=str(func_addr))
                result[func_addr] = cfg
    
    if not result:
        return False
    api.store(NAME, oid, result, opts)
    return True

def cfg_to_llm_json(bb_graph: nx.DiGraph, func_name: str = "unknown_function") -> str:
    data = {
        "name": func_name,
        "nodes": {},
        "edges": []
    }
    
    for node in bb_graph.nodes():
        # Retrieve the instructions along with other attributes, if needed
        instructions = bb_graph.nodes[node].get("instructions", [])
        data["nodes"][str(node)] = {}
        for offset, instr in instructions:
            data["nodes"][str(node)][offset] = instr

    targets_by_source = defaultdict(list)
    for u, v in bb_graph.edges():
        targets_by_source[u].append(str(v))
    data["edges"] = targets_by_source
    
    return json.dumps(data, indent=5)


def cfg_to_networkx(block_map: dict, bb_features: dict = None) -> nx.DiGraph:
    """
    Convert a canonical basic block graph into a NetworkX directed graph,
    attaching each instruction from the basic blocks to the corresponding node.

    Args:
        block_map (dict): Mapping of block identifiers to their data. Each value 
                          should contain at least the keys "dests" (for edge destinations)
                          and "members" (a list of tuples for instructions).
        bb_features (dict, optional): Mapping of block identifiers to additional
                                      feature dictionaries to attach to nodes.

    Returns:
        nx.DiGraph: Directed graph representing the control flow graph with instructions.
    """
    bb_graph = nx.DiGraph()

    # Iterate over the blocks and add each as a node
    for block, data in block_map.items():
        if block == "meta":  # Skip metadata if present
            continue

        # Extract the instructions from "members" (each instruction is typically a tuple like (address, instruction))
        instructions = data.get("members", [])
        # Here you could also process the instruction tuple further if needed (for example, converting to a string).

        # Add node with an 'instructions' attribute
        bb_graph.add_node(block, instructions=instructions)
    
    # Add edges between basic blocks based on the "dests" field
    for block, data in block_map.items():
        if block == "meta":
            continue

        for dest in data.get("dests", []):
            bb_graph.add_edge(block, dest)

    # Optionally, add more features to nodes if provided
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