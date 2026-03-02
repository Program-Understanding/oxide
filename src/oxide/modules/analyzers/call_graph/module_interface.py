DESC = " This module will create a call graph for the given object. It will return a networkX graph object."
NAME = "call_graph"

# imports
import networkx as nx
import logging
from typing import Dict, Any, List

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    """ Documentation for this module
        private - Whether module shows up in help
        set - Whether this module accepts collections
        atomic - TBD
    """
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True}


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """ Entry point for analyzers, these do not store in database
        these are meant to be very quickly computed things passed along
        into other modules
    """
    logger.debug("results()")

    oid_list = api.expand_oids(oid_list)
    graphs: Dict[str, nx.DiGraph] = {}

    for oid in oid_list:
        functions = api.get_field("ghidra_disasm", oid, "functions")
        basic_blocks = api.get_field("ghidra_disasm", oid, "original_blocks")

        graph = None
        if functions and basic_blocks:
            graph = build_call_graph_from_disasm(functions, basic_blocks)

        if graph is None or graph.number_of_nodes() == 0:
            call_map = api.retrieve("function_call_targets", oid)
            if not call_map:
                continue
            graph = build_call_graph(call_map)

        graphs[oid] = graph

    return graphs


def _to_int(value: Any) -> int | None:
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        try:
            return int(value, 0)
        except ValueError:
            return None
    return None


def _get_block_info(basic_blocks: Dict[Any, Any], block_addr: Any) -> Dict[str, Any] | None:
    if block_addr in basic_blocks:
        return basic_blocks[block_addr]

    if isinstance(block_addr, int):
        as_str = str(block_addr)
        if as_str in basic_blocks:
            return basic_blocks[as_str]
    elif isinstance(block_addr, str):
        as_int = _to_int(block_addr)
        if as_int is not None and as_int in basic_blocks:
            return basic_blocks[as_int]

    return None


def _first_block_id(blocks: List[Any]) -> int | None:
    for block in blocks:
        as_int = _to_int(block)
        if as_int is not None:
            return as_int
    return None


def build_call_graph_from_disasm(functions: Dict[Any, Any], basic_blocks: Dict[Any, Any]) -> nx.DiGraph:
    """
    Build a function-level call graph using ghidra_disasm output.
    This keeps imported/external function names when available.
    """
    graph = nx.DiGraph()

    functions_by_key: Dict[Any, Dict[str, Any]] = {}
    functions_by_int_key: Dict[int, Dict[str, Any]] = {}

    for func_key, func_info in functions.items():
        if func_key == "meta" or not isinstance(func_info, dict):
            continue

        func_name = str(func_info.get("name") or func_key)
        blocks = func_info.get("blocks", [])
        block_id = _first_block_id(blocks)
        graph.add_node(func_name, function_name=func_name, block_id=block_id)

        record = {
            "name": func_name,
            "blocks": blocks,
            "block_id": block_id,
        }
        functions_by_key[func_key] = record

        as_int = _to_int(func_key)
        if as_int is not None:
            functions_by_int_key[as_int] = record

    if not functions_by_key:
        return graph

    for func_key, func_info in functions_by_key.items():
        caller_name = func_info["name"]
        for block_addr in func_info.get("blocks", []):
            block_info = _get_block_info(basic_blocks, block_addr)
            if not block_info:
                continue

            for dest in block_info.get("dests", []):
                callee = functions_by_key.get(dest)
                if callee is None:
                    as_int = _to_int(dest)
                    if as_int is not None:
                        callee = functions_by_int_key.get(as_int)

                if callee is None:
                    continue

                callee_name = callee["name"]
                if caller_name != callee_name:
                    graph.add_edge(caller_name, callee_name)

    return graph

def build_call_graph(call_map: Dict[str, List[str]]) -> nx.DiGraph:
    """
    Given call_map where keys are callers and values are lists of callees,
    return a NetworkX DiGraph of the call relationships.
    """
    G = nx.DiGraph()
    for caller, callees in call_map.items():
        G.add_node(caller)   # ensures caller exists even if no outgoing edges
        for callee in callees:
            G.add_edge(caller, callee)
    return G
