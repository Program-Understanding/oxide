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
        call_map = api.retrieve("function_call_targets", oid)
        if not call_map:
            continue
        graphs[oid] = build_call_graph(call_map)

    return graphs

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
