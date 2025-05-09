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
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}

    for oid in oid_list:
        call_map = api.retrieve("call_mapping", oid)
        if call_map != None:
            result = create_graph(call_map)
            if result != None:
                results[oid] = result
        
    return results

#Generating our call graph from the database
def create_graph(call_dict):
    graph = nx.DiGraph()
    # 1) collect every function offset (as caller or callee)
    all_funcs = set(call_dict.keys()) | {c for info in call_dict.values() for c in info['calls_to']}
    # 2) add them as isolated nodes
    graph.add_nodes_from(all_funcs)
    # 3) then add edges
    for caller, info in call_dict.items():
        for callee in info['calls_to']:
            graph.add_edge(caller, callee)
    return graph

