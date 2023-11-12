DESC = " This module will create a call graph for the given object. It will return a networkX graph object."
NAME = "call_graph"

# imports
import networkx as nx
import matplotlib.pyplot as plt
import logging

from oxide.core import api

from typing import Dict, Any, List


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
    for caller in call_dict:
        for callee in call_dict[caller]['calls_to']:
            graph.add_edge(caller, callee)

    return graph