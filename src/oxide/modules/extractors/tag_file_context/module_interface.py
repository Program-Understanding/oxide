DESC = "Uses an LLM to generate a tag for a given function"
NAME = "tag_file_context"
CATEGORY = ""  # used for filtering of modules e.g. disassemblers like ida

import logging
from typing import Dict, List, Tuple, Any
import os
import networkx as nx   
from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"func_name": {"type": str, "mangle": True, "default": "None"},
            "n": {"type": int, "mangle": True, "default": 5}
            }

"""
options dictionary defines expected options, including type, default value, and whether
presence of option distinguishes a version of output (mangle).

An example of option
{"version": {"type": int, "mangle": True, "default": -1}
where 'version' is guarenteed to be passed into opts of process
    it has type int, with default value -1, and caching of results only relevant to this value
        template_extract --version=1 vs template_extract --version=2
    would result in running two different times
"""


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY}



def process(oid: str, opts: dict) -> bool:
    """
    Extracts a decompiled function, generates multiple tag candidates, then selects the best one.
    """
    logger.debug("process()")
    result = {}

    cg: nx.DiGraph = api.get_field("call_graph", oid, oid)

    dag, func2scc = build_scc_dag(cg)
    topo_scc      = list(nx.topological_sort(dag))      # list of SCCs

    changed = True
    while changed:
        changed = False
        for scc in topo_scc:
            for f in sorted(scc):
                func_name = get_func_name(oid, f)
                if should_reprompt_with_ctx(G, f):
                    result[f] = api.retrieve("tag_function_context", oid, {"func_name": func_name, "n": 1})


    api.store(NAME, oid, result, opts)
    return True


def build_scc_dag(G: nx.DiGraph):
    """
    Return
      * dag        –  a DiGraph whose nodes are frozensets of original functions
      * func2scc   –  dict: original node ➜ owning SCC node
    """
    # nx.strongly_connected_components returns generators of nodes
    scc_nodes  = [frozenset(c) for c in nx.strongly_connected_components(G)]
    func2scc   = {f:scc for scc in scc_nodes for f in scc}
    dag        = nx.DiGraph()

    for scc in scc_nodes:
        dag.add_node(scc)

    # add edges between SCCs (ignoring self-loops)
    for u, v in G.edges():
        su, sv = func2scc[u], func2scc[v]
        if su != sv:
            dag.add_edge(su, sv)

    return dag, func2scc

def get_func_name(oid, offset):
    functions = api.get_field("ghidra_disasm", oid, "functions")
    if functions:
        for func in functions:
            if func == offset:
                return functions[func]['name']
    return None

def get_func_name(oid, offset):
    functions = api.get_field("ghidra_disasm", oid, "functions")
    if functions:
        for func in functions:
            if func == offset:
                return functions[func]['name']
    return None