DESC = "This module incororporates feature extraction from TikNib (https://github.com/SoftSec-KAIST/TikNib)"
NAME = "tiknib_features"

import networkx as nx
import logging
from typing import Dict, Any, List

from core import api
import networkx as nx
import itertools

from cfg_features import get_cfg_features
from cg_features import get_cg_features
from asm_features import get_asm_features

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"version": {"type": int, "mangle": True, "default": -1},
           "rebase-off": {"type": bool, "mangle": True, "default": False},
            "processor": {"type": str, "mangle": True, "default": "none"}
           }


def documentation() -> Dict[str, Any]:
    """ Documentation for this module
        private - Whether module shows up in help
        set - Whether this module accepts collections
        atomic - TBD
    """
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True}


def _cfg_to_networkx(block_map: dict):
    """ Take in canonical basic block graph, and produce networkx graph from edges
        Input -
            block_map - canonical basic block dictionary, offset -> (members, dests)
        Output -
            bb_graph - networkx graph representing control flow graph
    """
    bb_graph = nx.DiGraph()
    bb_graph.add_nodes_from(block_map.keys())

    for block in block_map:
        if block == "meta":
            continue

        bb_graph.add_edges_from(itertools.product([block], block_map[block]["dests"]))

    return bb_graph


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """ Entry point for analyzers, these do not store in database
        these are meant to be very quickly computed things passed along
        into other modules
    """
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}

    processor = opts["processor"]
        
    for oid in oid_list:
        results[oid] = {}
        basic_blocks = api.get_field('ghidra_disasm', oid, "original_blocks", {"processor": processor})
        instructions = api.get_field('ghidra_disasm', oid, "instructions", {"processor": processor})
        functions = api.get_field('ghidra_disasm', oid, "functions", {"processor": processor})
        call_mapping = api.retrieve("call_mapping", oid)
        if basic_blocks != {}:
            bb_graph = _cfg_to_networkx(basic_blocks)
            cfg_features = get_cfg_features(bb_graph)
            cg_features = get_cg_features(call_mapping)
            asm_features = get_asm_features(bb_graph, instructions)
            results[oid]["cfg_features"] = cfg_features
            results[oid]["cg_features"] = cg_features
            results[oid]["asm_features"] = asm_features
            results[oid]["num_functions"] = len(functions)

        else:
            results[oid] = "None"
        
    return results