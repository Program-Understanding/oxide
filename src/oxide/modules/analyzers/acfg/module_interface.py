DESC = ""
NAME = "acfg"

import networkx as nx
import logging
from typing import Dict, Any, List

from core import api
import networkx as nx
import itertools

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
        results[oid] = {}
        original_blocks = api.get_field("ghidra_disasm", oid, "original_blocks")
        functions = api.get_field("ghidra_disasm", oid, "functions")
        function_calls = api.retrieve("function_calls", oid)
        graph = _cfg_to_networkx(original_blocks)
        betweeness_dict = nx.betweenness_centrality(graph, normalized=True, endpoints=True)

        for f in functions:
            results[oid][f] = {}
            basic_blocks = functions[f]['blocks']
            for bb in basic_blocks:
                block_features = {}
                block_features["num_offsprings"] = len(original_blocks[bb]['dests'])
                block_features['betweenness'] = betweeness_dict[bb]
                block_features['string_constants'] = None
                block_features['numeric_constants'] = None
                block_features['num_transfer_instructions'] = _num_transfer_instructions(original_blocks[bb])
                block_features['num_function_calls'] = _num_function_calls(function_calls, original_blocks[bb])
                block_features['num_instructions'] = len(original_blocks[bb]['members'])
                block_features['num_arithmetic_instructions'] = _num_arithmetic_instructions(original_blocks[bb])
                results[oid][f][bb] = block_features
        
    return results



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

def _num_function_calls(function_calls: dict, bb: dict):
    num_function_calls = 0

    for insr in bb['members']:
        if insr[0] in function_calls:
            num_function_calls += 1

    return num_function_calls

def _num_arithmetic_instructions(bb):
    num_arithmetic_instructions = 0

    for insr in bb['members']:
        i = insr[1].split(' ', 1)[0]
        if i in x86_arithmetic_instructions:
            num_arithmetic_instructions += 1
        elif i in mips_arithmetic_instructions:
            num_arithmetic_instructions += 1

    return num_arithmetic_instructions

def _num_transfer_instructions(bb):
    num_transfer_instructions = 0

    for insr in bb['members']:
        i = insr[1].split(' ', 1)[0]
        if i in x86_transfer_instruction:
            num_transfer_instructions += 1

    return num_transfer_instructions

x86_arithmetic_instructions = ["add", "sub", "mul", "imul", "div", "idiv", "neg", "adc", "sbb", "inc", "dec"]
mips_arithmetic_instructions = ["add", "sub", "addu", "subu", "mult", "multu", "div", "divu", "mfhi", "mflo", "mul", "and", "or", "nor", "xor", "addi", "addiu", "andi", "ori", "xori", "sll", "srl", "sra", "sllv", "srlv", "srav"]
arm_arithmetic_instructions = []

x86_transfer_instruction = ["mov", "xchg", "cmpxchg", "movz", "movzx", "movs", "movsx", "movsb", "movsw", "lea", "cmovcc"]