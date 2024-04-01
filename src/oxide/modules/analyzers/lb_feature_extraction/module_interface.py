""""
Copyright 2023 National Technology & Engineering Solutions",
of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS,",
the U.S. Government retains certain rights in this software.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
"""

DESC = "Performs feature extraction on binary extracting features relevant to conditional statements."
NAME = "lb_feature_extraction"

# imports
import logging

import angr

from typing import Dict, Any, List
from core.libraries.angr_utils import init_angr_project

from function_lib import (
    sensitive_functions,
    system_input_checks,
    pthread_funcs,
    functions_ignore,
)

import networkx as nx

from oxide.core import api

from findBranches import computeBranch, compareBranches

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    """Documentation for this module
    private - Whether module shows up in help
    set - Whether this module accepts collections
    atomic - TBD
    """
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """Entry point for analyzers, these do not store in database
    these are meant to be very quickly computed things passed along
    into other modules
    """
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    opts = {}

    for oid in oid_list:
        triggerResults = {}
        # Collect information and objects used for backwards slicing
        f_name, header = configure_bs(oid)
        if f_name == False or header == False:
            continue
        p = init_angr_project(f_name, header)
        base_addr = header.image_base

        # Pull disasm and basic_block module results
        disasm = api.retrieve("ghidra_disasm", oid)
        bbs = api.retrieve("basic_blocks", oid, opts)[oid]
        acid = api.retrieve("acid", oid)[oid]
        call_graph = api.retrieve("call_graph", oid)[oid]

        if disasm != None:
            functions = disasm["functions"]
        else:
            continue

        triggers = getTriggers(bbs)

        # Iterate through each function found in executable.
        for function in functions:
            functionName = functions[function]["name"]
            if (
                functionName.startswith("_")
                or functionName.startswith("__")
                or functionName in functions_ignore
            ):
                pass
            else:
                # Pull information relevant to current function.
                functionTriggers = {}

                functionBlocks = functions[function]["blocks"]
                commonBlocks = getCommonBlocks(bbs, functionBlocks)

                # Iterate through blocks in function
                for block in functionBlocks:
                    suspicous_triggers = []
                    if block in triggers:
                        branches = computeBranch(block, bbs, functionBlocks)

                        if len(branches) == 3:
                            functionTriggers[block] = {}
                            branchA = {}
                            branchB = {}

                            branchA, branchB = compareBranches(branches, commonBlocks)

                            # Returns a dictionary of function calls as well as capa results for each function
                            A_function_calls = getFunctionCalls(branchA, bbs, acid, functionBlocks, call_graph)
                            B_function_calls = getFunctionCalls(branchB, bbs, acid, functionBlocks, call_graph)

                            # Feature Extraction A
                            S_A = len(SensOperations(A_function_calls))
                            FC_A = len(totalFunctionCalls(A_function_calls))
                            M1_A = len(exclFunctCalls(A_function_calls, bbs))
                            S1_A = len(ExclSensFunctCalls(A_function_calls, bbs, acid))

                            # Feature Extraction B
                            S_B = len(SensOperations(B_function_calls))
                            FC_B = len(totalFunctionCalls(B_function_calls))
                            M1_B = len(exclFunctCalls(B_function_calls, bbs))
                            S1_B = len(ExclSensFunctCalls(B_function_calls, bbs, acid))

                            # Behavior Difference
                            branchDifference = behaviorDifference(A_function_calls, B_function_calls)

                            functionTriggers[block]["Sensitive Operations"] = S_A + S_B
                            functionTriggers[block]["Function Calls"] =  FC_A + FC_B
                            functionTriggers[block]["Exclusive Function Calls"] = M1_A + M1_B
                            functionTriggers[block]["Sensitive Opartions inside Exclusive Function Calls"] = S1_A + S1_B
                            functionTriggers[block]["Jaccard Distance"] = branchDifference

                            # Determine source of variables used in trigger stmt
                            # bs_chosen_statements = backward_slicing(p, block, base_addr)
                            # for bs_block in bs_chosen_statements:
                            #     if bs_block in disasm['functions']:
                            #         bs_name = disasm['functions'][bs_block]['name']
                            #         if bs_name in system_input_checks:
                            #             print(bs_name)
                            #             suspicous_triggers.append(bs_block)
                            # if len(suspicous_triggers) == 0:
                            #     functionTriggers[block]["Backward Slicing"] = 0
                            # else:
                            #     functionTriggers[block]["Backward Slicing"] = 1

                if len(functionTriggers) != 0:
                    triggerResults[functionName] = functionTriggers
        results[oid] = triggerResults
    return results


##########################
### Feature Extraction ###
##########################


def backward_slicing(p, block, base_addr):
    cfg = p.analyses.CFGEmulated(keep_state=True,state_add_options=angr.sim_options.refs, context_sensitivity_level=2)
    
    cdg = p.analyses.CDG(cfg)
    ddg = p.analyses.DDG(cfg)
    location = int(hex(base_addr + block), base=16)
    target_node = cfg.get_any_node(location)
    bs = p.analyses.BackwardSlice(cfg, cdg=cdg, ddg=ddg, targets=[ (target_node, 0) ], control_flow_slice=True)
    return bs.chosen_statements

def SensOperations(function_calls):
    sensitive_operations = []
    for call in function_calls:
        sensitive_operations.extend(function_calls[call]["sensitive_operations"])
    return sensitive_operations

def totalFunctionCalls(function_calls):
    all_function_calls = []
    for call in function_calls:
        all_function_calls.extend(function_calls[call]['reachable_nodes'])
    return all_function_calls

def exclFunctCalls(function_calls, bbs):
    all_function_calls = []
    for call in function_calls:
        for node in function_calls[call]['reachable_nodes']:
            if len(bbs[node]["dests_prev"]) == 1:
                all_function_calls.append(node)
    return all_function_calls

def ExclSensFunctCalls(function_calls, bbs, acid):
    sensitveOperations = []
    for call in function_calls:
        for node in function_calls[call]['reachable_nodes']:
            if len(bbs[node]["dests_prev"]) == 1:
                if node in acid['functions']:
                    sensitveOperations.extend(acid['functions'][node])
    return sensitveOperations

def behaviorDifference(A_function_calls, B_function_calls):
    A_sens_opperations = SensOperations(A_function_calls)
    B_sens_opperations = SensOperations(B_function_calls)

    # Calculate jaccard distance for two branches
    branchDifference = jaccard_distance(A_sens_opperations, B_sens_opperations)

    return branchDifference


###############################################
### Functions Supporting Feature Extraction ###
###############################################


def jaccard_distance(A, B):
    # Find symmetric difference of two sets
    nominator = list(set(A).symmetric_difference(set(B)))

    # Find union of two sets
    denominator = list(set(A) | set(B))
    if len(denominator) == 0:
        distance = 0
    else:
        distance = len(nominator) / len(denominator)

    return distance


def getFunctionCalls(branch, bbs, acid, function_blocks, call_graph):
    calls = {}
    for block in branch:
        if isinstance(block, str):
            pass
        else:
            last_insn = bbs[block]["last_insn"]
            if isCall(last_insn[1]):
                dests = bbs[block]['dests']
                for d in dests:
                    if d in function_blocks:
                        pass
                    else:
                        calls[d] = {}
                        reachable_nodes = nx.single_source_shortest_path_length(call_graph, d).keys()
                        calls[d]['reachable_nodes'] = reachable_nodes
                        calls[d]["sensitive_operations"] = []
                        for node in reachable_nodes:
                            if node in acid['functions']:
                                calls[d]["sensitive_operations"].extend(acid['functions'][node])
    return calls


def getTriggers(bbs):
    triggers = {}
    for b in bbs:
        dests = bbs[b]["dests"]
        if len(dests) > 1:
            if isCall(bbs[b]["last_insn"][1]):
                pass
            else:
                triggers[b] = bbs[b]
    return triggers

def configure_bs(oid):
    src = api.source(oid)
    data = api.get_field(src, oid, "data", {})
    src_type = api.get_field("src_type", oid, "type")
    header = api.get_field("object_header", oid, oid)
    if not header:
        logger.info("No header found for %s in %s", oid, NAME)
        return False, False
    header.type = src_type
    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data)
    return f_name, header


def getCommonBlocks(bbs, functionBlocks):
    # Get common blocks
    commonBlocks = []
    for fb in functionBlocks:
        if fb in bbs and len(bbs[fb]["dests_prev"]) > 1:
            commonBlocks.extend([fb])
    return commonBlocks


def isCall(instruction):
    if instruction.startswith("call"):
        return True
    else:
        return False
