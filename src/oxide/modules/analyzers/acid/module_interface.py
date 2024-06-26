DESC = " This module will take a call_graph along with capa_descriptions to generate better function descriptions for certain subgraphs"
NAME = "acid"

# imports
import logging

from typing import Dict, Any, List

from core import api

from subgraph_rules import rule_groupings

logger = logging.getLogger(NAME)
logger.debug("init")

from typing import Any
from typing import *
from core import api

from pathlib import *

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
    count = 0
    for oid in oid_list:
        count += 1
        call_mapping = api.retrieve("call_mapping", oid)
        if call_mapping is None:
            continue
        capa_descriptions = api.retrieve("capa_results", oid)[oid]        
        ghidra_disasm = api.retrieve("ghidra_disasm", oid)

        if call_mapping != {} and capa_descriptions != {}:
            call_mapping = assign_descriptions(call_mapping, capa_descriptions, ghidra_disasm)
            results[oid] = call_mapping
    return results


def assign_descriptions(call_mapping, capa_results, ghidra_disasm):
    descriptions = setup_descriptions(call_mapping)
    descriptions = assignDescriptionsToNodes(capa_results, ghidra_disasm, descriptions)
    call_mapping = map_descriptions_on_callmap(call_mapping, descriptions)
    call_mapping = retrieve_func_call_desc(call_mapping)
    results = get_descriptions(call_mapping, descriptions, ghidra_disasm)
    return results

def setup_descriptions(call_mapping):
    descriptions = {}
    for node in call_mapping:
        descriptions[node] = []
    return descriptions

def assignDescriptionsToNodes(capa_results, ghidra_disasm, descriptions):
    for d in capa_results["capa_capabilities"]:
        for addr in capa_results["capa_capabilities"][d]:
            if addr in descriptions:
                descriptions[addr].append(d)
            else:
                func_addr = _get_function(ghidra_disasm, addr)
                if func_addr:
                    descriptions[func_addr].append(d)
                else:   
                    print("addr miss")
                    descriptions[addr] = ["addr miss: " + d]
    return descriptions

def map_descriptions_on_callmap(call_mapping, descriptions):
    for node in call_mapping:
        if node in descriptions:
            call_mapping[node]['description'] = descriptions[node]
    return call_mapping

def retrieve_func_call_desc(call_mapping):
    for node in call_mapping:
        for call_to in call_mapping[node]['calls_to']:
            call_mapping[node]['calls_to'][call_to] = call_mapping[call_to]['description']
    return call_mapping

def get_descriptions(call_mapping, descriptions, ghidra_disasm):
    results = {}
    subgraphs = {}
    functions = ghidra_disasm['functions']
    for parent_node in call_mapping:
        called_function_capabilities = []

        # Adds capbility ffom child nodes to subgraphs
        for addr in call_mapping[parent_node]['calls_to']:
            for capability in call_mapping[parent_node]['calls_to'][addr]:
                called_function_capabilities.append(capability)
        if len(called_function_capabilities) >= 2:
            subgraphs[parent_node] = {}
            subgraphs[parent_node]['capa_descriptions'] = called_function_capabilities  
            subgraphs[parent_node]['function_name'] = functions[parent_node]['name']
            subgraphs[parent_node]['acid_descriptions'] = []

    for sg in subgraphs:
        if subgraphs[sg] != []:
            for rule in rule_groupings:

                # Finds which subgraph capabilities match a capability from rule
                existing_strings = [value for value in rule_groupings[rule] if value in subgraphs[sg]['capa_descriptions']]
                # Checks if we have at least 2 matches
                if len(existing_strings) >= 2:
                    subgraph_information = {}
                    subgraph_description = {}
                    matches = {}
                    for capabilities in call_mapping[sg]['calls_to']:
                        for c in call_mapping[sg]['calls_to'][capabilities]:
                            if c in existing_strings:
                                if capabilities in matches:
                                    matches[capabilities].append(c)
                                else:
                                    matches[capabilities] = [c]
                    subgraph_description[rule] = matches
                    subgraphs[sg]['acid_descriptions'].append(subgraph_description)

    filtered_descriptions = {}
    for addr in descriptions:
        if descriptions[addr] != []:
            filtered_descriptions[addr] = descriptions[addr]


    results['subgraphs'] = subgraphs
    results['functions'] = filtered_descriptions
    return results



def _get_function(ghidra_disasm, addr):
    functions = ghidra_disasm['functions']
    for function in functions:
        if addr in functions[function]['blocks']:
            return function
    return False