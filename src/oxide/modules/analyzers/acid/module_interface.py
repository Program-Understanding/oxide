DESC = " This module will take a call_graph along with capa_descriptions to generate better function descriptions for certain subgraphs"
NAME = "new_acid"

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
        capa_descriptions = api.retrieve("capa_results", oid)[oid]

        if call_mapping != {} and capa_descriptions != {}:
            call_mapping = assign_descriptions(call_mapping, capa_descriptions)
            results[oid] = call_mapping
    return results


def assign_descriptions(call_mapping, capa_descriptions):
    results = {}
    call_mapping = assignDescriptionsToNodes(call_mapping, capa_descriptions)
    call_mapping = retrieve_func_call_desc(call_mapping)
    results['Subgraphs'], results['All Descriptions'] = descriptions(call_mapping)
    return results


def assignDescriptionsToNodes(call_mapping, capa_descriptions):
    for capa_description in capa_descriptions["capa_capabilities"]:
        for node in call_mapping:
            if node in capa_descriptions["capa_capabilities"][capa_description]:
                if "description" not in call_mapping[node]:
                    call_mapping[node]["description"] = [capa_description]

                else:
                    call_mapping[node]["description"].append(capa_description)

    for node in call_mapping:
        if "description" not in call_mapping[node]:
            call_mapping[node]["description"] = []

    return call_mapping


def retrieve_func_call_desc(call_mapping):
    for node in call_mapping:
        for call_to in call_mapping[node]['calls_to']:
            call_mapping[node]['calls_to'][call_to] = call_mapping[call_to]['description']
    return call_mapping

def descriptions(call_mapping):
    results = {}
    subgraphs = {}
    for parent_node in call_mapping:
        if call_mapping[parent_node]['calls_to'] == {}:
            pass
        else:
            for addr in call_mapping[parent_node]['calls_to']:
                for capability in call_mapping[parent_node]['calls_to'][addr]:
                    if parent_node in subgraphs:
                        subgraphs[parent_node].append(capability)
                    else:
                        subgraphs[parent_node] = [capability]
                    if parent_node in results:
                        results[addr].append(capability)
                    else:
                        results[addr] = [capability]

    for sg in subgraphs:
        for rule in rule_groupings:
            if subgraphs[sg] != []:
                # Find which strings from the list exist as values in the dictionary
                existing_strings = [value for value in rule_groupings[rule] if value in subgraphs[sg]]
                if len(existing_strings) >= 2:
                    description = {}
                    rule_desc = {}
                    matches = {}
                    for capabilities in call_mapping[sg]['calls_to']:
                        for c in call_mapping[sg]['calls_to'][capabilities]:
                            if c in existing_strings:
                                matches[capabilities] = call_mapping[sg]['calls_to'][capabilities]
                    description["Description Generated From Offsets"] = matches
                    rule_desc[rule] = description
                    if sg in results:
                        results[sg].append(rule_desc)
                    else:
                        results[sg] = [rule_desc]
    
    return subgraphs, results