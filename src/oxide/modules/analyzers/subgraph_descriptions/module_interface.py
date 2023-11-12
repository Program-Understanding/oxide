DESC = " This module will take a call_graph along with capa_descriptions to generate better function descriptions for certain subgraphs"
NAME = "subgraph_descriptions"

# imports
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
        call_graph = api.retrieve("call_graph", oid)
        capa_descriptions = api.retrieve("capa_match", oid, oid)
        if call_graph != {} and capa_descriptions != {}:
            for oid, graph in call_graph.items():
                new_descriptions, count_of_subgraph_appearances = subgraph_descriptions(graph, capa_descriptions)
                result = {'All Descriptions': new_descriptions, 'Count of Subgraph Appearances': count_of_subgraph_appearances}
            results[oid] = result
            
    return results


def subgraph_descriptions(call_graph, capa_descriptions):
    call_graph = assignDescriptionsToNodes(call_graph, capa_descriptions)
    subgraphs = getSubgraphs(call_graph)
    new_descriptions, all_descriptions_combinations = finding_relationships(subgraphs)
    new_descriptions = addOldDescriptions(call_graph, new_descriptions)
    count_of_subgraph_appearances = calculateTimesASubgraphAppears(all_descriptions_combinations)
    return new_descriptions, count_of_subgraph_appearances


def calculateTimesASubgraphAppears(all_descriptions_combinations):
    count_of_subgraph_appearances = {}
    for combination in all_descriptions_combinations:
        if combination[0] != 'No description available' and combination[1] != 'No description available':
            description_combo = combination[0] + ' and ' + combination[1]
            if description_combo not in count_of_subgraph_appearances:
                count_of_subgraph_appearances[description_combo] = 1
            else:
                count_of_subgraph_appearances[description_combo] += 1
    
    return count_of_subgraph_appearances



def addOldDescriptions(call_graph, new_descriptions):
    for node in call_graph.nodes:
        if node not in new_descriptions and call_graph.nodes[node]['description'] != 'No description available':
            new_descriptions[node] = call_graph.nodes[node]['description']
    
    return new_descriptions

def assignDescriptionsToNodes(call_graph, capa_descriptions):
    for capa_description in capa_descriptions:
        for node in call_graph.nodes:
            if node == capa_descriptions[capa_description]['address_found']:
                if 'description' not in call_graph.nodes[node]:
                    call_graph.nodes[node]['description'] = [capa_description]
                else:
                    call_graph.nodes[node]['description'].append(capa_description)
    
    for node in call_graph.nodes:
        if 'description' not in call_graph.nodes[node]:
            call_graph.nodes[node]['description'] = 'No description available'

    return call_graph


def getSubgraphs(call_graph):
    adjacent_nodes = {}
    for node in call_graph.nodes:
        adjacent_node = call_graph[node]
        if len(adjacent_node) > 0:
            adjacent_nodes[node] = []
            for data in call_graph.nodes.data():
                for item in adjacent_node:
                    if data[0] == item:
                        adjacent_nodes[node].append([data[0], data[1]['description']])

    subgraphs = {}
    for node in adjacent_nodes:
        subgraphs[node] = []
        for adjacent_node in list(adjacent_nodes[node]):
            for second_adjacent_node in list(adjacent_nodes[node]):
                if adjacent_node != second_adjacent_node:
                    if isinstance(adjacent_node[1], list) and isinstance(second_adjacent_node[1], list):
                        for description in adjacent_node[1]:
                            for second_description in second_adjacent_node[1]:
                                subgraphs[node].append([[adjacent_node[0], description], [second_adjacent_node[0], second_description]])
                    else:
                        subgraphs[node].append([adjacent_node, second_adjacent_node])
            adjacent_nodes[node].remove(adjacent_node)
    
    return subgraphs


def finding_relationships(subgraphs):
    new_descriptions = {}
    combination_of_subgraph_descriptions = []
    
    for subgraph in subgraphs:
        for grouping in subgraphs[subgraph]:
            for rule_grouping in rule_groupings:
                if grouping[0][1] in rule_groupings[rule_grouping] and grouping[1][1] in rule_groupings[rule_grouping]:
                    generated_from = {'Description Generated From Offsets': [grouping[0][0], grouping[1][0]]}
                    if subgraph not in new_descriptions:
                        new_descriptions[subgraph] = [{rule_grouping: generated_from}]
                    elif rule_grouping not in new_descriptions[subgraph]: 
                        new_descriptions[subgraph].append({rule_grouping: generated_from})

            if grouping[0][1] != 'No description available' and grouping[1][1] != 'No description available':
                combination_of_subgraph_descriptions.append([grouping[0][1], grouping[1][1]])

    return new_descriptions, combination_of_subgraph_descriptions
                    
                    


rule_groupings = {'Grabs a DNS and sends a HTTP Request to it':['resolve DNS', 'send HTTP request'],
                  'Sends encoded data over a socket': ['encode data using XOR', 'send data on socket'],
                  'Sends encoded data over a socket': ['encode data using Base64', 'send data on socket'],
                  'Sends encoded data over a socket': ['encode data using SHA256', 'send data on socket'],
                  'Gathering Machine Information': ['get hostname', 'get OS information', 'get number of processors', 'get networking interfaces', 'get kernel version'],
                  'Checks to see if it is already running, if it isn\'t, then it will run': ['check mutex', 'create mutex'],
                  'Remote Access': ['open network connection', 'accept command line input'],
                  'Gathering User Information': ['get session user name', 'get token membership'],
                  'Run the specified file on startup': ['write file on Windows', 'persist via Run registry key'],
                  'Creates a new file and deletes itself': ['self delete', 'write file on linux', 'write file on Windows'],
                  'Open a file and write information to it': ['write file on Linux', 'create or open file'],
                  'Finding and terminating a process': ['terminate process via kill', 'enumerate processes'],
                  'Hashing file data': ['enumerate files', 'hash data using SHA256'],
                  'Obfuscating commands': ['refrence Base64 string', 'decode Base64 string'],
                  'Gain access to a file and run it': ['change file permission on Linux', 'start process'],
                  'Pre-execution check': ['check for software breakpoints', 'get OS information'],
                  'Anti-debugging': ['check for software breakpoints', 'reference anti-VM strings targeting VMWare']
                  }