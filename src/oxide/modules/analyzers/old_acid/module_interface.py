DESC = " This module will take a call_graph along with capa_descriptions to generate better function descriptions for certain subgraphs"
NAME = "old_acid"

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
        print("File: ", count)
        count += 1
        call_graph = api.retrieve("call_graph", oid)
        capa_descriptions = api.retrieve("capa_results", oid)[oid]

        if call_graph != {} and capa_descriptions != {}:
            for oid, graph in call_graph.items():
                new_descriptions, count_of_subgraph_appearances = subgraph_descriptions(graph, capa_descriptions)
                result = {
                    "All Descriptions": new_descriptions,
                    "Count of Subgraph Appearances": count_of_subgraph_appearances,
                }
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
        elementA = combination["grouping"][0]
        elementB = combination["grouping"][1]
        location = combination['location']
        if (elementA != "No description available" and elementB != "No description available"):
            description_combo = elementA + " and " + elementB

            if description_combo not in count_of_subgraph_appearances:
                count_of_subgraph_appearances[description_combo] = {}
                count_of_subgraph_appearances[description_combo]["count"] = 1
                count_of_subgraph_appearances[description_combo]["locations"] = [location]

            else:
                count_of_subgraph_appearances[description_combo]["count"] += 1
                count_of_subgraph_appearances[description_combo]["locations"].append(location)

    return count_of_subgraph_appearances


def addOldDescriptions(call_graph, new_descriptions):
    for node in call_graph.nodes:
        if (node not in new_descriptions and call_graph.nodes[node]["description"] != "No description available"):
            new_descriptions[node] = call_graph.nodes[node]["description"]

    return new_descriptions


def assignDescriptionsToNodes(call_graph, capa_descriptions):
    for capa_description in capa_descriptions["capa_capabilities"]:
        for node in call_graph.nodes:
            if node in capa_descriptions["capa_capabilities"][capa_description]:
                if "description" not in call_graph.nodes[node]:
                    call_graph.nodes[node]["description"] = [capa_description]

                else:
                    call_graph.nodes[node]["description"].append(capa_description)

    for node in call_graph.nodes:
        if "description" not in call_graph.nodes[node]:
            call_graph.nodes[node]["description"] = "No description available"

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
                        adjacent_nodes[node].append([data[0], data[1]["description"]])

    subgraphs = {}
    for node in adjacent_nodes:
        subgraphs[node] = []
        for adjacent_node in list(adjacent_nodes[node]):
            for second_adjacent_node in list(adjacent_nodes[node]):
                if adjacent_node != second_adjacent_node:
                    if isinstance(adjacent_node[1], list) and isinstance(second_adjacent_node[1], list):
                        for description in adjacent_node[1]:
                            for second_description in second_adjacent_node[1]:
                                subgraphs[node].append(
                                    [
                                        [adjacent_node[0], description],
                                        [second_adjacent_node[0], second_description],
                                    ]
                                )

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
                subgraph_combo = {"grouping": [], "location": None}
                if (grouping[0][1] in rule_groupings[rule_grouping]and grouping[1][1] in rule_groupings[rule_grouping]and grouping[0][1] != grouping[1][1]):
                    generated_from = {
                        "Description Generated From Offsets": [
                            grouping[0][0],
                            grouping[1][0],
                        ]
                    }

                    if subgraph not in new_descriptions:
                        new_descriptions[subgraph] = [{rule_grouping: generated_from}]

                    elif rule_grouping not in new_descriptions[subgraph]:
                        new_descriptions[subgraph].append({rule_grouping: generated_from})

            if (grouping[0][1] != "No description available" and grouping[1][1] != "No description available"):
                subgraph_combo["grouping"] = [grouping[0][1], grouping[1][1]]
                subgraph_combo["location"] = subgraph
                combination_of_subgraph_descriptions.append(subgraph_combo)

    return new_descriptions, combination_of_subgraph_descriptions