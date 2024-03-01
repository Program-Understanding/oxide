""" Plugin: Prints out capa results for an oid.
"""
NAME="compare_function_tlsh_hashes"
from oxide.core import api
import tlsh
import os

# working on taking input from function_tlsh module and comparing
 #args is 1st direct args, then whats passed in thru pipe
 #opts is flags passed
def compare_function_hashes(args, opts):
    """
       Use to analyze function hashes of a collection
       Syntax: compare_function_tlsh [ --min=<minimum score> | --max=<maximum_score> | --hr | --human_readable | --condensed ]
       (Input should pipe in from function_tlsh module output)
    """
    human_readable = False
    if "hr" in opts or "human-readable" in opts:
        human_readable = True
    minimum = None
    if "min" in opts:
        minimum = opts["min"]
    maximum = None
    if "max" in opts:
        maximum = opts["max"]
    condensed = False
    if "condensed" in opts:
        condensed = True
    args_dict = dict(args[0])
    possible_oids = args_dict.keys()
    valid, invalid = api.valid_oids(possible_oids)
    similarities = {}
    if valid:
        for oid in possible_oids: #big O n^4, terrible
            if not human_readable:
                if oid in similarities:
                    continue
                similarities[oid] = {}
            for other_oid in possible_oids:
                if oid == other_oid:
                    continue
                functions = args_dict[oid].keys()
                other_functions = args_dict[other_oid].keys()
                for function in functions:
                    if "tlsh hash" not in args_dict[oid][function] or args_dict[oid][function]["tlsh hash"] is None:
                        continue
                    for other_function in other_functions:
                        if "tlsh hash" not in args_dict[other_oid][other_function] or args_dict[other_oid][other_function]["tlsh hash"] is None:
                            continue
                        score = tlsh.diff(args_dict[oid][function]["tlsh hash"],args_dict[other_oid][other_function]["tlsh hash"])
                        if (maximum and score > maximum) or (minimum and score < minimum):
                            continue
                        if not human_readable:
                            if condensed:
                                similarities[f"{oid}.{function}-{other_oid}.{other_function}"] = score
                            else:
                                if other_oid not in similarities[oid]:
                                    similarities[oid][other_oid] = {}
                                if function not in similarities[oid][other_oid]:
                                    similarities[oid][other_oid][function] = {}
                                similarities[oid][other_oid][function][other_function] = score
                        else:
                            oid_h = api.get_field("file_meta",oid,"original_paths")
                            oid_h = next(iter(oid_h))
                            other_oid_h = api.get_field("file_meta",other_oid,"original_paths")
                            other_oid_h = next(iter(other_oid_h))
                            if condensed:
                                similarities[f"{oid_h}.{function}-{other_oid_h}.{other_function}"] = score
                            else:
                                if oid_h not in similarities:
                                    similarities[oid_h] = {}
                                if other_oid_h not in similarities[oid_h]:
                                    similarities[oid_h][other_oid_h] = {}
                                if function not in similarities[oid_h][other_oid_h]:
                                    similarities[oid_h][other_oid_h][function] = {}
                                similarities[oid_h][other_oid_h][function][other_function] = score
    else:
        return False
    return similarities
exports = [compare_function_hashes]
