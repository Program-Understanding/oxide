""" Plugin: Prints out similarities between functions
"""
NAME="compare_function_tlsh_hashes"
from oxide.core import api
import tlsh
import os

def filter_function_hashes(args, opts):
    """
       Use to analyze function hashes of a collection, showing scores of functions between OIDs
       Syntax: filter_function_hashes [ --min=<minimum score> | --max=<maximum_score> | --hr | --human_readable ]
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
    args_dict = dict(args[0])
    possible_oids = args_dict.keys()
    valid, invalid = api.valid_oids(possible_oids)
    similarities = {}
    if valid:
        for oid in possible_oids: #big O n^4, terrible
            oid_h = api.get_field("file_meta",oid,"original_paths")
            oid_h = next(iter(oid_h))
            for other_oid in possible_oids:
                if oid == other_oid:
                    continue
                other_oid_h = api.get_field("file_meta",other_oid,"original_paths")
                other_oid_h = next(iter(other_oid_h))
                if not human_readable:
                    if (oid,other_oid) in similarities or (other_oid,oid) in similarities:
                        continue
                else:
                    if (oid_h,other_oid_h) in similarities or (other_oid_h,oid_h) in similarities:
                        continue
                functions = args_dict[oid].keys()
                other_functions = args_dict[other_oid].keys()
                for function in functions:
                    if "tlsh hash" not in args_dict[oid][function] or args_dict[oid][function]["tlsh hash"] is None:
                        continue
                    best_score = -1
                    best_function = ""
                    for other_function in other_functions:
                        if "tlsh hash" not in args_dict[other_oid][other_function] or args_dict[other_oid][other_function]["tlsh hash"] is None:
                            continue
                        score = tlsh.diff(args_dict[oid][function]["tlsh hash"],args_dict[other_oid][other_function]["tlsh hash"])
                        if (maximum and score > maximum) or (minimum and score < minimum):
                            continue
                        if score > best_score:
                            best_score = score
                            best_function=other_function
                    if best_score > -1:
                        score_store(best_score,similarities,human_readable,function,best_function,oid,other_oid,oid_h,other_oid_h)
    else:
        return False
    return similarities

def score_store(score,similarities,human_readable,function,other_function,oid,other_oid,oid_h,other_oid_h):
    if human_readable:
        oid = oid_h
        other_oid = other_oid_h
    if (oid,other_oid) not in similarities:
        similarities[(oid,other_oid)] = {}
    similarities[(oid,other_oid)][(function,other_function)] = score

def show_tlsh_matching_functions(args,opts):
    """
       Use to analyze function hashes of a collection, showing the closest matching functions between OIDs
       Syntax: show_tlsh_matching_functions [ --funs=<amount of functions to show per OID> | --min=<minimum hash score> | --hr | --human_readable]
       (Input should pipe in from function_tlsh module output)
    """
    human_readable = False
    if "hr" in opts or "human-readable" in opts:
        human_readable = True
    fun_num = 1
    if "funs" in opts:
        fun_num = opts["funs"]
    minimum = 0
    if "min" in opts:
        minimum = opts["min"]
    args_dict = dict(args[0])
    possible_oids = args_dict.keys()
    valid, invalid = api.valid_oids(possible_oids)
    similarities = {}
    if valid:
        for oid in possible_oids: #big O n^4, terrible
            oid_h = api.get_field("file_meta",oid,"original_paths")
            oid_h = next(iter(oid_h))
            for other_oid in possible_oids:
                if oid == other_oid:
                    continue
                other_oid_h = api.get_field("file_meta",other_oid,"original_paths")
                other_oid_h = next(iter(other_oid_h))
                if not human_readable:
                    if (oid,other_oid) in similarities or (other_oid,oid) in similarities:
                        continue
                else:
                    if (oid_h,other_oid_h) in similarities or (other_oid_h,oid_h) in similarities:
                        continue
                functions = args_dict[oid].keys()
                other_functions = args_dict[other_oid].keys()
                for function in functions:
                    if "tlsh hash" not in args_dict[oid][function] or args_dict[oid][function]["tlsh hash"] is None:
                        continue
                    if fun_num == 1:
                        best_score = 0
                        best_function = ""
                    for other_function in other_functions:
                        if "tlsh hash" not in args_dict[other_oid][other_function] or args_dict[other_oid][other_function]["tlsh hash"] is None:
                            continue
                        score = tlsh.diff(args_dict[oid][function]["tlsh hash"],args_dict[other_oid][other_function]["tlsh hash"])
                        if score > minimum:
                            if fun_num !=1:
                                insert_score(score,similarities,human_readable,function,other_function,oid,other_oid,oid_h,other_oid_h,fun_num)
                            else:
                                if score > best_score:
                                    best_score = score
                                    best_function = other_function
                    if fun_num == 1 and best_score > 0:
                        insert_score(score,similarities,human_readable,function,best_function,oid,other_oid,oid_h,other_oid_h,fun_num)
    else:
        return False
    return similarities

def insert_score(score,similarities,human_readable,function,other_function,oid,other_oid,oid_h,other_oid_h,fun_num):
    if human_readable:
        oid = oid_h
        other_oid = other_oid_h
    if fun_num != 1:
        if (oid,other_oid) not in similarities:
            similarities[(oid,other_oid)] = {}
        if function not in similarities[(oid,other_oid)]:
            similarities[(oid,other_oid)][function] = {}
        for i in range(1,fun_num+1):
            if f"best_function_{i}" not in similarities[(oid,other_oid)][function]:
                similarities[(oid,other_oid)][function][f"best_function_{i}"] = {other_function:score}
                break
            else:
                if similarities[(oid,other_oid)][function][f"best_function_{i}"][list(similarities[(oid,other_oid)][function][f"best_function_{i}"].keys())[0]] < score: #this could be better
                    similarities[(oid,other_oid)][function][f"best_function_{i}"] = {other_function:score}
                    break
    else:
        if (oid,other_oid) not in similarities:
            similarities[(oid,other_oid)] = {}
        similarities[(oid,other_oid)][function] = other_function


exports = [filter_function_hashes,show_tlsh_matching_functions]
