""" Plugin: Prints out capa results for an oid.
"""
NAME="compare_function_tlsh_hashes"
from oxide.core import api
import tlsh

# working on taking input from function_tlsh module and comparing
 #args is 1st direct args, then whats passed in thru pipe
 #opts is flags passed
def compare_function_hashes(args, opts):
    """
       Use to analyze function hashes given from the function_tlsh module
       Syntax: run function_tlsh &<collection> | compare_function_tlsh | show
    """
    args_dict = dict(args[0])
    possible_oids = args_dict.keys()
    valid, invalid = api.valid_oids(possible_oids)
    similarities = {}
    if valid:
        for oid in possible_oids: #big O n^4, terrible
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
                        similarities[f"{oid}.{function}-{other_oid}.{other_function}"] = score
    else:
        return False
    breakpoint()
    return similarities
exports = [compare_function_hashes]
