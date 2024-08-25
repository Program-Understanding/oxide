""" Plugin: Prints out information regarding angr constraints
"""
NAME="angr_constraint_details"
AUTHOR="Kevan"

from oxide.core import api

def count_all(args, opts):
    """
    Use this to count the amount of classes, such as bitvector or bool
    from angr constraints

    Usage: run angr_constraints &<collection> | count_all | show
    """
    args_dict = dict(args[0])
    possible_oids = args_dict.keys()
    valid, invalid = api.valid_oids(possible_oids)
    results = {}
    if valid:
        for oid in possible_oids: #iterate through each oid
            for counts in args_dict[oid]['counts']:
                if args_dict[oid]['counts'] == "No constraints":
                    continue
                if counts not in results:
                    results[counts] = 0
                results[counts] += args_dict[oid]['counts'][counts]
    return results

exports = [count_all]
