""" Plugin: Prints out information regarding angr constraints
"""
NAME="angr_filters"
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

def sample_by_time(args, opts):
    """
    Use this to filter a number of results from the angr function based upon which had
    high times. pass --n for number of OIDs, and --t for minimum time threshold.
    The results are the oids with their path and the names of functions which go over
    the threshold

    Usage: run angr_function_time &<collection> | sample_by_time --n=<int> --t=<int> | show
    """
    results = {}
    n = 1
    t = 600
    results_dict = args[0]

    nargs = len(args[0])
    if "n" in opts:
        try:
            n = int(opts["n"])
            if n < 0: raise ValueError
            if n > nargs: n = nargs
        except ValueError:
            raise ShellSyntaxError("Invalid integer value for n: %s" % opts["n"])

    for oid in results_dict:
        f_dict = results_dict[oid]
        # f_dict[g_d[fun]["name"]]["angr seconds"] = f"{ftime} seconds"
        for fun in f_dict:
            try:
                angr_seconds = float(f_dict[fun]["angr seconds"].split(" ")[0])
            except:
                continue
            if angr_seconds >= t:
                if not oid in results:
                    results[oid] = {f"functions >= {t}": []}
                results[oid][f"functions >= {t}"].append(fun)
        if oid in results:
            n-=1
            if n <= 0:
                break
    for oid in results:
        results[oid]["path"] = api.get_field("original_path",oid,oid)
    return results

exports = [count_all,sample_by_time]
