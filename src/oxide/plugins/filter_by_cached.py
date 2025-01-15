#filter oids by whether they're cached in a module
AUTHOR="Kevan"
NAME="filter_by_cached"
from oxide.core import api

def filter_by_cached(args: list, opts: dict):
    """ Return a list of oids which have cached results for a given module
        Provide the opts as you would expect them to appear in the module
        Can be used to filter oids that have already had results cached into a
        different collection or context

        Syntax: filter_by_cached module_name oids

    """
    if not args or len(args) < 2:
        print("missing args")
        return False
    else:
        module_name = args[0]
        oids = args[1:]
    valid, invalid = api.valid_oids(oids)
    cached_oids = []
    oids = api.expand_oids(valid)
    for oid in oids:
        if api.exists(module_name, oid, opts):
            cached_oids.append(oid)
    return cached_oids

def filter_by_not_cached(args: list, opts: dict):
    """ Return a list of oids which do not have cached results for a given module
        Provide the opts as you would expect them to appear in the module
        Can be used to filter oids that have already had results cached into a
        different collection or context

        Syntax: filter_by_not_cached module_name oids

    """
    if not args or len(args) < 2:
        print("missing args")
        return False
    else:
        module_name = args[0]
        oids = args[1:]
    valid, invalid = api.valid_oids(oids)
    cached_oids = []
    oids = api.expand_oids(valid)
    for oid in oids:
        if not api.exists(module_name, oid, opts):
            cached_oids.append(oid)
    return cached_oids

exports = [filter_by_cached, filter_by_not_cached]
