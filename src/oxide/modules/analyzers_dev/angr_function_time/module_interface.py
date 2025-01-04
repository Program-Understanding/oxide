AUTHOR="KEVAN"
NAME="angr_function_time"
DESC="Time how long a function takes to run in angr"

from oxide.core import api
import logging
logger = logging.getLogger(NAME)
opts_doc = {"timeout": {"type":int,"mangle":True,"default":600,"description":"timeout in seconds per function"}}

def documentation():
    return {"description":DESC, "opts_doc": opts_doc, "private": False,"set":False, "atomic": True}

def results(oid_list, opts):
    from oxide.core.libraries.angr_utils2 import angrManager, angrTherapy,angrManagerProxy
    angrManager.register("angr_project",angrTherapy,angrManagerProxy)
    oid_list = api.expand_oids(oid_list)
    results ={}
    for oid in oid_list:
        g_d = api.get_field("ghidra_disasm",oid,"functions")
        f_dict = {}
        angrmanager = angrManager()
        angrmanager.start()
        angrproj = angrmanager.angr_project(oid)
        for fun in g_d:
            ftime = angrproj.timed_underconstrained_function_run(fun,opts["timeout"])
            f_dict[g_d[fun]["name"]] = f"{ftime} seconds"
        results[oid] = f_dict

    return results
