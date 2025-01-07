AUTHOR="KEVAN"
NAME="angr_function_time"
DESC="Time how long a function takes to run in angr"

from oxide.core import api
import logging
logger = logging.getLogger(NAME)
opts_doc = {"summaries": {"type":bool, "mangle":False,"default":True,"description":"Include function summaries from function summary module as well"}}

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
        if opts["summaries"]:
            function_summary = api.get_field("function_summary", oid, oid)
        for fun in g_d:
            if opts["summaries"] and g_d[fun]["name"] in function_summary and type(fun) is int:
                f_dict[g_d[fun]["name"]] = {}
                f_dict[g_d[fun]["name"]]["summary"] = function_summary[g_d[fun]["name"]]
            elif opts["summaries"] or type(fun) is not int:
                #sometimes the function comes out as a string
                #or it doesn't have a summary
                continue
            with angrManager() as angrmanager:
                if type(fun) is not int:
                    continue
                if fun is None:
                    continue
                angrproj = angrmanager.angr_project(oid)
                ftime_result = angrproj.timed_underconstrained_function_run(fun,opts["timeout"])
                if type(ftime_result) is tuple:
                    ftime = ftime_result[0]
                    exceeded_memory_limit = ftime_result[1]
                    f_dict[g_d[fun]["name"]]["angr seconds"] = f"{ftime} seconds"
                    f_dict[g_d[fun]["name"]]["exceeded memory limit(stopped early)"] = exceeded_memory_limit
                else:
                    f_dict[g_d[fun]["name"]]["angr seconds"] = "angr error"
        results[oid] = f_dict
        api.store(NAME,oid,f_dict,opts)
    return results
