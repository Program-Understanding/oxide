AUTHOR="KEVAN"
NAME="angr_function_time"
DESC="Time how long a function takes to run in angr"

from oxide.core import api
import logging
from angrProgress import angrProgress

logger = logging.getLogger(NAME)
opts_doc = {"timeout": {"type":int,"mangle":True,"default":600,"description":"timeout in seconds per function"},
            "summaries": {"type":bool, "mangle":False,"default":True,"description":"Include function summaries from function summary module as well"}}

def documentation():
    return {"description":DESC, "opts_doc": opts_doc, "private": False,"set":False, "atomic": True}

def process(oid, opts):
    from oxide.core.libraries.angr_utils2 import angrManager, angrTherapy,angrManagerProxy
    angrManager.register("angr_project",angrTherapy,angrManagerProxy)
    for oid in oid_list:
        g_d = api.get_field("ghidra_disasm",oid,"functions")
        f_dict = {}
        prog = angrProgress(len(g_d))
        if opts["summaries"]:
            function_summary = api.get_field("function_summary", oid, oid)
            function_extract = api.retrieve("function_extract", oid,{})
        for fun in g_d:
            #skipping _start as it doesn't ret and will run until it times out
            if g_d[fun]["name"] == "_start":
                continue
            if opts["summaries"] and g_d[fun]["name"] in function_summary and type(fun) is int:
                f_dict[g_d[fun]["name"]] = {}
                f_dict[g_d[fun]["name"]]["summary"] = function_summary[g_d[fun]["name"]]
                f_dict[g_d[fun]["name"]]["instructions"] = function_extract[g_d[fun]["name"]]["instructions"]
            elif opts["summaries"] or type(fun) is not int:
                #sometimes the function comes out as a string
                #or it doesn't have a summary
                continue
            if type(fun) is int:
                with angrManager() as angrmanager:
                    angrproj = angrmanager.angr_project(oid)
                    ftime_result = angrproj.timed_underconstrained_function_run(fun,opts["timeout"])
                    if type(ftime_result) is tuple:
                        ftime = ftime_result[0]
                        stopped_early = ftime_result[1]
                        f_dict[g_d[fun]["name"]]["angr seconds"] = f"{ftime} seconds"
                        if stopped_early:
                            f_dict[g_d[fun]["name"]]["stopped early for"] = stopped_early
                    else:
                        f_dict[g_d[fun]["name"]]["angr seconds"] = "angr error"
            prog.tick()
        results[oid] = f_dict
        api.store(NAME,oid,f_dict,opts)
    return results
