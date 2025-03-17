AUTHOR="KEVAN"
NAME="angr_function_time"
DESC="Time how long a function takes to run in angr"

from oxide.core import api
import logging
from angrProgress import angrProgress
import re

logger = logging.getLogger(NAME)
opts_doc = {"timeout": {"type":int,"mangle":True,"default":600,"description":"timeout in seconds per function"}}

def documentation():
    return {"description":DESC, "opts_doc": opts_doc, "private": False,"set":False, "atomic": True}

def process(oid, opts):
    from oxide.core.libraries.angr_utils2 import angrManager, angrTherapy,angrManagerProxy
    angrManager.register("angr_project",angrTherapy,angrManagerProxy)
    g_d = api.get_field("ghidra_disasm",oid,"functions")
    if not g_d:
        logger.error(f"Error with ghidra disassembly for {oid}!")
        return False
    f_dict = {}
    prog = angrProgress(len(g_d))
    function_summary = api.get_field("function_summary", oid, oid)
    function_extract = api.retrieve("function_extract", oid,{})
    if not function_summary:
        logger.error(f"Error with function summary for {oid}")
        return False
    if not function_extract:
        logger.error(f"Error with function extract for {oid}")
        return False
    for fun in g_d:
        f_name = g_d[fun]["name"]        
        signature = g_d[fun]["signature"]
        #have to remove stuff that ghidra adds to signature that isn't good
        signature = re.sub(r'\b__stdcall\b',"",signature)
        #skipping anything with "undefined" in the function signature
        #undefined is ghidra saying it doesn't know the signature properly
        #and if we don't know the signature properly its best to move on
        if "undefined" in signature or "FILE" in signature:
            prog.tick()
            continue
        #skipping _start as it doesn't ret and will run until it times out
        #also skipping other libc things and things that don't have any basic blocks
        if g_d[fun]["blocks"] == [] or f_name in ["_start","__stack_chk_fail","_init","_fini","_INIT_0","_FINI_0", "__libc_start_main", "malloc", "puts",
                      #functions excluded by x86 sok
                      "__x86.get_pc_thunk.bx", # glibc in i386 function
               "__libc_csu_init",
               "__libc_csu_fini",
               "deregister_tm_clones",
               "register_tm_clones",
               "__do_global_dtors_aux",
               "frame_dummy",
               "_start",
               "atexit",
               "_dl_relocate_static_pie",
               "__stat",
               "stat64",
               "fstat64",
               "lstat64",
               "fstatat64",
               "__fstat"]:
            prog.tick()
            continue
        if f_name in function_summary and type(fun) is int:
            f_dict[f_name] = {}
            f_dict[f_name]["summary"] = function_summary[f_name]
            f_dict[f_name]["instructions"] = function_extract[f_name]["instructions"]
            f_dict[f_name]["angr seconds"] = ""
            #logger.info(f"Function signature {signature}")
            with angrManager() as angrmanager:
                angrproj = angrmanager.angr_project(oid)
                ftime_result = angrproj.timed_underconstrained_function_run(fun,opts["timeout"],signature)
                if type(ftime_result) is tuple:
                    ftime = ftime_result[0]
                    stopped_early = ftime_result[1]
                    f_dict[f_name]["angr seconds"] = f"{ftime} seconds"
                    if stopped_early:
                        f_dict[f_name]["stopped early for"] = stopped_early
                else:
                    f_dict[f_name]["angr seconds"] = "angr error"
            #checking to see if we stopped early immediately due to low memory
            #this seems to happen sometimes, maybe due to multiprocessing...
            #like if we have too many angr processes going at once and one or more
            #is hogging too much of the RAM, the tests start and stop immediately due
            #to seeing the RAM being fully used up
            if "stopped early for" in f_dict[f_name] and f_dict[f_name]["stopped early for"] == "low memory" and float(f_dict[f_name]["angr seconds"].split(" ")[0]) < 0.01:
                with angrManager() as angrmanager:
                    angrproj = angrmanager.angr_project(oid)
                    ftime_result = angrproj.timed_underconstrained_function_run(fun,opts["timeout"],signature)
                    if type(ftime_result) is tuple:
                        ftime = ftime_result[0]
                        stopped_early = ftime_result[1]
                        f_dict[f_name]["angr seconds"] = f"{ftime} seconds"
                        if stopped_early:
                            f_dict[f_name]["stopped early for"] = stopped_early
                    else:
                        f_dict[f_name]["angr seconds"] = "angr error"
        elif type(fun) is not int:
            #sometimes the function comes out as a string
            prog.tick()
            continue
        prog.tick()
    results = f_dict
    api.store(NAME,oid,results,opts)
    return results
