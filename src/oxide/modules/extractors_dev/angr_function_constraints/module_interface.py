AUTHOR="KEVAN"
NAME="angr_function_constraints"
DESC="Retrieve the constraints made by a function and its registers from running within angr"

from oxide.core import api
import logging

logger = logging.getLogger(NAME)
opts_doc = {"timeout": {"type":int,"mangle":True,"default":600,"description":"timeout in seconds per function"},
            "registers": {"type":str, "mangle":True,"default":"rax","description":"comma separated list of registers to check from angr (eg 'rax,rdi')"}}

def documentation():
    return {"description":DESC, "opts_doc": opts_doc, "private": False,"set":False, "atomic": True}

def process(oid, opts):
    from oxide.core.libraries.angr_utils2 import angrManager, angrTherapy,angrManagerProxy
    angrManager.register("angr_project",angrTherapy,angrManagerProxy)
    g_d = api.get_field("ghidra_disasm",oid,"functions")
    if g_d is None:
        logger.error(f"Error with ghidra disassembly for {oid}!")
        return False
    f_dict = {}
    for fun in g_d:
        fun_name = g_d[fun]["name"]
        #skipping _start as it doesn't ret and will run until it times out
        if g_d[fun]["name"] in ["_start","__stack_chk_fail","_init","_fini","_INIT_0","_FINI_0"] \
           or type(fun) is not int:
            continue
        f_dict[g_d[fun]["name"]] = {}
        with angrManager() as angrmanager:
            angrproj = angrmanager.angr_project(oid)
            user_regs = opts["registers"].split(",")
            if type(user_regs) is not list:
                user_regs = list(user_regs)
            res : tuple[list,dict,list,list,list] | int = angrproj.function_constraints(fun,opts["registers"].split(","),opts["timeout"])
            if type(res) is tuple:
                constraints, registers, mems, regs, syscalls = res
                f_dict[fun_name]["constraints"] = constraints
                f_dict[fun_name]["registers"] = registers
                f_dict[fun_name]["memory writes"] = mems
                f_dict[fun_name]["register writes"] = regs
                f_dict[fun_name]["syscalls"] = syscalls
            else:
                match res:
                    case 0:
                        f_dict[g_d[fun]["name"]]["angr error"] = "Exception"
                    case 1:
                        f_dict[g_d[fun]["name"]]["angr error"] = "Time out"
                    case 2:
                        f_dict[g_d[fun]["name"]]["angr error"] = "low memory"
    results = f_dict
    api.store(NAME,oid,results,opts)
    return results
