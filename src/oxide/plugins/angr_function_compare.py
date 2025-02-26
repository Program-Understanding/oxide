""" Plugin: Utility functions for manipulating files and collections
"""
NAME = "angr_function_compare"

from oxide.core import api
import logging
logger = logging.getLogger(NAME)

class Progress:
    """ Display progress through functions
    """
    def __init__(self, name: str, lot: int = 1) -> None:
        self.lot = lot
        self.progress = 0
        self.length = 50
        self.name = name

    def tick(self) -> None:
        self.progress+=1
        prog = int(round((self.progress/self.lot)*self.length)-1)
        print(f"{self.name} progress: [{'='*prog + ' '*(self.length-int(round((self.progress/self.lot)*self.length)-1))}] {self.progress}/{self.lot}",flush=True,end="\r")
        
        if self.progress/self.lot == 1:
            print()

    def new_line_tick(self) -> None:
        self.progress+=1
        prog = int(round((self.progress/self.lot)*self.length)-1)
        print(f"{self.name} progress: [{'='*prog + ' '*(self.length-int(round((self.progress/self.lot)*self.length)-1))}] {self.progress}/{self.lot}")

def function_compare(args: list[str], opts: dict) -> dict:
    """
    Compares the functions of two given oids using symbolic execution via angr
    to examine the constraints

    Syntax:
    function_compare %oid1 %oid2 [--r=<comma separated list of registers>]
    """
    from z3 import Solver, sat
    from collections import defaultdict
    from claripy import backends, And
    convert = backends.z3.convert
    best_matches = {}
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise Exception("No valid oids")
    args = api.expand_oids(valid)
    if not args:
        return {}
    if len(args) != 2:
        raise Exception("Should be giving exactly 2 oids")
    oid1 = args[0]
    oid2 = args[1]
    similarities = api.local_retrieve(NAME,oid1+oid2)
    oid1_funs = api.get_field("ghidra_disasm",oid1,"functions")
    oid2_funs = api.get_field("ghidra_disasm",oid2,"functions")
    registers = None
    if "r" in opts:
        registers = opts["r"]
    elif "registers" in opts:
        registers = opts["registers"]
    if not registers:
        registers = ["rax"]
    oid1_cons = api.retrieve("angr_function_constraints",oid1,{"registers":registers})
    oid2_cons = api.retrieve("angr_function_constraints",oid2,{"registers":registers})
    if not oid1_cons or not oid2_cons or not oid1_funs or not oid2_funs:
        raise Exception("Retrieve failed")
    if not similarities:
        similarities = {}
        for fun in oid1_funs:
            fun_name = oid1_funs[fun]["name"]
            similarities[fun_name] = {}
            best_matches[fun_name] = {}
            if fun_name not in oid1_cons: continue
            elif "angr error" in oid1_cons[fun_name]: continue
            function_prog = Progress(fun_name,len(oid2_funs))
            for o_fun in oid2_funs:
                o_fun_name = oid2_funs[o_fun]["name"]
                if o_fun_name not in oid2_cons: function_prog.tick(); continue
                elif "angr error" in oid2_cons[o_fun_name]: function_prog.tick(); continue
                #check every function in each OID
                similarities[fun_name][o_fun_name] = defaultdict(int)
                # check similaritiy of mem writes, register writes
                solver = Solver()
                for thing in ["memory writes", "register writes"]:
                    o1_thing = oid1_cons[fun_name][thing]
                    o2_thing = oid2_cons[o_fun_name][thing]
                    for c in o1_thing:
                        #c is the constraint which is a tuple w/ address/register then
                        #the value that was written there... skipping writes that
                        #go to None because idk what that's all about but if you're
                        #not writing anywhere do i care?
                        if c[0] == None: continue
                        for oc in o2_thing:
                            if oc[0] == None: continue
                            if oc[1].size() != c[1].size():
                                if oc[1].size() < c[1].size():
                                    c = (c[0],c[1][oc[1].size()-1:0])
                                else:
                                    oc = (oc[0],oc[1][c[1].size()-1:0])
                            solver.add(convert(c[1]!=oc[1]))
                            if not solver.check() == sat:
                                similarities[fun_name][o_fun_name][thing]+=1
                            solver.reset()
                #check similarity of constraints and user-provided registers
                for thing in ["constraints", "registers"]:
                    for typ in ["deadends", "errors"]:
                        o1_thing = oid1_cons[fun_name][thing][typ]
                        o2_thing = oid2_cons[o_fun_name][thing][typ]
                        for c in o1_thing:
                            #need to skip any lists that are empty
                            if not c: continue
                            for oc in o2_thing:
                                if not oc: continue
                                if type(c) is list:
                                    c = And(*c)
                                if type(oc) is list:
                                    oc = And(*oc)
                                solver.add(convert(c!=oc))
                                if not solver.check() == sat:
                                    similarities[fun_name][o_fun_name][thing]+=1
                                solver.reset()
                #check similarity of syscalls
                o1_syscalls = oid1_cons[fun_name]["syscalls"]
                o2_syscalls = oid2_cons[o_fun_name]["syscalls"]
                for o1_call in o1_syscalls:
                    for o2_call in o2_syscalls:
                        if o1_call == o2_call:
                            similarities[fun_name][o_fun_name]["syscalls"]+=1
                function_prog.tick()
        api.local_store(NAME,oid1+oid2,similarities)
    #evaluate similarities for best match
    for fun in oid1_funs:
        fun_name = oid1_funs[fun]["name"]
        if fun_name not in oid1_cons: continue
        elif "angr error" in oid1_cons[fun_name]: continue
        for o_fun in oid2_funs:
            o_fun_name = oid2_funs[o_fun]["name"]
            if o_fun_name not in oid2_cons: continue
            elif "angr error" in oid2_cons[o_fun_name]: continue
            #check if this other function is the best match
            if not fun_name in best_matches:
                #don't give a best match if its not the best match
                if sum([similarities[fun_name][o_fun_name][cat] for cat in ["syscalls","constraints","registers","memory writes","register writes"]]) > 0:
                    best_matches[fun_name] = {"best match" : {
                        "name":o_fun_name,
                        "syscalls": similarities[fun_name][o_fun_name]["syscalls"],
                        "constraints": similarities[fun_name][o_fun_name]["constraints"],
                        "user specified registers": similarities[fun_name][o_fun_name]["registers"],
                        "memory writes": similarities[fun_name][o_fun_name]["memory writes"],
                        "register writes": similarities[fun_name][o_fun_name]["register writes"]}}
            else:
                #here we check the current best match against the current other function
                print(f'best matches[{fun_name}]["best match"] = {best_matches[fun_name]["best match"]}')
                o_fun_cons : int = similarities[fun_name][o_fun_name]["constraints"]
                o_fun_calls : int = similarities[fun_name][o_fun_name]["syscalls"]
                o_fun_regs : int= similarities[fun_name][o_fun_name]["registers"]
                o_fun_r_writes : int= similarities[fun_name][o_fun_name]["register writes"]
                o_fun_m_writes : int = similarities[fun_name][o_fun_name]["memory writes"]
                o_fun_score = 10*o_fun_cons + o_fun_calls + o_fun_regs + o_fun_r_writes + o_fun_m_writes
                best_cons : int = best_matches[fun_name]["best match"]["constraints"]
                best_calls : int = best_matches[fun_name]["best match"]["syscalls"]
                best_regs : int = best_matches[fun_name]["best match"]["user specified registers"]
                best_r_w : int = best_matches[fun_name]["best match"]["register writes"]
                best_m_w : int = best_matches[fun_name]["best match"]["memory writes"]
                best_score = 10*best_cons + best_calls + best_regs + best_r_w + best_m_w
                # if o_fun_score > best_score:
                #     best_matches[fun_name]["best match"] = {"name":o_fun_name, "syscalls":o_fun_calls,"constraints":o_fun_cons,"user specified registers":o_fun_regs,"memory writes":o_fun_m_writes,"register writes":o_fun_r_writes}
                if o_fun_cons >= best_cons and \
                   o_fun_regs >= best_regs:
                    if o_fun_r_writes >= best_r_w and \
                       o_fun_m_writes >= best_m_w:
                        best_matches[fun_name]["best match"] = {"name":o_fun_name, "syscalls":o_fun_calls,"constraints":o_fun_cons,"user specified registers":o_fun_regs,"memory writes":o_fun_m_writes,"register writes":o_fun_r_writes}
    return best_matches

exports = [function_compare]
