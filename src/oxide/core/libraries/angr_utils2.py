AUTHOR="KEVAN"

"""
remaking angr utils as i find that the existing one needs some maintenance,
but i'd like to free it and also rewrite it over time without breaking things
"""
from multiprocessing.managers import BaseManager, BaseProxy
import traceback
import logging
import os
#add silly libraries that want to talk here
for lib in ["angr", "claripy","cle","pyvex_c"]:
    l = logging.getLogger(lib)
    l.setLevel(logging.CRITICAL)
logger = logging.getLogger("angr_utils2")
from oxide.core import api, config

class angrManager(BaseManager):
    pass
import psutil

maximum_memory=int(psutil.virtual_memory().total*0.7)//config.multiproc_max

def ufr_step_func(simgr):
    simgr.move(from_stash='active', to_stash='deadended', filter_func=lambda s: 0x0 == s.ip.concrete_value)
    if len(simgr.active) > 0:
        state = simgr.active[0]
        #logger.info(f"checking memory...pid {state.globals['pid']}: {psutil.Process(state.globals['pid']).memory_info().rss} >= {maximum_memory} = { psutil.Process(state.globals['pid']).memory_info().rss >= maximum_memory}")
        if psutil.Process(state.globals["pid"]).memory_info().rss >= maximum_memory:
            simgr.move(from_stash="active", to_stash="lowmem")
    return simgr

def memory_write_breakpoint(state):
    state.globals["mem_writes"].append((state.inspect.mem_write_address,state.inspect.mem_write_expr))

def register_write_breakpoint(state):
    #could also track state.inspect.reg_write_offset but currently not
    state.globals["reg_writes"].append((state.inspect.mem_write_address,state.inspect.reg_write_expr))

def syscalls_breakpoint(state):
    state.globals["syscalls"].append(state.inspect.syscall_name)

class angrTherapy:
    def __init__(self,oid : str):
        import angr
        from claripy import BVS
        """
        initiate an angr project given an oid
        """
        oid_source = api.source(oid)
        if oid_source is None:
            logger.error(f"Couldn't get source of OID")
            return False
        data=api.get_field(oid_source,oid,"data",{})
        if data is None:
            logger.error(f"Couldn't get data from OID")
            return False
        f : list[str]|None = api.get_field("file_meta",oid,"names")
        if f is None:
            logger.error(f"Couldn't get the file source of OID")
            return False
        ff : str= f.pop()
        fff = api.tmp_file(ff,data)
        self._proj = angr.Project(fff)
        self._opts = angr.options
        self._bvs = BVS

    def timed_underconstrained_function_run(self,function_offset: int,timeout:int=600, prototype:str="")->tuple | bool:
        from time import time
        #first run the analysis that'll make simprocedures for all other function calls
        #self._proj.analyses.CalleeCleanupFinder()
        #fun_offset is like an int like 4096 or something
        angr_fun_addr = self._proj.loader.min_addr+function_offset
        if angr_fun_addr > self._proj.loader.max_addr:
            return False
        #add the option to run the call state w/o following calls
        angr_opts = {self._opts.LAZY_SOLVES,self._opts.CALLLESS,self._opts.SYMBOL_FILL_UNCONSTRAINED_MEMORY,self._opts.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,self._opts.CONSERVATIVE_READ_STRATEGY,self._opts.SYMBOLIC_WRITE_ADDRESSES,self._opts.SYMBOLIC_INITIAL_VALUES,self._opts.UNDER_CONSTRAINED_SYMEXEC}
        if prototype:
            try:
                fun_call_state = self._proj.factory.call_state(angr_fun_addr,add_options=angr_opts,prototype=prototype)
            except Exception as e:
                logger.warning("Something wrong w/ using prototype... Making call state without prototype")
                logger.warning(f"Protoype was {prototype}")
                fun_call_state = self._proj.factory.call_state(angr_fun_addr,add_options=angr_opts)
        else:
            fun_call_state = self._proj.factory.call_state(angr_fun_addr,add_options=angr_opts)
        #store the process id for ram purposes
        #logger.info(f"PID for newly spawned angr project: {os.getpid()} given maximum memory of {maximum_memory}")
        fun_call_state.globals["pid"] = os.getpid()
        #symbol fill the .bss and .data sections
        for section in [".bss", ".data"]:
            start = self._proj.loader.main_object.sections_map[section].vaddr
            end = start + self._proj.loader.main_object.sections_map[section].memsize
            for addr in range(start, end): fun_call_state.memory.store(addr, self._bvs(f"mem_{addr}", 8))
        simgr = self._proj.factory.simgr(fun_call_state)
        start_time = time()
        try:
            while simgr.active:
                if time()-start_time > timeout:
                    return (time()-start_time, "timed out")
                simgr.step(step_func=ufr_step_func)
            if "lowmem" in simgr.stashes and len(simgr.stashes["lowmem"]) > 0:
                return (time()-start_time, "low memory")
            return (time()-start_time, False)
        except Exception as e:
            logger.error(f"angr caught exception {e}")
            logger.error(traceback.format_exc())
            return False

    def function_constraints(self,function_offset:int, registers:list[str]=[],timeout:int=600)->tuple|int:
        """ Given the address of a function, return constraints based upon the function's run-through """
        from collections import defaultdict
        import traceback
        constraints = defaultdict(list)
        registers_constraints = defaultdict(list)
        memory_updates :list[tuple] = list()
        reg_updates :list[tuple] = list()
        syscalls : list = list()
        angr_fun_addr = self._proj.loader.min_addr+function_offset
        if angr_fun_addr > self._proj.loader.max_addr:
            return False
        fun_call_state = self._proj.factory.call_state(angr_fun_addr,add_options={self._opts.LAZY_SOLVES})
        #initialize tracking of side effects
        fun_call_state.globals["mem_writes"] = []
        fun_call_state.globals["reg_writes"] = []
        fun_call_state.globals["syscalls"] = []
        fun_call_state.inspect.b("mem_write",action=memory_write_breakpoint,when="after")
        fun_call_state.inspect.b("reg_write",action=register_write_breakpoint,when="after")
        fun_call_state.inspect.b("syscall",action=syscalls_breakpoint,when="after")
        #let the user know if they accidentally input a bad register
        for register in registers:
            if not hasattr(fun_call_state.regs,register):    
                logger.warning(f"State doesn't have register {register}")
        simgr = self._proj.factory.simgr(fun_call_state)
        from time import time
        start_time = time()
        try:
            while simgr.active:
                simgr.step(step_func=ufr_step_func)
                if time()-start_time > timeout:
                    #return false if we run out of time
                    return 1
                if "lowmem" in simgr.stashes and len(simgr.stashes["lowmem"]) > 0:
                    #return false for now if we run out of memory
                    return 2
            for state in simgr.deadended:
                #constraints
                constraints["deadends"].append(state.solver.constraints)
                #registers
                for register in registers:
                    if hasattr(state.regs,register):
                        registers_constraints[register].append((getattr(state.regs,register)))
                #side effects
                for addr, val in state.globals["mem_writes"]:
                    memory_updates.append((addr,val))
                for addr, val in state.globals["reg_writes"]:
                    reg_updates.append((addr,val))
                for call in state.globals["syscalls"]:
                    syscalls.append(call)
            if len(simgr.errored) > 0:
                logger.warning("There have been states that errored")
            for error in simgr.errored:
                constraints["errors"].append(error.state.solver.constraints)
                #side effects
                for addr, val in error.state.globals["mem_writes"]:
                    memory_updates.append((addr,val))
                for addr, val in error.state.globals["reg_writes"]:
                    reg_updates.append((addr,val))
                for call in error.state.globals["syscalls"]:
                    syscalls.append(call)
                logger.warning(f"State errored due to {error.error}")
            return constraints, registers_constraints, memory_updates, reg_updates,syscalls
        except Exception as e:
            logger.error(f"angr caught exception {e}")
            logger.error(f"traceback {traceback.format_exc()}")
            return 0

class angrManagerProxy(BaseProxy):
    _exposed_ = ("timed_underconstrained_function_run","function_constraints")
    def timed_underconstrained_function_run(self, function_offset: int,timeout=600,prototype:str=""):
        return self._callmethod("timed_underconstrained_function_run",(function_offset,timeout,prototype))
    def function_constraints(self,function_offset:int,registers:list[str]=[],timeout:int=600):
        return self._callmethod("function_constraints",(function_offset,registers,timeout))

angrManager.register("angr_project",angrTherapy,angrManagerProxy)
