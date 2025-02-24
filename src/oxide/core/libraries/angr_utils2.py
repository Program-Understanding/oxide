AUTHOR="KEVAN"

"""
remaking angr utils as i find that the existing one needs some maintenance,
but i'd like to free it and also rewrite it over time without breaking things
"""
from multiprocessing.managers import BaseManager, BaseProxy

import logging
#add silly libraries that want to talk here
for lib in ["angr", "claripy","cle"]:
    l = logging.getLogger(lib)
    l.setLevel(logging.CRITICAL)
logger = logging.getLogger("angr_utils2")
from oxide.core import api

class angrManager(BaseManager):
    pass
import psutil
minimum_memory=int(psutil.virtual_memory().total*0.3)

def ufr_step_func(simgr):
    simgr.move(from_stash='active', to_stash='deadended', filter_func=lambda s: 0x0 == s.ip.concrete_value)
    if psutil.virtual_memory().available <= minimum_memory:
        simgr.move(from_stash="active", to_stash="lowmem")
    return simgr

class angrTherapy:
    def __init__(self,oid):
        import angr
        from claripy import backends
        """
        initiate an angr project given an oid
        """
        data=api.get_field(api.source(oid),oid,"data",{})
        f = api.get_field("file_meta",oid,"names").pop()
        f = api.tmp_file(f,data)
        self._proj = angr.Project(f)
        self._opts = angr.options
        self._convert = backends.z3.convert

    def timed_underconstrained_function_run(self,function_offset: int,timeout:int=600)->tuple | bool:
        from time import time
        #first run the analysis that'll make simprocedures for all other function calls
        self._proj.analyses.CalleeCleanupFinder()
        #fun_offset is like an int like 4096 or something
        angr_fun_addr = self._proj.loader.min_addr+function_offset
        if angr_fun_addr > self._proj.loader.max_addr:
            return False
        #add the option to run the call state w/o following calls
        fun_call_state = self._proj.factory.call_state(angr_fun_addr,add_options={self._opts.LAZY_SOLVES})        
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
        except Exception:
            return False

    def function_constraints(self,function_offset:int, registers:list[str]=[],timeout:int=600)->tuple|bool:
        """ Given the address of a function, return constraints based upon the function's run-through """
        constraints = []
        registers_constraints = []
        angr_fun_addr = self._proj.loader.min_addr+function_offset
        if angr_fun_addr > self._proj.loader.max_addr:
            return False
        fun_call_state = self._proj.factory.call_state(angr_fun_addr)
        simgr = self._proj.factory.simgr(fun_call_state)
        from time import time
        start_time = time()
        try:
            while simgr.active:
                simgr.step(step_func=ufr_step_func)
                if time()-start_time > timeout:
                    #return false if we run out of time
                    return False
                if "lowmem" in simgr.stashes and len(simgr.stashes["lowmem"]) > 0:
                    #return false for now if we run out of memory
                    return False
            for state in simgr.deadended:
                constraints.append(self._convert(state.solver.constraints))
                for register in registers:
                    if hasattr(state,register):
                        registers_constraints.append(self._convert(getattr(state,register)))
                    else:
                        logger.warning(f"State doesn't have register {register}")
            if len(simgr.errored) > 0:
                logger.warning("There have been states that errored")
            for state in simgr.errored:
                constraints.append(self._convert(state.state.solver.constraints))
            return constraints, registers_constraints
        except Exception:
            return False

class angrManagerProxy(BaseProxy):
    _exposed_ = ("timed_underconstrained_function_run","loop_analyzer")
    def timed_underconstrained_function_run(self, function_offset: int,timeout=600):
        return self._callmethod("timed_underconstrained_function_run",(function_offset,timeout))
    def function_constraints(self,function_offset:int,registers:list[str]=[],timeout:int=600):
        return self._callmethod("function_constraints")

angrManager.register("angr_project",angrTherapy)
