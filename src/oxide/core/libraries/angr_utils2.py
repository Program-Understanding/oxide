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

from oxide.core import api

class angrManager(BaseManager):
    pass

def ufr_step_func(simgr):
    simgr.move(from_stash='active', to_stash='deadended', filter_func=lambda s: 0x0 == s.ip.concrete_value)
    return simgr

class angrTherapy:
    def __init__(self,oid):
        import angr
        """
        initiate an angr project given an oid
        """        
        data=api.get_field(api.source(oid),oid,"data",{})
        f = api.get_field("file_meta",oid,"names").pop()
        f = api.tmp_file(f,data)
        self._proj = angr.Project(f)

    def timed_underconstrained_function_run(self,function_offset,timeout=600):
        from time import time
        #fun_offset is like an int like 4096 or something
        angr_fun_addr = self._proj.loader.min_addr+function_offset
        if angr_fun_addr > self._proj.loader.max_addr:
            return -1
        fun_call_state = self._proj.factory.call_state(angr_fun_addr)
        simgr = self._proj.factory.simgr(fun_call_state)
        start_time = time()
        while simgr.active:
            if time()-start_time > timeout:
                break
            simgr.step(step_func=ufr_step_func)
        return time()-start_time

class angrManagerProxy(BaseProxy):
    _exposed_ = ("timed_underconstrained_function_run",)
    def timed_underconstrained_function_run(self, function_offset,timeout=600):
        return self._callmethod("timed_underconstrained_function_run",(function_offset,timeout))

angrManager.register("angr_project",angrTherapy)
