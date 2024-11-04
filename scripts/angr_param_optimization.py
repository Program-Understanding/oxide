import sys
import logging
import time
import json
import psutil

logger = logging.getLogger("angr_parameter_optimization")

start_time = float()

def k_step_func(simmgr):
    global start_time
    global timeout
    if time.time() - start_time > timeout: #checking timeout limit
        simmgr.move(from_stash="active", to_stash="deadend")
    return simmgr

my_tactic = ""

def my_solver(self, timeout=None, max_memory=None):
    """ 
    This replaces the backend Z3 solver used by angr
    """
    global my_tactic
    from threading import current_thread, main_thread
    if not self.reuse_z3_solver or getattr(self._tls, "solver", None) is None:
        import z3

        if my_tactic:
            s = z3.Tactic(my_tactic,ctx=self._context).solver()
        else:
            s = z3.Solver()  # , logFile="claripy.smt2")
        if current_thread() != main_thread():
            s.set(ctrl_c=False)
        try:
            import __pypy__
            __pypy__.add_memory_pressure(1024 * 1024 * 10)
        except ImportError:
            _is_pypy = False
        if self.reuse_z3_solver:
            # Store the Z3 solver to a thread-local storage if the reuse-solver option is enabled
            self._tls.solver = s
    else:
        # Load the existing Z3 solver for this thread
        s = self._tls.solver
        s.reset()

    # Configure timeouts
    if timeout is not None:
        if "soft_timeout" in str(s.param_descrs()):
            s.set("soft_timeout", timeout)
            s.set("solver2_timeout", timeout)
        else:
            s.set("timeout", timeout)
    if max_memory is not None:
        s.set("max_memory", max_memory)
    return s

def process(path,tactic,angr_solver):
    """
    This module takes in various parameters as options to
    pass to angr or Z3 in order to try and optimize them for
    faster execution speed in angr
    """
    global start_time
    global timeout
    global my_tactic
    results = {}
    if angr_solver:
        import angr
        # this will have to be run twice...
        #set proper timeout
        my_tactic = tactic
        timeout = 60
        #create the angr project for the oid
        proj = angr.Project(path,load_options={"auto_load_libs":False})
        angr_logger = logging.getLogger("angr")
        angr_logger.setLevel(50)
        #make the cfg using cfgfast
        proj.analyses.CFGFast()
        #start and initialize the execution at the entry state of the program
        entry_state = proj.factory.entry_state(add_options=angr.options.simplification)
        simgr = proj.factory.simgr(entry_state)
        #make sure we don't use all the RAM and crash the interpreter
        #leaving 25% of the RAM free
        simgr.use_technique(angr.exploration_techniques.MemoryWatcher(min_memory=int(psutil.virtual_memory().total*0.25)))
        start_time = time.time()
        while simgr.active:
            simgr.step()
        ending_time = time.time()
        #initialize results output dictionary
        results = {'states': sum([len(simgr.stashes[stash]) for stash in simgr.stashes]), 'seconds': ending_time-start_time}
    else:
        import angr
        #import backend_z3 so i can use my custom solver
        from claripy.backends import backend_z3
        #set the parameter helper's global variables
        my_tactic = tactic
        #now use my custom solver!
        backend_z3.BackendZ3.solver = my_solver
        #create the angr project for the oid
        proj = angr.Project(path,load_options={"auto_load_libs":False})
        angr_logger = logging.getLogger("angr")
        angr_logger.setLevel(50)
        #make the cfg using cfgfast
        proj.analyses.CFGFast()
        #start and initialize the execution at the entry state of the program
        #the added option should make angr use Z3 more for simplification
        entry_state = proj.factory.entry_state(add_options=angr.options.simplification)
        simgr = proj.factory.simgr(entry_state)
        #very important: make sure angr doesn't use all RAM and crash the system
        simgr.use_technique(angr.exploration_techniques.MemoryWatcher(min_memory=2048))
        start_time = time.time()
        while simgr.active:
            simgr.step()
        ending_time = time.time()
        results = {'states': sum([len(simgr.stashes[stash]) for stash in simgr.stashes]), 'seconds': ending_time-start_time}
    #output the json of the results
    print(json.dumps(results))

#main functionality,
#grab the path, tactic to use,
#whether we're using the angr solver (redundant with argv2 but...)
#and the basename of the file
path = sys.argv[1]
timeout = float(sys.argv[2])
try:
    my_tactic = sys.argv[3]
except Exception:
    my_tactic = ""
try:
    if my_tactic:
        import z3
        new_z3_tactic = z3.Tactic(my_tactic)
        del z3, new_z3_tactic
    process(path,my_tactic,bool(my_tactic))
except ValueError as e:
    print("VALUE ERROR :(",e)
except Exception as e:
    print("UNKNOWN ERROR :(",e)
