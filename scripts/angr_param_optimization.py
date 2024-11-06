AUTHOR="kevan"
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

def process(path,angr_solver):
    """
    This module takes in various parameters as options to
    pass to angr or Z3 in order to try and optimize them for
    faster execution speed in angr
    """
    global start_time
    global timeout
    global my_tactic
    results = {}
    
    import angr
    #create the angr project for the oid
    proj = angr.Project(path,load_options={"auto_load_libs":False})
    angr_logger = logging.getLogger("angr")
    angr_logger.setLevel(50)
    #make the cfg using cfgfast, (can improve code discovery)
    proj.analyses.CFGFast()
    #start and initialize the execution at the entry state of the program
    entry_state = proj.factory.entry_state(add_options=angr.options.simplification)
    simgr = proj.factory.simgr(entry_state)
    #make sure we don't use all the RAM and crash the interpreter
    #leaving 30% of the RAM free
    simgr.use_technique(angr.exploration_techniques.MemoryWatcher(min_memory=int(psutil.virtual_memory().total*0.3)))
    if not angr_solver:
        #import backend_z3 so i can use my custom solver
        from claripy.backends import backend_z3
        #now use the solver with the input tactic
        backend_z3.BackendZ3.solver = my_solver
    start_time = time.time()
    #loop over all stashes, trying to put them back into the active stash
    #from memory saver if we can once we've stepped all active states
    timed_out = False
    while time.time() - start_time < timeout and (simgr.active or ("lowmem" in simgr.stashes and simgr.stashes["lowmem"])):
        if simgr.active:
            simgr.step()
        if "lowmem" in simgr.stashes and simgr.stashes["lowmem"]:
            for state in simgr.stashes["lowmem"]:
                #trim the state history to lower its footprint
                state.history.trim()
            simgr.move(from_stash="lowmem", to_stash="active")
    ending_time = time.time()
    if ending_time - start_time > timeout:
        timed_out = True
    #initialize results output dictionary
    num_states = sum([len(simgr.stashes[stash]) for stash in simgr.stashes])
    results = {'states': num_states, 'seconds': ending_time-start_time, 'reached max seconds' : timed_out}
    #trying to maybe capture the solver's constraints if the results just have one state
    if num_states == 1:
        constraints = [state.solver.constraints for state in [simgr.stashes[stash] for stash in simgr.stashes]][0]
        results['constraints'] = str(constraints)
    print(json.dumps(results))

#main functionality,
#grab the path, tactic to use,
#whether we're using the angr solver (redundant with argv2 but...)
#and the basename of the file
path = sys.argv[1]
#timeout is saved as a global variable and is thus not a
#direct argument to any other function
timeout = float(sys.argv[2])
my_tactic = ""
try:
    my_tactic = sys.argv[3]
except Exception:
    my_tactic = ""
try:
    if my_tactic:
        import z3
        new_z3_tactic = z3.Tactic(my_tactic)
        del z3, new_z3_tactic
    process(path,bool(my_tactic))
except ValueError as e:
    print("VALUE ERROR :(",e)
except Exception as e:
    print("UNKNOWN ERROR :(",e)
