AUTHOR="kevan"
import sys
import logging
import time
import json
import psutil

logger = logging.getLogger("angr_parameter_optimization")
logging.basicConfig(level=logging.ERROR)

#global variables passed between functions
#could possibly be made into arguments to process and then
#states or the simgr could probably hold these as attributes but...
start_time = float()
my_tactic = ""
minimum_memory=int(psutil.virtual_memory().total*0.3)

def k_step_func(simmgr):
    global start_time
    global timeout
    global minimum_memory
    if time.time() - start_time > timeout: #checking timeout limit
        #if we've timed out, move states to deadend, we're done
        simmgr.move(from_stash="active", to_stash="deadend")
        if len(simmgr.stashes["lowmem"]):
            simmgr.move(from_stash="lowmem", to_stash="deadend")
    #check the virtual memory
    if psutil.virtual_memory().available <= minimum_memory:
        simmgr.move(from_stash="active", to_stash="lowmem")
    return simmgr

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
           pass
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

def process(path,angr_solver,z3_timeout):
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
    #make the loggers stop talking to me
    angr_logger = logging.getLogger("angr")
    angr_logger.setLevel(50)
    cle_logger = logging.getLogger("cle")
    cle_logger.setLevel(50)
    another_logger = logging.getLogger("angr.state_plugins.unicorn_engine")
    another_logger.setLevel(50)
    and_another_logger = logging.getLogger("cle.backends.externs")
    and_another_logger.setLevel(50)
    and_another_logger = logging.getLogger("cle.loader")
    and_another_logger.setLevel(50)
    #make the cfg using cfgfast, (can improve code discovery)
    proj.analyses.CFGFast()
    #start and initialize the execution at the entry state of the program
    entry_state = proj.factory.entry_state(add_options=angr.options.simplification)
    entry_state.options.add(angr.options.TRACK_CONSTRAINTS)
    simgr = proj.factory.simgr(entry_state)
    #make sure we don't use all the RAM and crash the interpreter
    #leaving 30% of the RAM free
    #start w/ making a stash for states to go when memory is low
    #RAM is handled in step function now...
    simgr.stashes["lowmem"] = []
    #commenting out this line which'll do the behaviour coded above for memory... commented out for debugging
    #simgr.use_technique(angr.exploration_techniques.MemoryWatcher(min_memory=int(psutil.virtual_memory().total*0.3)))
    if not angr_solver:
        #import backend_z3 so i can use my custom solver
        from claripy.backends import backend_z3
        #now use the solver with the input tactic
        backend_z3.BackendZ3.solver = my_solver
    #set the solver's z3 timeout
    entry_state.solver._solver.timeout = z3_timeout
    start_time = time.time()
    #loop over all stashes, trying to put them back into the active stash
    #from memory saver if we can once we've stepped all active states
    timed_out = False
    while time.time() - start_time < timeout and (simgr.active or ("lowmem" in simgr.stashes and simgr.stashes["lowmem"])):
        if simgr.active:
            simgr.step(step_func=k_step_func)
        if "lowmem" in simgr.stashes and simgr.stashes["lowmem"]:
            for state in simgr.stashes["lowmem"]:
                #trim the state history to lower its footprint
                state.history.trim()
            #move the states back into active
            simgr.move(from_stash="lowmem", to_stash="active")
    ending_time = time.time()
    if ending_time - start_time > timeout:
        timed_out = True
    #initialize results output dictionary
    num_states = sum([len(simgr.stashes[stash]) for stash in simgr.stashes])
    if num_states <= 1:
        print("Likely Z3 timeout")
        return
    results = {'states': num_states, 'seconds': ending_time-start_time, 'reached max seconds' : timed_out}
    print(json.dumps(results))

#main functionality,
#grab the path, tactic to use,
#and the basename of the file
path = sys.argv[1]
#timeout is saved as a global variable and is thus not a
#direct argument to any other function
timeout = float(sys.argv[2])
z3_timeout = int(sys.argv[3])*1000
try:
    my_tactic = sys.argv[4]
except Exception:
    my_tactic = ""
try:
    if my_tactic:
        import z3
        new_z3_tactic = z3.Tactic(my_tactic)
        del z3, new_z3_tactic
    process(path,not bool(my_tactic),z3_timeout)
except ValueError as e:
    print("VALUE ERROR : ",e)
except TypeError as e:
    print("TYPE ERROR : ",e)
except Exception as e:
    print("ERROR : ",e)
