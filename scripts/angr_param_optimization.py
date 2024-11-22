AUTHOR="kevan"
NAME="angr_parameter_optimization_subproc"
import sys
import logging
import time
import traceback
import psutil

#test string
#debugpy :cwd "/home/kevan/oxide_dev/oxide/" :program "scripts/angr_param_optimization.py" :args ["/usr/bin/hostid" "123" "1500" "120" "qfidl"]

#getting around issue of big ol ints
sys.set_int_max_str_digits(0)

logger = logging.getLogger(NAME)
logging.basicConfig(level=logging.CRITICAL)
logging.getLogger("oxide").disabled=True
logging.getLogger("pharos_disasm").disabled=True
logging.getLogger("disasm_utils").disabled=True
logging.getLogger("claripy.frontend.light_frontend").disabled=True
logging.getLogger("exhaust_disasm").disabled=True
logging.getLogger("disassembly").disabled=True
#turn off logging before we load oxide
from oxide.core import oxide as oxide
print(f"Finished loading oxide")

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

def function_call_breakpoint(state):
    #called when we get to a function call
    global results
    global start_time
    state_history_addrs = state.history.recent_bbl_addrs
    try:
        state_ip = state.ip.concrete_value
    except Exception:
        state_ip = state.ip
    cons = state.solver.constraints
    if not state_ip in results['calls']:
        results['calls'][state_ip] = []
    results['calls'][state_ip].append({"state history bb addrs": state_history_addrs,
                                        "constraints": cons,
                                        "seconds since start": time.time() - start_time,
                                        "destination": state.inspect.function_address})

def system_call_breakpoint(state):
    #called when we get to a system call
    global results
    global start_time
    state_history_addrs = state.history.recent_bbl_addrs
    try:
        state_ip = state.ip.concrete_value
    except Exception:
        state_ip = state.ip
    cons = state.solver.constraints
    if not state_ip in results['syscalls']:
        results['syscalls'][state_ip] = []
    results['syscalls'][state_ip].append({"state history bb addrs": state_history_addrs,
                                          "constraints": cons,
                                          "seconds since start": time.time() - start_time,
                                          "destination": state.inspect.syscall_name})

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
    global results
    global oid
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
    entry_state.inspect.b("call",action=function_call_breakpoint,when=angr.BP_BEFORE)
    entry_state.inspect.b("syscall",action=system_call_breakpoint,when=angr.BP_BEFORE)
    if not angr_solver:
        #import backend_z3 so i can use my custom solver
        from claripy.backends import backend_z3
        #now use the solver with the input tactic
        backend_z3.BackendZ3.solver = my_solver
    #set the solver's z3 timeout
    entry_state.solver._solver.timeout = z3_timeout
    #construct the simulation manager
    simgr = proj.factory.simgr(entry_state, save_unsat=True)
    #make sure we don't use all the RAM and crash the interpreter
    #leaving 30% of the RAM free
    #start w/ making a stash for states to go when memory is low
    #RAM is handled in step function now...
    simgr.stashes["lowmem"] = []
    #commenting out this line which'll do the behaviour coded above for memory... commented out for debugging
    #simgr.use_technique(angr.exploration_techniques.MemoryWatcher(min_memory=int(psutil.virtual_memory().total*0.3)))
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
    results['num states'] = num_states
    results['seconds'] = ending_time-start_time
    results['reached max seconds'] = timed_out
    if num_states <= 1:
        #add the disassembly to the results so we can see what's up and why we have so few states
        disassembly = ""
        for func in proj.kb.functions:
            for i in proj.factory.block(func).disassembly.insns:
                disassembly += f"{hex(i.address)} {i.mnemonic} {i.op_str}\n"
        results['angr disasm'] = disassembly
    #locally store the results
    oxide.local_store(NAME,oid,results)
    print("OK")
    sys.exit(0)

#main functionality,
#grab the path, tactic to use,
#and the basename of the file
path = sys.argv[1]
oid = sys.argv[2]
#timeout is saved as a global variable and is thus not a
#direct argument to any other function
timeout = float(sys.argv[3])
z3_timeout = int(sys.argv[4])*1000
#keep the results as a global for use w/ breakpoint function
results = {"calls":{},"syscalls":{}}
try:
    my_tactic = sys.argv[5]
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
    sys.exit(1)
except ImportError as e:
    print(f"Importing failed... {e}")
    sys.exit(1)
except Exception as e:
    print(f"error in process(): {e}")
    print(traceback.format_exc())
    if results["calls"] or results["syscalls"] or len(results) > 2:
        print("partial results found; attempting to save data...")
        try:
            results["seconds"] = time.time()-start_time
            results["valid"] = False
            results["reached max seconds"] = True
            results["num states"] = max(len(results["calls"]),len(results["syscalls"]))
            oxide.local_store(NAME,oid,results)
            #returning a different code to let the caller know we stored partial results
            print("data successfully written out to local store")
            sys.exit(2)
        except Exception as e:
            print(f"Failed to save data... {e}")
    sys.exit(1)
