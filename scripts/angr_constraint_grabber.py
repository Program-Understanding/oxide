NAME="angr_constraint_grabber"
AUTHOR="Kevan"
DESC="Script made to grab the constraints from angr within a timeout given an oid. Returns constraints in terms of system calls and function calls. Doesn't run with any tactics"
import sys
import logging
import time
import traceback
import psutil
from pickle import dumps

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
                                       "state instruction history": state.history.recent_ins_addrs,
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
                                          "state instruction history": state.history.recent_ins_addrs,
                                          "constraints": cons,
                                          "seconds since start": time.time() - start_time,
                                          "destination": state.inspect.syscall_name})

def subprocess(path,z3_timeout,path):
    """
    This module takes in various parameters as options to
    pass to angr or Z3 in order to try and optimize them for
    faster execution speed in angr
    """
    global start_time
    global timeout
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
        #if we still have active states, step them
        if simgr.active:
            simgr.step(step_func=k_step_func)
        #else we should see about moving the states back in from lowmem
        #to do that, and not use up /more/ RAM, we should see about storing the constraints in the results from the
        #deadended states, and deleting the states to make more room
        elif "lowmem" in simgr.stashes and simgr.stashes["lowmem"]:
            #move the deaded states into results and then delete them
            for state in simgr.stashes["deadended"]:
                if not state.ip in results['deadends']:
                    results['deadends'][state.ip] = []
                results['deadends'][state.ip].append({"state bb history": state.history.recent_bbl_addrs,
                                                      "state_ins_history": state.history.recent_ins_addrs,
                                                      "constraints": state.solver.constraints})
            #move a state back and try to step it
            state = simgr.stashes["lowmem"].pop()
            #trim the state history to lower its footprint
            state.history.trim()
            #move the states back into active
            simgr.stashes["active"].append(state)
    ending_time = time.time()
    if ending_time - start_time > timeout:
        timed_out = True
    #capture number of states and time taken
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
    #capture the constraints from the deadended states
    for state in simgr.stashes["deadended"]:
        if not state.ip in results['deadends']:
            results['deadends'][state.ip] = []
        results['deadends'][state.ip].append({"state bb history": state.history.recent_bbl_addrs,
                                              "state_ins_history": state.history.recent_ins_addrs,
                                              "constraints": state.solver.constraints})
    #locally store the results
    #oxide.local_store(NAME,oid,results)
    with open(path,"wb") as f:
        f.write(dumps(results))
    print("OK")
    sys.exit(0)

#main functionality,
#grab the path and the basename of the file
path = sys.argv[1]
out_path = sys.argv[2]
oid = sys.argv[3]
#timeout is saved as a global variable and is thus not a
#direct argument to any other function
timeout = float(sys.argv[4])
z3_timeout = int(sys.argv[5])*1000
#keep the results as a global for use w/ breakpoint function
results = {"calls":{},"syscalls":{}, "deadends":{}}
try:
    subprocess(path,z3_timeout,out_path)
except ValueError as e:
    print("VALUE ERROR : ",e)
    sys.exit(1)
except ImportError as e:
    print(f"Importing failed... {e}")
    sys.exit(1)
except Exception as e:
    print(f"error in subprocess(): {e}")
    print(traceback.format_exc())
    if results["calls"] or results["syscalls"] or len(results) > 2:
        print("partial results found; attempting to save data...")
        try:
            results["seconds"] = time.time()-start_time
            results["valid"] = False
            results["reached max seconds"] = True
            results["num states"] = max(len(results["calls"]),len(results["syscalls"]))
            with open(out_path, "wb") as f:
                f.write(dumps(results))
            #oxide.local_store(NAME,oid,results)
            #returning a different code to let the caller know we stored partial results
            print("data successfully written out to local store")
            sys.exit(2)
        except Exception as e:
            print(f"Failed to save data... {e}")
    sys.exit(1)
