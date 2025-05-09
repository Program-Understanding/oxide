AUTHOR="kevan"
NAME="angr_optimization_test"
import traceback
import sys
import logging
import time
import psutil
from pickle import loads, dumps
#debugging RAM malarcky
from sys import getsizeof
import z3
#add option to set verbosity of z3
z3.set_option("verbose", 10)
import claripy
#trying to get rid of as much excess logging as possible to help w/ debugging if anything goes wrong
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

start_time = float()
my_tactic = ""

def my_solver(self, timeout=None, max_memory=None):
    """ 
    This replaces the backend Z3 solver used by angr
    """
    global my_tactic
    global num_processes
    from threading import current_thread, main_thread
    if not self.reuse_z3_solver or getattr(self._tls, "solver", None) is None:
        
        #again add option to set verbosity of z3 just in case
        z3.set_option("verbose", 10)

        if my_tactic:
            s = z3.Tactic(my_tactic,ctx=self._context).solver()
            print(f"running with tactic {my_tactic}")
        else:
            s = z3.Solver(ctx=self._context)  # , logFile="claripy.smt2")
            print(f"Running without a tactic")
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
    else:
        #making sure to make sure that max memory is really for real getting set because it doesn't otherwise look like it
        s.set("max_memory",max(int(((psutil.virtual_memory().total*0.66)/2**6)/num_processes), 1024))
    return s

def is_sat(solver,constraints):
    global process
    try:
        #check memory
        max_bytes = (1024*1024*1024) * 5
        if process.memory_info().rss > max_bytes:
            raise Exception(f"USING MORE THAN {max_bytes} bytes of RAM")
        #passing the constraints as extra constraints instead of adding them to the
        #solver turns out to be huge in terms of saving ram
        return solver.satisfiable(extra_constraints=constraints)
    except claripy.errors.ClaripyZ3Error:
        return False

def subprocess(constraint_file,out_path):
    #this function will load the constraints from the oxide datastore using the oid and name,
    #then it will run through the constraints with the tactic given, making sure to use the appropriate
    #z3 timeout and keeping track of how long it takes to solve each constraint
    #first i'll make sure to replace the default claripy solver with my own
    #now use the solver with the input tactic
    global num_processes
    claripy.backends.backend_z3.BackendZ3.solver = my_solver
    #inp = oxide.local_retrieve(name,oid)
    with open(constraint_file,"rb") as f:
        inp = loads(f.read())
    stats = {}
    #need to loop through syscalls', function calls', and deadends' constraints
    #initialize solver w/ max memory being coded to 66% of ram divided by number of processes running
    slvr = claripy.Solver() #need to divide by 2**6 as max_memory should be sent in MB and not B
    #setting also a minimum value of 1024 MB as recommended by z3, though this shouldn't ever be hit
    slvr.max_memory = max(int(((psutil.virtual_memory().total*0.66)/2**6)/num_processes), 1024)
    # for state_ip in inp['syscalls'].keys():
    #looping through syscalls:
    if inp['syscalls']:
        stats['syscalls'] = []
        for cons in inp['syscalls']:
            ini_time = time.time()
            sat = is_sat(slvr,cons)
            stats['syscalls'].append({"number of constraints": len(cons),
                                      "seconds taken to determine sat": time.time()-ini_time,
                                      "satisfiable": sat})

    #looping through function calls
    if inp['calls']:
        stats['function calls'] = []
    # for state_ip in inp['calls'].keys():
    #     stats['function calls'][state_ip] = []
        for cons in inp['calls']:
                ini_time = time.time()
                sat = is_sat(slvr,cons)
                stats['function calls'].append({"number of constraints": len(cons),
                                                "seconds taken to determine sat": time.time()-ini_time,
                                                "satisfiable": sat})
    #looping through deadended states
    #making sure we even have any deadends first
    if inp['deadends']:
        stats['deadends'] = []
        # for state_ip in inp['deadends'].keys():
            # stats['deadends'][state_ip] = []
        for cons in inp['deadends']:
            ini_time = time.time()
            sat = is_sat(slvr,cons)
            stats['deadends'].append({"number of constraints": len(cons),
                                      "seconds taken to determine sat": time.time()-ini_time,
                                      "satisfiable": sat})
    #finally, need to calculate the total time taken by adding up the number of seconds
    #across deadends, syscalls, and funcalls
    total_time_in_seconds = 0
    for category in ['deadends','function calls', 'syscalls']:
        if category in stats:
            # for state_ip in stats[category].keys():
            for list_item in stats[category]:
                total_time_in_seconds += list_item["seconds taken to determine sat"]
    stats["total seconds"] = total_time_in_seconds
    #store the results in the local oxide scratch and exit gracefully
    with open(out_path,"wb") as f:
        f.write(dumps(stats))
    print("Done")
    sys.exit(0)

process = psutil.Process()
constraint_file = sys.argv[1]
output_path = sys.argv[2]
oid = sys.argv[3]
#timeout is saved as a global variable and is thus not a
#direct argument to any other function
z3_timeout = int(sys.argv[4])*1000
#keep the results as a global for use w/ breakpoint function
num_processes = int(sys.argv[5])
results = {"calls":{},"syscalls":{}}
print("Initialized results, starting process...")
try:
    my_tactic = sys.argv[6]
except Exception:
    my_tactic = ""
try:
    subprocess(constraint_file,output_path)
except Exception as e:
    print(f"Exception occurred in subprcess(): {e}")
    print(traceback.format_exc())
    sys.exit(1)
