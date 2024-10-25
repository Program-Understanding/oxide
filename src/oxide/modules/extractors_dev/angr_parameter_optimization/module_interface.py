AUTHOR="KEVAN"
DESC="Pass options to try and analyze effect on angr and Z3"
NAME="angr_parameter_optimization"

import logging
logger = logging.getLogger(NAME)

from core import api
import time

opts_doc={"timeout": {"type": int, "mangle": True, "default": 120, "description": "Time in seconds for angr before it times out, default is 5 minutes"},
          "exploration": {"type": str, "mangle": True, "description": "Choose a different exploration technique. Should be from angr.exploration_techniques, such as 'angr.exploration_techniques.dfs'","default":""},
          "tactics": {"type": str, "mangle": True, "description": "Comma separated list of tactics to use for angr's Z3 solver in a z3.Then() order. Takes precedence over tactic", "default": ""},
          "tactic": {"type": str, "mangle": True, "description": "Singular tactic to use for angr's Z3 solver. Tactics takes precedence"}
          }

def documentation():
    return {"description":DESC,
            "opts_doc": opts_doc,
            "private": False,
            "set": False,
            "atomic":True
            }

def k_step_func(simmgr):
    global start_time
    global timeout
    if time.time() - start_time > timeout: #checking timeout limit
        simmgr.move(from_stash="active", to_stash="deadend")
    return simmgr

start_time = float()
timeout = float()
def process(oid, opts):
    """
    This module takes in various parameters as options to
    pass to angr or Z3 in order to try and optimize them for
    faster execution speed in angr
    """
    global start_time
    global timeout
    import angr
    # this will have to be run twice...
    #set proper timeout
    my_tactics = []
    my_tactic = ""
    timeout = opts['timeout']
    if opts['tactics']:
        my_tactics = opts['tactics'].split(",")
        if opts['tactic']:
            logger.warning("Tactics option overrides tactic, your provided tactic will not be used")
    elif opts['tactic']:
        my_tactic = opts['tactic']
    #initialize results output dictionary
    results = {'with angr solver': {}}
    #create the angr project for the oid
    data = api.get_field(api.source(oid), oid, "data", {})
    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data)
    proj = angr.Project(f_name,load_options={"auto_load_libs":False})
    angr_logger = logging.getLogger("angr")
    angr_logger.setLevel(50)
    #make the cfg using cfgfast
    proj.analyses.CFGFast()
    #start and initialize the execution at the entry state of the program
    entry_state = proj.factory.entry_state(add_options=angr.options.simplification)
    simgr = proj.factory.simgr(entry_state)
    #make sure we don't use all the RAM and crash the interpreter
    #leaving 2GB free of RAM
    import param_helper
    if opts["exploration"]:
        param_helper.set_simgr_techniques(opts["exploration"],simgr)
    start_time = time.time()
    while simgr.active:
        simgr.step()
    ending_time = time.time()
    results['with angr solver']['states'] = sum([len(simgr.stashes[stash]) for stash in simgr.stashes])
    results['with angr solver']['time taken'] = ending_time-start_time
    # i have to reimport angr and stuff each time I call this function, otherwise
    # there will be some residual leftover stuff in memory that I'd much
    # rather have cleared
    # i might need to kill and reload angr after every test.... i know its ugly
    #refresh angr and things
    del angr
    import angr
    #import backend_z3 so i can use my custom solver
    from claripy.backends import backend_z3
    #set the parameter helper's global variables
    param_helper.my_tactics = my_tactics
    param_helper.my_tactic = my_tactic
    #now use my custom solver!
    backend_z3.BackendZ3.solver = param_helper.my_solver
    #create the angr project for the oid
    proj = angr.Project(f_name,load_options={"auto_load_libs":False})
    angr_logger = logging.getLogger("angr")
    angr_logger.setLevel(50)
    #make the cfg using cfgfast
    proj.analyses.CFGFast()
    #start and initialize the execution at the entry state of the program
    #the added option should make angr use Z3 more for simplification
    entry_state = proj.factory.entry_state(add_options=angr.options.simplification)
    simgr = proj.factory.simgr(entry_state)
    if opts["exploration"]:
        param_helper.set_simgr_techniques(opts["exploration"],simgr)
    start_time = time.time()
    while simgr.active:
        simgr.step()
    ending_time = time.time()
    results['with my solver'] = {}
    results['with my solver']['states'] = sum([len(simgr.stashes[stash]) for stash in simgr.stashes])
    results['with my solver']['seconds taken'] = ending_time-start_time
    results['angr strategy'] = opts['exploration'] if opts['exploration'] else "None selected"
    del angr
    api.store(NAME,oid,results,opts)
    return True
    
