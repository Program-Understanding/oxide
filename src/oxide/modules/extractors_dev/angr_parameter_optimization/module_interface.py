AUTHOR="KEVAN"
DESC="Pass options to try and analyze effect on angr and Z3"
NAME="angr_parameter_optimization"

import logging
logger = logging.getLogger(NAME)

from core import api
import angr
import time

opts_doc={"timeout": {"type": int, "mangle": True, "default": 600, "description": "Time in seconds for angr before it times out, default is 5 minutes"},
          "exploration": {"type": str, "mangle": True, "description": "Choose a different exploration technique. Should be from angr.exploration_techniques, such as 'angr.exploration_techniques.dfs'","default":""}
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

start_time = None
timeout = None

def process(oid, opts):
    """
    This module takes in various parameters as options to
    pass to angr or Z3 in order to try and optimize them for
    faster execution speed in angr
    """
    global start_time
    global timeout
    #set proper timeout
    timeout = opts['timeout']
    #initialize results output dictionary
    results = {}
    #create the angr project for the oid
    data = api.get_field(api.source(oid), oid, "data", {})
    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data)
    data = api.get_field(api.source(oid), oid, "data", {})
    proj = angr.Project(f_name,load_options={"auto_load_libs":False})
    angr_logger = logging.getLogger("angr")
    angr_logger.setLevel(50)
    #make the cfg using cfgfast
    cfg = proj.analyses.CFGFast()
    #start and initialize the execution at the entry state of the program
    entry_state = proj.factory.entry_state()
    simgr = proj.factory.simgr(entry_state)
    supported_options = ["dfs","loops"]
    if opts["exploration"]:
        match opts["exploration"]:
            case "dfs":
                simgr.use_technique(angr.exploration_techniques.DFS())
            case "loops":
                simgr.use_technique(angr.exploration_techniques.LoopSeer())
            case _:
                logger.warning(f"Unknown exploration option {opts['exploration']}\
                try from the following: {supported_options}")

    beginning_time = time.time()
    start_time = time.time()
    while simgr.active:
        simgr.step()
    ending_time = time.time()

    results['time taken'] = ending_time-beginning_time
    api.store(NAME,oid,results,opts)
    return True
    
