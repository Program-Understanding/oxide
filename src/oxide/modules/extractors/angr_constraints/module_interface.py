AUTHOR="KEVAN"
DESC="Use this module to view information regarding constraints on an OID from angr. Returns count of constraint types and constraints generated"
NAME="angr_constraints"

class Timeout(Exception):
    pass

from core import api
from constraints_helper import count_classes

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"timeout": {"type": float, "mangle": True, "default": 120}}

def documentation():
    return {"description":DESC,
            "opts_doc": opts_doc,
            "private": False,
            "set": False,
            "atomic":True
            }

start_time = float()
f_name = ""
oid=""
timeout=float()

def k_step_func(simmgr):
    global start_time
    global timeout

    if time.time() - start_time > timeout: #checking timeout limit
        start_time = None
        simmgr.move(from_stash="active", to_stash="deadend")
        raise Timeout
    return simmgr

def process(oid, opts):
    """
     This function will accept an oid and give back a dictionary
    which contains information gotten from angr regarding the constraints
    angr constructed upon running its symbolic execution.

    The return is a count of each type of constraint that angr returned,
    such as bitvectors, strings, etc. and the constraints themselves both
    in claripy format and z3, where the z3 output is put into a Z3 solver
    and the sexpr() is printed.
    """
    #this function could be better. currently turns classes into strings
    #which is then roughly scanned for an ast type. but could be more
    #fine grain
    global timeout
    global start_time
    import time
    import logging
    import angr
    import claripy
    import z3
    timeout = opts["timeout"]

    data = api.get_field(api.source(oid), oid, "data", {}) #get file data
    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data) #make temp file for angr project
    #angr_proj = init_angr_project(f_name, header) #angr project seemingly not working right
    #logger stuff from init_angr_project() that seems useful
    cle_logger = logging.getLogger("cle")
    cle_logger.setLevel(50)
    angr_logger = logging.getLogger("angr")
    angr_logger.setLevel(50)
    claripy_logger = logging.getLogger("claripy")
    claripy_logger.setLevel(50)
    pyvex_logger = logging.getLogger("pyvex.lifting.libvex")
    pyvex_logger.setLevel(50)
    pyvex_logger = logging.getLogger("pyvex.lifting.util")
    pyvex_logger.setLevel(50)
    identifier_logger = logging.getLogger("angr.analyses.identifier.identify")
    identifier_logger.setLevel(50)
    output_dict = {}
    #start the process of running the actual simulation manager
    proj = angr.Project(f_name)
    state = proj.factory.entry_state()
    simgr = proj.factory.simulation_manager(state)
    # implement this key line to limit RAM usage so that the kernel doesn't kill the process
    simgr.use_technique(angr.exploration_techniques.MemoryWatcher(min_memory=2048))
    start_time = time.time()
    try:
        while simgr.active:
            simgr.step()
    except Timeout as e:
        logger.warning(f"{timeout} second angr timeout limit reached {f_name}:{oid}")
    except Exception as e:
        logger.warning(f"angr error with {f_name}:{oid}::{e}")
        return False
    if len(simgr.deadended) == 0:
        logger.debug(f"No deadends for {f_name}:{oid}")
        return False
    for s in range(len(simgr.deadended)): #s is state number
        state = simgr.deadended[s]
        output_dict["deadend " + str(s)] = {}
        cons = []
        cl_cons = []
        try:
            for c in state.solver.constraints:
                cl_cons.append(c)
                cons.append(claripy.backends.z3.convert(c))
        except Exception as e:
            logger.debug(f"error with converting states for {f_name}:{oid}")
            output_dict["deadend " + str(s)]["claripy"] = "None"
        con_trees = set() #getting unique entries
        for co in cl_cons:
            con_trees.add(str(co))
        output_dict["deadend " + str(s)]["claripy"] = con_trees
        try:
            solver = z3.Solver()
            solver.add(z3.And(cons))
            if solver.check() == z3.sat:
                m =solver.model()
                if len(m)>0:
                    #z3d = {}
                    #z3d["sexpr"] = m.sexpr() 
                    #z3d["model"] = str(list(m)) #convert from ctype pointer
                    output_dict["deadend " + str(s)]["z3"] = m.sexpr() #used to be z3d
                    continue
                output_dict["deadend " + str(s)]["z3"] = "None"
        except Exception:
            logger.debug(f"error with z3 solver for {f_name}:{oid}")
            output_dict["deadend " + str(s)]["z3"] = "None"

    logger.debug(f"Finished with {f_name} with oid {oid}, beginning counting...")
    counts = {}
    for deadend in output_dict: #iterate through each deadend state
        if output_dict[deadend]["claripy"] == 'None':
                continue #skip if a backend errors
        for s in output_dict[deadend]["claripy"]:
            count_classes(s,counts)
        count_classes(output_dict[deadend]["z3"],counts)
    if counts == {}:
        counts = "No constraints"
        logger.debug(f"Could not generate counts for {f_name}:{oid}")
    api.store(NAME,oid,{"counts":counts,"constraints":output_dict},opts)
    del angr, claripy, z3
    return True
