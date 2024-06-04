AUTHOR="KEVAN"
DESC="Use this module to dump constraint information used by angr's backend Claripy and z3"
NAME="constraint_types"

from core import api
import logging
import angr
import claripy
import z3

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation():
    return {"description":DESC,
            "opts_doc": opts_doc,
            "private": False,
            "set": False,
            "atomic":True
            }

def results(oid_list: list, opts: dict):
    """Entry point for analyzers, these do not store in database
    these are meant to be very quickly computed things passed along
    into other modules

    This function will accept an OID list and give back a dictionary
    which contains information gotten from angr regarding the constraints
    angr generated during its symbolic execution of the program.
    Constraints are returned both in angr's native claripy format and the z3
    format that claripy uses in the backend (it converts to z3 inherently
    due to its use of z3)

    Results are separated by deadended state, then z3 and claripy, then
    each scopes further respective to the backend.
    """
    results = {}
    for oid in oid_list:
        results[oid] = {}
        data = api.get_field(api.source(oid), oid, "data", {}) #get file data
        f_name = api.get_field("file_meta", oid, "names").pop()
        f_name = api.tmp_file(f_name, data) #make temp file for anger project

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
        proj = angr.Project(f_name)
        logger.debug(f"{oid} entry addr: "+hex(proj.entry))
        state = proj.factory.entry_state()
        state.options |= {angr.sim_options.CONSTRAINT_TRACKING_IN_SOLVER}
        state.options -= {angr.sim_options.COMPOSITE_SOLVER}
        # todo keep track of what the constraints are at the end
        # then categorize them and send them back to the user
        # maybe in a dictionary like {category : number}

        simgr = proj.factory.simulation_manager(state)
        simgr.explore()

        for s in range(len(simgr.deadended)): #s is state number
            state = simgr.deadended[s]
            results[oid]['deadend ' + str(s)] = {}
            cons = []
            cl_cons = []
            for c in state.solver.constraints:
                cl_cons.append(c)
                cons.append(claripy.backends.z3.convert(c))
            con_trees = set() #getting unique entries
            cl_leafs = set() #because there are a lot of duplicates
            for co in cl_cons:
                if not co.concrete:
                    #don't worry about concrete vars
                    con_trees.add(c)
                    for co_l in co.recursive_leaf_asts:
                        cl_leafs.add(c)
            cl_d = {}
            cl_d["trees"] = con_trees if len(con_trees) > 0 else "None"
            cl_d["leafs"] = cl_leafs if len(cl_leafs) > 0 else "None"
            results[oid]['deadend ' + str(s)]["claripy"] = cl_d
            solver = z3.Solver()
            for c in cons:
                solver.add(c)
            if solver.check() == z3.sat:
                m = solver.model()
                if len(m)>0:
                    z3d = {}
                    z3d["sexpr"] = m.sexpr()
                    z3d["model"] = m
                    results[oid]['deadend ' + str(s)]["z3"] = z3d
                    continue
            results[oid]['deadend ' + str(s)]["z3"] = "None"
    return results
