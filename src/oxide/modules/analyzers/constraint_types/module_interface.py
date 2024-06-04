AUTHOR="KEVAN"
DESC="Use this module to dump the type of constraints used by angr's backend"
NAME="constraint_types"

from core import api
from core.libraries.angr_utils import init_angr_project, process_cfg
import logging
import angr
import claripy
import z3

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"start_vaddr": {"type": str, "mangle": False, "default": " "},
            "end_vaddr": {"type": str, "mangle": False, "default": " "}}

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

    This function will accept a starting address as input and pass it along
    to Angr to perform some symbolic execution. The starting address should
    be a function.
    """
    results = {}
    for oid in oid_list:
        results[oid] = {}
        header=api.get_field("object_header",oid,oid) #interpret_elf.py
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

        for s in range(len(simgr.deadended)):
            state = simgr.deadended[s]
            results[oid]['deadend ' + str(s)] = {}
            cons = []
            for c in state.solver.constraints:
                cons.append(claripy.backends.z3.convert(c))
            solver = z3.Solver()
            for c in cons:
                solver.add(c)
            if solver.check() == z3.sat:
                m = solver.model()
                if len(m)>0:
                    results[oid]['deadend ' + str(s)]["sexpr"] = m.sexpr()
                    results[oid]['deadend ' + str(s)]["model"] = m
                    continue
            results[oid]['deadend ' + str(s)] = "None"
    return results
