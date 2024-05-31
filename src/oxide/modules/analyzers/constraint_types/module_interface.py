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
        angr_proj = init_angr_project(f_name, header) #angr project

        state = angr_proj.factory.entry_state(args=[f_name])
        state.options |= {angr.sim_options.CONSTRAINT_TRACKING_IN_SOLVER}
        state.options -= {angr.sim_options.COMPOSITE_SOLVER}
        # todo keep track of what the constraints are at the end
        # then categorize them and send them back to the user
        # maybe in a dictionary like {category : number}

    return results
