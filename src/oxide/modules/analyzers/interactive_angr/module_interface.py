DESC = "Use this module to have an interactive exploration with Angr"
NAME = "interactive_angr"

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
    if opts['start_vaddr'] == " ":
        logger.error("Missing start address!")
        return False
    try:
        if (type(opts['start_vaddr']) is int):
            hex_val_start = hex(opts['start_vaddr'])
        else:
            hex_val_start = hex(int(opts['start_vaddr'],16)) #type coercion?
    except TypeError as err:
        logger.error(f"Invalid start address: Expecting either a hex or int offset")
        return False
    except ValueError:
        logger.debug(f"Error with starting address...")
        return False
        #working on getting address properly
    logger.debug(f"Starting with vaddr {opts['start_vaddr']}")
    results = {}
    oid_list = api.expand_oids(oid_list)
    # work through each oid, but probably should only have one oid as input
    for oid in oid_list:
        results[oid] = {}
        header = api.get_field("object_header",oid,oid) #interpret_elf.py
        data = api.get_field(api.source(oid), oid, "data", {}) #get file data
        f_name = api.get_field("file_meta", oid, "names").pop()
        f_name = api.tmp_file(f_name, data) #make temp file for anger project
        angr_proj = init_angr_project(f_name, header) #angr project
        
        #make sure the addr is within range
        max_addr = hex(angr_proj.loader.main_object.max_addr)
        min_addr = hex(angr_proj.loader.main_object.min_addr)
        if not (max_addr > hex_val_start and min_addr <= hex_val_start):
            logger.error(f"Given starting address is out of bounds for {oid}! Should be between {min_addr} and {max_addr}")
            return False

        #try and run angr through that address!
        state = angr_proj.factory.blank_state(addr=opts['start_vaddr'])
        simmgr = angr_proj.factory.simgr(state)
        while simmgr.active:
            simmgr.step()
            for thing in simmgr.stashes:
                for stte in simmgr.stashes[thing]:
                    constraints = [claripy.backends.z3.convert(c) for c in stte.solver.constraints]
                    logger.debug(f"{stte}:{thing} constraints:")
                    logger.debug(f"{z3.simplify(z3.And(constraints))}")
        for thing in simmgr.stashes:
                for stte in simmgr.stashes[thing]:
                    results[oid][thing] = {}
                    constraints = [claripy.backends.z3.convert(c) for c in stte.solver.constraints]
                    results[oid][thing]["constraints"] = z3.simplify(z3.And(constraints))
                    results[oid][thing]["stdin"] = stte.posix.dumps(0)
                    results[oid][thing]["stdout"] = stte.posix.dumps(1)
                    results[oid][thing]["stderr"] = stte.posix.dumps(2)
        error_int = 0
        for thing in simmgr.errored:
            results[oid][f"errored state {error_int}"] = {}
            constraints = [claripy.backends.z3.convert(c) for c in stte.solver.constraints]
            results[oid][f"errored state {error_int}"]["constraints"] = z3.simplify(z3.And(constraints))
            results[oid][f"errored state {error_int}"]["stdin"] = stte.posix.dumps(0)
            results[oid][f"errored state {error_int}"]["stdout"] = stte.posix.dumps(1)
            results[oid][f"errored state {error_int}"]["stderr"] = stte.posix.dumps(2)
    return results
