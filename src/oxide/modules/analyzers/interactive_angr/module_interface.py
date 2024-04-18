DESC = "Use this module to have an interactive exploration with Angr"
NAME = "interactive_angr"

from core import api
from core.libraries.angr_utils import init_angr_project, process_cfg
import logging
import angr

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
    """
    if opts['start_vaddr'] == " ":
        logger.fatal("Missing start address!")
        return False
    try:
        hex_val_start = int(opts['start_vaddr'],16)
    except TypeError:
        logger.fatal("Invalid start address")
        return False
    except ValueError:
        print("Something is still weird with getting address")
        #working on getting address properly
    logger.debug(f"Starting with vaddr {opts['start_vaddr']}")
    results = {"results":{}}
    oid_list = api.expand_oids(oid_list)
    # work through each oid, but probably should only have one oid as input
    for oid in oid_list:
        header = api.get_field("object_header",oid,oid) #get file header
        data = api.get_field(api.source(oid), oid, "data", {}) #get file data
        f_name = api.get_field("file_meta", oid, "names").pop()
        f_name = api.tmp_file(f_name, data) #make temp file for anger project
        angr_proj = init_angr_project(f_name, header) #angr project
        
        #make sure the addr is within range
        max_addr = hex(angr_proj.loader.main_object.max_addr)
        min_addr = hex(angr_proj.loader.main_object.min_addr)
        if not (int(max_addr,16) > int(opts['start_vaddr'],16) and int(min_addr,16) <= int(opts['start_vaddr']),16):
            logger.fatal(f"Given starting address is out of bounds for {oid}!")
            return False

        #try and run angr through that address!
        state = angr_proj.factory.blank_state(addr=opts['start_vaddr'])
    return results
