import logging
import os
import multiprocessing
from typing import Dict, Any
from oxide.core import api, sys_utils
import subprocess
import json
DESC = "This module can run any valid Ghidra script that is stored in the scripts directory (for now)"
NAME = "ghidra_script"
CATEGORY = "disassembler"
USG =   "This module takes a collection of binary files and analyzes them using Ghidra and Ghidra postscripts. It returns a dictionary that\
        is specified in the Ghidra postscript. The dictionary is stored in the database under the module name. The dictionary is stored\
        under the oid of the binary file."


logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"version": {"type": int, "mangle": True, "default": -1},
            "rebase-off": {"type": bool, "mangle": True, "default": False},
            "script": {"type": str, "mangle": True, "default": "ghidra_extract.java"},
            "arch": {"type": str, "mangle": True, "default": ""}
           }


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": False, "category": CATEGORY, "Usage": USG}

def process(oid: str, opts: dict) -> bool:
    logger.debug("process()")
    
    result = {}
    path = None
    # tracks version of ghidra that was used to extract instructions
    if opts['version'] > 0:
        try:
            path = getattr(api, "ghidra_path{}".format(opts['version']))
        except AttributeError:
            logger.info("Selected ghidra_path# not found, defaulting to ghidra_path")
            path = getattr(api, "ghidra_path")
    else:
        path = getattr(api, "ghidra_path")

    if not path:
        logger.warning('No ghidra path was set or configured to None')
        return False

    logger.info("Using ghidra path: %s", path)    
    project = api.ghidra_project
    ghidra_path = os.path.join(path, "support", "analyzeHeadless")
    
    if not os.path.exists(ghidra_path):#Checks to see if the path exists
        logger.error('The provided ghidra path is incorrect, please make sure everything is spelt correctly and the path points to the folder that contains ghidraRun: \' %s \' ', path)
        return False
    
    # disambiguates database name between cores
    project_name = "{}_{}".format(project, multiprocessing.current_process().name)
    project_path = api.scratch_dir
    scripts_path = api.scripts_dir
    extract_script = opts['script']
    tmp_json = os.path.join(api.scratch_dir, "ghidra_tmp.json")
    print("Extracting with script: ", extract_script)
    print("Temporarily storing in file: ", tmp_json)
    # Check that the script exists
    if not os.path.exists(os.path.join(scripts_path, extract_script)):
        logger.error('The provided script path is incorrect, please make sure everything is spelt correctly and the path points to the folder that contains the script: \' %s \' ', extract_script)
        return False

    # Toggles whether module returns vaddr or file offsets
    offsets_off = opts['rebase-off']

    # Get the data from the source
    src = api.source(oid)
    data = api.get_field(src, oid, "data", {})
    if not data:
        logger.debug("Not able to process %s", oid)
        return False

    # Generate a temporary file from the stored data.
    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data)

    # Check that the header exists and that the format is known.
    header = api.get_field("object_header", oid, oid)
    if not header:
        logger.warning('No header found for %s in %s', oid, NAME)
        return False
    if not header.known_format:
        logger.warning("File Sample unknown format, Ghidra returning empty. (%s)", )
        return None
    

    cmd = "{} {} {} ".format(ghidra_path, project_path, project_name) + \
          "-import {} -overwrite -scriptPath {} ".format(f_name, scripts_path)   + \
          "-postScript {} {}".format(extract_script, tmp_json)
    print(cmd)
    with open(os.devnull, "w") as null:
        try:
            output = subprocess.check_output(cmd, universal_newlines=True, shell=True, stderr=null)
        except subprocess.CalledProcessError as e:
            logger.warning(e.output)
    with open(tmp_json, "r") as f:
        result = json.loads(f.read())
        
    sys_utils.delete_file(tmp_json) 
    if result is None: return False
    api.store(NAME, oid, result, opts)
    return True
