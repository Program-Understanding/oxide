DESC = " This module uses ghidra to run script that produces JSON output. Uses default file as arg1."
NAME = "ghidra_script"

import logging
import os
import multiprocessing

from typing import Dict, Any

import ghidra_runscript
from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"version": {"type": int, "mangle": True, "default": -1},
            "script": {"type": str, "mangle": True, "default": "none.py"},
            "args": {"type": str, "mangle": True, "default": ""}}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": False}


def process(oid: str, opts: dict) -> bool:
    logger.debug("process()")

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
    ghidra_runscript.GHIDRA_PATH = os.path.join(path, "support", "analyzeHeadless")
    # disambiguates database name between cores
    ghidra_runscript.GHIDRA_Project_NAME = "{}_{}".format(project, multiprocessing.current_process().name)
    ghidra_runscript.GHIDRA_Project_PATH = api.scratch_dir
    ghidra_runscript.SCRIPTS_PATH = api.scripts_dir
    ghidra_runscript.SCRIPT = opts["script"]
    ghidra_runscript.SCRIPT_ARGS = opts["args"]
    # Optional, script can ignore if using stdout
    ghidra_runscript.GHIDRA_TMP_FILE = os.path.join(api.scratch_dir, f"tmp-ghidra-{multiprocessing.current_process().name}.out")

    src = api.source(oid)
    data = api.get_field(src, oid, "data", {})
    if not data:
        logger.debug("Not able to process %s", oid)
        return False

    header = api.get_field("object_header", oid, oid)
    if not header:
        logger.warning('No header found for %s in %s', oid, NAME)
        return False

    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data)

    result = ghidra_runscript.extract(f_name, header)
    if result is None: return False
    api.store(NAME, oid, result, opts)
    return True
