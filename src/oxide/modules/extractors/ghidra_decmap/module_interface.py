"""
Copyright 2023 National Technology & Engineering Solutions
of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS,
the U.S. Government retains certain rights in this software.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
"""

DESC = "This module uses ghidra to associate lines of decompilation to addresses"
NAME = "ghidra_decmap"
CATEGORY = "decompiler"

import logging
import os
import multiprocessing
import platform

from typing import Dict, Any

from oxide.core import api
import ghidra_decompiler_mapping

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"version": {"type": int, "mangle": True, "default": -1},
            "rebase-off": {"type": bool, "mangle": True, "default": False}}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": False, "category": CATEGORY}


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

    project = api.ghidra_project
    operating_system = platform.system()
    if 'Linux' in operating_system or 'Darwin' in operating_system:
        ghidra_decompiler_mapping.GHIDRA_PATH = os.path.join(path, "support", "analyzeHeadless")
    elif 'Windows' in operating_system:
        ghidra_decompiler_mapping.GHIDRA_PATH = os.path.join(path, "support", "analyzeHeadless.bat")

    if not os.path.exists(ghidra_decompiler_mapping.GHIDRA_PATH):#Checks to see if the path exists
        logger.error('The provided ghidra path is incorrect, please make sure everything is spelt correctly and the path points to the folder that contains ghidraRun: \' %s \' ', path)
        return False
    
    # disambiguates database name between cores
    ghidra_decompiler_mapping.GHIDRA_Project_NAME = f"{project}_{multiprocessing.current_process().name}"
    ghidra_decompiler_mapping.GHIDRA_Project_PATH = api.scratch_dir
    ghidra_decompiler_mapping.SCRIPTS_PATH = api.scripts_dir
    ghidra_decompiler_mapping.EXPORT_SCRIPT_PATH = "decompile_mapping.py"
    ghidra_decompiler_mapping.GHIDRA_TMP_FILE = os.path.join(api.scratch_dir, f"DecompilerMapping-{multiprocessing.current_process().name}.json")
    print(ghidra_decompiler_mapping.GHIDRA_TMP_FILE)
    # Toggles whether module returns vaddr or file offsets
    ghidra_decompiler_mapping.OFFSETS_OFF = opts['rebase-off']

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
    result = ghidra_decompiler_mapping.extract(f_name, header)
    # File cleaned up in extract

    if result is None: return False
    api.store(NAME, oid, result, opts)
    return True
