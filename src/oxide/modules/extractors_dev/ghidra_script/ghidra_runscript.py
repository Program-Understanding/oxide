""" Wrapper for scripts for Ghidra to run arbitrary user script.
"""

import os
import subprocess
import json
import logging
import time
import shlex

from typing import Optional, Tuple

from oxide.core.libraries.ghidra_utils import get_file_offset

NAME = "ghidra_disasm"
logger = logging.getLogger(NAME)

LOAD_ADDR = 0

# --------------------------- Tool 5: Ghidra -----------------------------------------


"""
    Persistent bugs:
        Ghidra 9.2.2 produces address "1000:0000" while 9.0.2 "004000000"
"""


def extract_ghidra_disasm(file_test: str) -> Optional[str]:
    cmd = f"{GHIDRA_PATH} {GHIDRA_Project_PATH} {GHIDRA_Project_NAME} " + \
          f"-import {file_test} -overwrite -scriptPath {SCRIPTS_PATH} "+ \
          f"-postScript {SCRIPT} {SCRIPT_ARGS}"
    logger.info("cmd: %s", cmd)
    output = None
    with open(os.devnull, "w") as null:
        try:
            output = subprocess.check_output(cmd, universal_newlines=True, shell=True, stderr=null)
        except subprocess.CalledProcessError as e:
            logger.warning(e.output)
    return output


def extract(file_test: str, header) -> dict:
    """ Runs instruction extraction from ghidraHEADLESS using a java language
        script.

        Input -
            file_test (file) - Sample using bap.run() which runs analyses
            header_interface (header) - header object using header utiility lib

        Returns -
            output_map (dict) - dictionary containing facts extracted from tool
    """
    output_map = {}
    output_map["meta"] = {}
    output_map["result"] = {}

    if not header.known_format:
        logger.warning("File Sample unknown format, Ghidra returning empty. (%s)", file_test)
        return None

    if not os.path.exists(os.path.join(SCRIPTS_PATH, SCRIPT)):
        logger.warning("Script file does not exist (%s)", os.path.join(SCRIPTS_PATH, SCRIPT))
        return None

    start = time.time()
    extract_script_dump = extract_ghidra_disasm(file_test)
    end = time.time()

    if not extract_script_dump:
        logger.warning("Ghidra extract script returned an error")
        return None

    output_map["result"] = extract_script_dump

    output_map["meta"]["time"] = end - start

    return output_map
