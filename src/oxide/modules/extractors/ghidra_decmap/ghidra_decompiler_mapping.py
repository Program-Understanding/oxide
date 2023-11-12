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

""" Wrapper for scripts for Ghidra, in which decompilation is associated with addresses
"""

import os
import subprocess
import json
import logging
import time

from oxide.core.libraries.ghidra_utils import get_file_offset

from typing import Optional

from oxide.core import sys_utils

NAME = "ghidra_decmap"
logger = logging.getLogger(NAME)


def extract_ghidra_decmap(file_test: str) -> Optional[str]:
    """ Run ghidra with arguments populated to execute script
    """
    cmd = "{} {} {} ".format(GHIDRA_PATH, GHIDRA_Project_PATH, GHIDRA_Project_NAME) + \
          "-import {} -overwrite -scriptPath {} ".format(file_test, SCRIPTS_PATH)   + \
          "-postScript {} {}".format(EXPORT_SCRIPT_PATH, GHIDRA_TMP_FILE)
    logger.info("cmd: %s", cmd)
    output = None
    with open(os.devnull, "w") as null:
        try:
            output = subprocess.check_output(cmd, universal_newlines=True, shell=True, stderr=null)
        except subprocess.CalledProcessError as e:
            logger.warning(e.output)
    return output


def extract(file_test: str, header: dict) -> dict:
    """ Runs instruction extraction from ghidraHEADLESS using a java language script
        Input -
            file_test - temporary file name to analyze
            header_interface (header) - header object using header utiility lib
    """
    output_map = {}
    output_map["meta"] = {}

    if not header.known_format:
        logger.info("File Sample is of unknown format, Ghidra returning empty output.")
        return None

    start = time.time()

    # Collect stdout from ghidra script to parse
    extract_ghidra_decmap(file_test)

    # parse output file
    try:
        raw = sys_utils.get_contents_of_file(GHIDRA_TMP_FILE).decode("utf-8")
    except AttributeError:
        logger.info("Ghidra tmp file (%s) not found", GHIDRA_TMP_FILE)
        return None

    output_map['decompile'] = {}
    try:
        mapping = json.loads(raw)
        LOAD_ADDR = mapping['meta']['load_addr']
        LOAD_ADDR = int(LOAD_ADDR, 16)

        del mapping['meta']

        for elem in mapping:
            if elem == 'None':
                continue
            output_map['decompile'][get_file_offset(int(elem, 16), header, LOAD_ADDR)] = mapping[elem]
    except json.decoder.JSONDecodeError:
        logger.info("Json decoding error encountered on Ghidra tmp file.")
        return None

    # Clean up temp file
    logger.debug("Removing tmp file")
    sys_utils.delete_file(GHIDRA_TMP_FILE)

    end = time.time()
    output_map["meta"]["time"] = end - start

    return output_map
