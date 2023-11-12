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

""" Wrapper for scripts for Ghidra to extract basic block and
    instructions
"""

import os
import subprocess
import json
import logging
import time
import re
from typing import Optional, Tuple

from oxide.core.libraries.ghidra_utils import get_file_offset

NAME = "string_reference"
logger = logging.getLogger(NAME)

LOAD_ADDR = 0

def extract_ghidra_disasm(file_test: str) -> Optional[str]:
    cmd = "{} {} {} ".format(GHIDRA_PATH, GHIDRA_Project_PATH, GHIDRA_Project_NAME) + \
          "-import {} -overwrite -scriptPath {} ".format(file_test, SCRIPTS_PATH)   + \
          "-postScript {} | grep RESULT".format(EXTRACT_SCRIPT)
    logger.info("cmd: %s", cmd)
    output = None
    with open(os.devnull, "w") as null:
        try:
            output = subprocess.check_output(cmd, universal_newlines=True, shell=True, stderr=null)
        except subprocess.CalledProcessError as e:
            logger.warning(e.output)
    return output

def _sort_lines(extract_lines: str) -> Tuple[list, list, list]:
    ghidra_str_ref = []
    for line in extract_lines.split('\n'):
        try:
            space_index = line.index(' ')
            temp = line[space_index + 1:]
            json.loads(line[space_index + 1:])
        except ValueError as e:
            continue
        except json.decoder.JSONDecodeError:
            logger.error("json decoding error %s", line[space_index + 1:])
            # ensure line can be decoded
            continue

        if line[0:7] == "RESULTS":
            ghidra_str_ref.append(line[space_index + 1:])
        else:
            logger.debug("Line is not instruction, block, or function - %s", line)

    return ghidra_str_ref

def _populate_str_map(ghidra_str_ref: list, header_interface, output_map: dict) -> None:
    if len(ghidra_str_ref) == 0:
        logger.info("No str_ref found in Ghidra.")
        return

    for line in ghidra_str_ref:
        if len(line) < 1:
            continue

        try:
            str_ref_list = json.loads(line)
            # TODO:: check instruction format len of json
            instruction_address = str_ref_list[0]
            str_ref_address = str_ref_list[1]
            ref_string = str_ref_list[2]
        except ValueError:
            logger.warning("Instruction address is not valid %s", inst_list[0])
            output_map["instructions"] = {}  # reset dictionary
            return
        output_map["string_reference"][instruction_address] = {
            "reference_address": str_ref_address,
            "reference_string": ref_string
        }

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
    output_map["string_reference"] = {}

    if not header.known_format:
        logger.warning("File Sample unknown format, Ghidra returning empty. (%s)", file_test)
        return None

    start = time.time()
    extract_script_dump = extract_ghidra_disasm(file_test)
    end = time.time()

    if not extract_script_dump:
        logger.warning("Ghidra extract script returned an error")
        return None

    str_ref = _sort_lines(extract_script_dump)

    if len(str_ref) > 0:
        _populate_str_map(str_ref, header, output_map)
    return output_map