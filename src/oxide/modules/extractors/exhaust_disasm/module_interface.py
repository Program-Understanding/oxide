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

DESC = " This module retrieves the disassembly starting at every byte in an object file."
NAME = "exhaust_disasm"
USG = "This module takes a collection of binary files and uses the specified disasembler option, either capstone or xed, and returns a \
dictionary with the disassembled instructions where each byte's address is used as the object key and the value contains information about \
each instruction at that address"

import logging
import ctypes

from typing import Optional, Dict, Any

logger = logging.getLogger(NAME)
logger.debug("init")

AVAILABLE = ["xed", "capstone"]

try:
    import capstone
except ModuleNotFoundError:
    AVAILABLE.remove("capstone")
    logger.info("Unable to import Capstone.")

try:
    import pyxed
except ModuleNotFoundError:
    AVAILABLE.remove("xed")
    logger.info("Unable to import PyXED.")

if not AVAILABLE:
    raise ModuleNotFoundError("PyXED and Capstone are missing.")

from oxide.core import api, otypes
from oxide.core.libraries.disasm_utils import disassemble_wcap, disassemble_wxed

opts_doc = {"disassembler": {"type": str, "mangle": False, "default": "ghidra"},
            "decoder": {"type": str, "mangle": False, "default": "capstone"}}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage": USG}


def process(oid: str, opts: dict):
    logger.debug("process()")

    header = api.get_field("object_header", oid, oid)
    if not header: return False

    file_size = api.get_field("file_meta", oid, "size")
    data = api.get_field("files", oid, "data")

    decoder = opts["decoder"]

    if decoder not in AVAILABLE:
        return None

    ranges = []
    for _, sect_info in header.section_info.items():
        if sect_info["section_exec"]:
            # section is executable
            ranges.append((sect_info["section_offset"], sect_info["section_offset"] + sect_info["section_len"]))

    executable_offsets = []
    for section_range in ranges:
        # union all offsets from start to end of section
        executable_offsets += list(range(section_range[0], section_range[1]))
    if not executable_offsets: return False

    # perform decoding
    disasm = None  # assumed capstone or xed, only possible choice allowed
    if decoder == "capstone":
        disasm = disassemble_wcap(file_size, data, header, dict.fromkeys(executable_offsets, ""))
    elif decoder == "xed":
        disasm = disassemble_wxed(file_size, data, header, dict.fromkeys(executable_offsets, ""))
    else:
        logging.info("Invalid decodder selected")
        return False

    if disasm is None: return None
    result = {'instructions': disasm}
    api.store(NAME, oid, result, opts)
    return True
