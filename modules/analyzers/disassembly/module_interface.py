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

DESC = " This module retrieves the disassembly of a given object file using a tool to guide decoding."
NAME = "disassembly"

import logging
import ctypes

from typing import Optional, List, Dict, Any

logger = logging.getLogger(NAME)
logger.debug("init")

AVAILABLE = ["xed", "capstone"]

try:
    import capstone
except ModuleNotFoundError:
    AVAILABLE.remove("capstone")
    logger.warning("Unable to import Capstone.")

try:
    import pyxed
except ModuleNotFoundError:
    AVAILABLE.remove("xed")
    logger.warning("Unable to import PyXED.")

if not AVAILABLE:
    raise ModuleNotFoundError("PyXED and Capstone are missing.")

from core import api, otypes
from core.libraries.disasm_utils import disassemble_wcap, disassemble_wxed

opts_doc = {"disassembler": {"type": str, "mangle": False, "default": "ghidra_disasm"},
            "decoder": {"type": str, "mangle": False, "default": "capstone"}}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True}


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    logger.debug("results()")
    disassembler = opts["disassembler"]
    disassemblers = api.get_available_modules("disassembler")
    if disassembler not in disassemblers:
        logger.info("Invalid option `%s` for disassembler, options are %s", disassembler,
                                                                            disassemblers)
        logger.info(f"Option may not have loaded correct, please check `run {disassembler}`")

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        header = api.get_field("object_header", oid, oid)
        if not header:
            logger.info('No header found for {}'.format(oid))
            continue

        file_size = api.get_field("file_meta", oid, "size")
        data = api.get_field("files", oid, "data")

        decoder = opts["decoder"]

        tool_insns = None
        if not disassembler or disassembler == "ghidra_disasm":
            tool_insns = api.get_field("ghidra_disasm", oid, "instructions", opts)
        elif disassembler == "probablistic_disasm":
            # TODO: switch this to default disassembler
            tool_insns = api.get_field("probablistic_disasm", oid, "instructions", opts)
        elif disassembler in disassemblers:
            tool_insns = api.get_field(disassembler, oid, "instructions", opts)
        else:
            # invalid disassembler option
            tool_insns = None

        if not tool_insns:
            continue

        if 'meta' in tool_insns: del tool_insns['meta']

        disasm = None
        # perform decoding
        if decoder == "capstone":
            disasm = disassemble_wcap(file_size, data, header, tool_insns)
        elif decoder == "xed":
            disasm = disassemble_wxed(file_size, data, header, tool_insns)
        else:
            logger.info("Invalid decoder selected")

        if not disasm:
            continue

        results[oid] = {"instructions": disasm}

    return results