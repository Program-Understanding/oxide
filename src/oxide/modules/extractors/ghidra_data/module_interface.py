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

desc = "This module uses ghidra to extract data references and pointers via module:ghidra_export"
# Output of ghidra_export is parsed ghidra database that describes data, sections, etc
name = "ghidra_data"

import logging
import ghidra_pointers

from typing import Dict, Any

from oxide.core import api

logger = logging.getLogger(name)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    return {"description": desc, "opts_doc": opts_doc, "private": False, "set": False, "atomic": True}


def process(oid: str, opts: dict) -> bool:
    logger.debug("process()")

    ghidra_export = api.retrieve("ghidra_export", oid)
    ghidra_cfg = api.get_field("ghidra_disasm", oid, "original_blocks")
    load_addr = api.get_field("ghidra_disasm", oid, "meta")["load_addr"]

    if not ghidra_export:
        logger.debug("XML information not found")
        return False

    if not ghidra_cfg:
        logger.debug("No CFG extracted from Ghidra.")
        return False

    # Access to header interface
    header = api.get_field("object_header", oid, oid)
    if not header:
        return False

    result = ghidra_pointers.extract(header, ghidra_export, ghidra_cfg, load_addr)
    if result is None: return False
    api.store(name, oid, result, opts)
    return True
