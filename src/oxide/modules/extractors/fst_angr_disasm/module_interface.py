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

DESC = " This module uses angr to extract a disassembly."
NAME = "fst_angr_disasm"
CATEGORY = "disassembler"
USG = "This module takes a collection of binary files and calls the extract function and performs disassembly using angr. It returns a dictionary \
with information about each basic block within the binary including a list of destination block offsets that are reachable from each block \
and a list of instructions and their addresses."

import logging

from oxide.core import api
import fst_angr_extract

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY, "usage": USG}


def process(oid: str, opts: dict) -> bool:
    logger.debug("process()")

    src = api.source(oid)
    data = api.get_field(src, oid, "data", {})
    if not data:
        logger.debug("Not able to process %s", oid)
        return False
    src_type = api.get_field("src_type", oid, "type")
    header = api.get_field("object_header", oid, oid)
    if not header:
        logger.info('No header found for %s in %s', oid, NAME)
        return False
    header.type = src_type
    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data)

    result = fst_angr_extract.extract(f_name, header)
    if result is None: return False
    api.store(NAME, oid, result, opts)
    return True
