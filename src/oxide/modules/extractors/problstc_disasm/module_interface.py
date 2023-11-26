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

DESC = " This module computes probablistic disassembly based on module:exhaust_disasm."
NAME = "problstc_disasm"
CATEGORY = "disassembler"
USG = "This module takes a collection of binary files and analyzes them using the exhaust_disasm module. It returns "

import logging

from typing import Dict, Any

from oxide.core import api
import speculative

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY, "usage": USG}


def process(oid: str, opts: dict) -> bool:
    """ Compute probablistic disassembly from exhaustive disassembly
            https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
    """
    logger.debug("process()")

    src = api.source(oid)
    data = api.get_field(src, oid, "data", {})
    if not data:
        logger.debug("Not able to process %s", oid)
        return False

    header = api.get_field("object_header", oid, oid)
    if not header:
        logger.info('No header found for %s in %s', oid, NAME)
        return False

    disasm = api.retrieve("exhaust_disasm", oid)
    if not disasm or 'instructions' not in disasm:
        logger.info("No disassembly found for %s" % disasm)
        return False
    disasm = disasm['instructions']

    try:
        result = speculative.extract(disasm)
    except ZeroDivisionError:
        # In some cases probalistic disassemly hits division by 0 in adjust code probs
        # this needs serious rethinking
        result = None
    if not result: return False
    api.store(NAME, oid, result, opts)
    return True
