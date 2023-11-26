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

DESC = " This module uses the elf_parse module to extract features from the ELF header."
NAME = "elf"
USG = "This module takes an oid or a collection of oids that represent a file and returns a disctionary with information that describes \
each file if it is an ELF file using elf_parse"

import logging

from typing import Dict, Any

from interpret_elf import ElfRepr
from parse_elf import parse_elf
from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage" :USG}

def process(oid: str, opts: dict) -> bool:
    #logger.debug("process()")
    logger.debug("Processing oid %s", oid)
    src_type = api.get_field("src_type", oid, "type")

    if "ELF" not in src_type:
        return False

    src = api.source(oid)
    data = api.get_field(src, oid, "data", {})
    if not data:
        logger.debug("Not able to process %s", oid)
        return False

    result = parse_elf(data, oid)
    result["header"] = ElfRepr(result)

    api.store(NAME, oid, result, opts)
    return True