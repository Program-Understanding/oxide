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

DESC = "Extracts DWARF4/5 debug information from ELF binaries."
NAME = "dwarf5"

import logging
import os
import sys
import types
from typing import Any, Dict

from oxide.core import api
import extract
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc: Dict[str, Any] = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True}


def process(oid: str, opts: dict) -> bool:
    logger.debug("process(%s)", oid)

    src_type = api.get_field("src_type", oid, "type")
    if not src_type or "ELF" not in src_type:
        logger.info("oid (%s) is not ELF, skipping.", oid)
        return False

    src = api.source(oid)
    if not src:
        logger.debug("No source for oid %s", oid)
        return False

    data = api.get_field(src, oid, "data", {})
    if not data:
        logger.debug("No data for oid %s", oid)
        return False

    header = api.get_field("object_header", oid, oid)
    if header is None:
        logger.debug("No header for oid %s", oid)
        return False

    result = extract.parse_dwarf(oid, data, header)
    if result is None:
        return False

    api.store(NAME, oid, result, opts)
    return True
