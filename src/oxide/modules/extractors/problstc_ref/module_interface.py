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

DESC = " This module uses probablistic disassembly docker file extract a disassembly."
NAME = "problstc_ref"
CATEGORY = "disassembler"

import logging
import subprocess

from typing import Dict, Any

from oxide.core import api
import probablistic_extract

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


try:
    probablistic_extract.test_docker()
except subprocess.CalledProcessError:
    logger.error("Docker not configured.")
    raise ImportError("Docker not configured.")


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY}


def process(oid: str, opts: dict) -> bool:
    logger.debug("process()")

    if api.probdisasm_image == "":
        logger.debug("No probablistic disassembler (superset disasm) image set.")
        return False

    probablistic_extract.PROBDISASM_IMAGE = api.probdisasm_image

    src = api.source(oid)
    data = api.get_field(src, oid, "data", {})
    if not data:
        logger.debug("Not able to process %s", oid)
        return False

    header = api.get_field("object_header", oid, oid)
    if not header:
        logger.info("No header found.")
        return False

    ex_disasm = api.retrieve("exhaust_disasm", oid)
    if ex_disasm is None:
        logger.info("No exhaustive disassembly found.")
        return False

    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data)

    result = probablistic_extract.extract(f_name, ex_disasm, header, api.scratch_dir)
    if result is None: return False
    api.store(NAME, oid, result, opts)
    return True
