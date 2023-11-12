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

DESC = " This module determines if a PE file is packed or not. Experimentally usable for ELF/MACHO."
NAME = "packer_detect"
USG = "The module checks if each binary file is likely packed or not and returns the analysis as a dictionary of OID to result pairs indicating \
some information about the binary file including if it is likely packed or not, the number of bad sections, the number of executable \
sections, the number of imports, the number of known bad section names, the number of  non-standard section names, the number of sections \
with read, write and execute permissions and the number of standard section names all found in the binary."

import logging

from typing import Dict, Any, List

from oxide.core import api
import detect_packer

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "Usage": USG}

def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        file_meta = api.get_field('object_header', oid, oid)
        if not file_meta:
            logger.debug("Not able to process (%s)", oid)
            results[oid] = None

        data = api.get_field("files", oid, "data")
        if not data:
            logger.debug("no data for oid (%s)", oid)
            results[oid] = None

        result = detect_packer.detect_packer(file_meta, data)
        if not result:
            results[oid] = None
        results[oid] = result

    return results
