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

DESC = " This module will return hashes of each section"
NAME = "section_hashes"
USG = "This module returns a dictionary containing the SHA-1 hash value for each section within each individual binary file. Each OID has a nested dictionary \
with section names as keys and their corresponding SHA-1 hash values"

import logging
import hashlib

from typing import Dict, Any, List

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "Usage": USG}


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """ Iterate through sections, computing hashes
    """
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        header = api.get_field("object_header", oid, oid)
        if not header:
            continue

        src = api.source(oid)
        data = api.get_field(src, oid, "data", {})
        if not data:
            continue

        hashes = {}
        for sec_name in header.section_info:
            start = header.section_info[sec_name]["section_offset"]
            length = header.section_info[sec_name]["section_len"]
            if length:
                s_data = data[start: start + length]
                if s_data:
                    hashes[sec_name] = hashlib.sha1(s_data).hexdigest()
                else:
                    hashes[sec_name] = 0
            else:
                hashes[sec_name] = 0
        results[oid] = hashes

    return results
