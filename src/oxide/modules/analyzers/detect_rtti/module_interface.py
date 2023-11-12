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

DESC = " This module will detect the use of RTTI from GCC (existance of .data.rel.ro)"
NAME = "detect_rtti"
USG = "This module returns a dictionary with the oids as keys and a boolean value indicating \
whether or not the correspondong file contains RTTI."

import logging

from typing import Dict, Any, List

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

"""
    Known problems:
        Only works on ELF, MACHO has a different format
"""


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "Usage" : USG}


def results(oid_list: List[str], opts: dict) -> Dict[str, bool]:
    """ Process information from available extractors to detect RTTI
        Parameters
            oid_list: list[str] - list of oxide ids used to process for RTTI
            opts: dictionary - dictionary of module options
    """
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        header = api.get_field("object_header", oid, oid)
        if not header:
            results[oid] = False
            continue

        src = api.source(oid)
        data = api.get_field(src, oid, "data", {})
        if not data:
            results[oid] = False
            continue

        if ".data.rel.ro" not in header.section_info:
            # if no data.rel.ro conclude that there is no RTTI in binary
            results[oid] = False
            continue
        relro_info = header.section_info[".data.rel.ro"]

        # Bytes for relro section, potentially empty if bad indicies
        relro_section = data[relro_info["section_offset"]:
                             (relro_info["section_offset"] + relro_info["section_len"])]

        if header.is_64bit() is True:
            rtti_pointer_offset = 8
            pointer_size = 8
        else:
            # assume 32 bit
            rtti_pointer_offset = 4
            pointer_size = 4

        relro_at_offset = relro_section[rtti_pointer_offset:
                                        rtti_pointer_offset + pointer_size]

        # rtti[oid] = whether or not the bytes are 0x00,
        # if bytes are anything other than 0x00{pointer_size} then has RTTI
        results[oid] = not (relro_at_offset == b"\x00" * pointer_size)

    return results
