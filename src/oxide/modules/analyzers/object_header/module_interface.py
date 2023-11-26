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

DESC = " This module retrieves the correct general header object from different file types."
NAME = "object_header"
USG = "This module returns a dictionary that contains information extracted from the headers of each binary file within a collection which \
include python objects that contain detailed information about the headers and their memory addresses"

import logging

from typing import List, Any, Dict, Tuple

from oxide.core import api, otypes

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"fake": {"type": bool, "mangle": False, "default": False} }


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "Usage": USG}


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    logger.debug("results()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        header = None
        src_type = api.get_field("src_type", oid, "type")
        if 'PE' in src_type:
            header = api.get_field("pe", oid, "header")
        elif 'ELF' in src_type:
            header = api.get_field("elf", oid, "header")
        elif 'MACHO' in src_type or "OSX Universal Binary" in src_type:
            header = api.get_field("macho", oid, "header")
        if opts["fake"] and not header:
            data = api.get_field(api.source(oid), oid, "data")
            if data:
                header = fake_header(data)
        results[oid] = header

    return results


def fake_header(buf: bytes):
    class header:
        def get_code_chunks_of_section(section) -> List[Tuple[int, int]]:
            return [(0, len(buf))]

    h = header()
    h.insn_mode = 32 # default - 32 bit
    h.known_format = False
    sections = {}
    sections["none"] = {}
    sections["none"]['section_exec'] = True
    sections["none"]['section_addr'] = 0
    sections["none"]['section_offset'] = 0
    sections["none"]['section_len'] = len(buf)
    sections["none"]['section_end'] = len(buf)
    h.section_info = sections
    return h
