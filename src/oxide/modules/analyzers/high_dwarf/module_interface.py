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

DESC = "Analyze high-level information from DWARF debug data (functions, inlined functions)."
NAME = "high_dwarf"

import logging

from typing import Dict, Any

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc: Dict[str, Any] = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True}


def results(oid_list: list, opts: dict) -> Dict[str, Any]:
    logger.debug("results()")

    res = {}
    for oid in oid_list:
        header = api.get_field("object_header", oid, oid)
        if not header:
            logger.debug("No header found (%s)", oid)
            continue

        # dwarf5 module stores DWARF info under the "dwarf5" module name
        debug_info = api.get_field("dwarf5", oid, ".debug_info")
        if debug_info is None:
            logger.debug("%s has no DWARF debug information.", oid)
            continue

        functions = []
        inlined_funcs = []

        for cu_offset, dies in debug_info.items():
            for die_offset, die in dies.items():
                tag = die.get("Tag", "")
                attrs = die.get("Attributes", [])

                if tag == "DW_TAG_subprogram":
                    fun_name = None
                    fun_low_pc = None
                    fun_high_pc = None
                    for attr_name, val in attrs:
                        if attr_name == "DW_AT_name":
                            fun_name = val
                        elif attr_name == "DW_AT_low_pc":
                            fun_low_pc = val
                        elif attr_name == "DW_AT_high_pc" and fun_low_pc is not None:
                            fun_high_pc = val + fun_low_pc
                    if fun_name and fun_low_pc is not None and fun_high_pc is not None:
                        functions.append((
                            fun_name,
                            header.get_offset(fun_low_pc),
                            header.get_offset(fun_high_pc),
                        ))

                elif tag == "DW_TAG_inlined_subroutine":
                    abst_origin = None
                    fun_low_pc = None
                    fun_high_pc = None
                    for attr_name, val in attrs:
                        if attr_name == "DW_AT_abstract_origin":
                            abst_origin = val
                        elif attr_name == "DW_AT_low_pc":
                            fun_low_pc = val
                        elif attr_name == "DW_AT_high_pc" and fun_low_pc is not None:
                            fun_high_pc = val + fun_low_pc
                    if abst_origin and fun_low_pc is not None and fun_high_pc is not None:
                        inlined_funcs.append((
                            abst_origin,
                            header.get_offset(fun_low_pc),
                            header.get_offset(fun_high_pc),
                        ))

        res[oid] = {"functions": functions, "inlined_functions": inlined_funcs}

    return res
