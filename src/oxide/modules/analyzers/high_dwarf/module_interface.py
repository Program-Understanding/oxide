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

DESC = "Analyze high-level information from dwarf information"
NAME = "high_dwarf"

import logging

from typing import Dict, Any

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"disassembler": {"type": str, "mangle": False, "default": "ghidra"}}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True}


def results(oid_list, opts):
    logger.debug("results()")

    res = {}
    for oid in oid_list:
        header = api.get_field("object_header", oid, oid)
        if not header:
            logger.debug("No header found (%s)", oid)
            continue

        # Extract dwarf information
        debug_info = api.get_field("parse_dwarf", [oid], ".debug_info")

        if debug_info is None:
            logger.debug("%s has no debug information present.", oid)
            continue

        functions = []
        inlined_funcs = []

        for cu_offset in debug_info:
            for die_offset in debug_info[cu_offset]:
                if debug_info[cu_offset][die_offset]["Tag"] == 'DW_TAG_subprogram':
                    fun_name = None
                    fun_low_pc = None  # address range of function in binary
                    fun_high_pc = None
                    for pair in debug_info[cu_offset][die_offset]["Attributes"]:
                        if pair[0] == 'DW_AT_low_pc':
                            fun_low_pc = int(pair[1], 16)
                        if fun_low_pc and pair[0] == 'DW_AT_high_pc':
                            # relative offset from low, these should be requested in the correct order searching for low then high
                            fun_high_pc = int(pair[1], 16) + fun_low_pc
                        if pair[0] == 'DW_AT_name':
                            fun_name = pair[1]

                        functions.append((fun_name,
                                          header.get_offset(fun_low_pc),
                                          header.get_offset(fun_high_pc)))

                elif debug_info[cu_offset][die_offset]["Tag"] == 'DW_TAG_inline_subroutine':
                    abst_origin = None
                    fun_low_pc = None
                    fun_high_pc = None
                    for pair in debug_info[cu_offset][die_offset]["Attributes"]:
                        if pair[0] == 'DW_AT_abstract_origin':
                            abst_origin = pair[1]
                        if pair[0] == 'DW_AT_low_pc':
                            fun_low_pc = pair[1]
                        if pair[0] == 'DW_AT_high_pc':
                            fun_high_pc = pair[1] + fun_low_pc

                        inlined_funcs.append((abst_origin,
                                              header.get_offset(fun_low_pc),
                                              header.get_offset(fun_high_pc)))

        """
        for entry, cu in debug_info.items():
            if entry == "offset":
                continue

            for die_offset, die in cu["dies"].items():
                if (die["die_tag"] == "DW_TAG_subprogram"):
                    fun_name = None
                    fun_low_pc = None  # address range of function in binary
                    fun_high_pc = None
                    for die_attr_offset, attr in die['die_attributes'].items():
                        #  We are not concerned with source line number or file
                        #  Decl_line, Decl_file, Sibling, and Frame_base
                        aname = attr["attr_name"]
                        if (aname == "DW_AT_name"):
                            fun_name = attr["attr_desc"]
                        elif (aname == 'DW_AT_low_pc'):
                            fun_low_pc = int(attr["attr_desc"], 16)
                        elif (aname == 'DW_AT_high_pc'):
                            fun_high_pc = fun_low_pc + int(attr["attr_desc"], 16)  # high is offset from low
                    functions.append((fun_name,
                                      header.get_offset(fun_low_pc),
                                      header.get_offset(fun_high_pc)))
                elif (die["die_tag"] == "DW_TAG_inlined_subroutine"):
                    abst_origin = None  # Unclear what this means
                    fun_low_pc = None  # address range of function in binary
                    fun_high_pc = None
                    for die_attr_offset, attr in die['die_attributes'].items():
                        # No concerned with call file and call line
                        aname = attr["attr_name"]
                        if (aname == 'DW_AT_abstract_origin'):
                            abst_origin = attr["attr_desc"]
                        elif (aname == 'DW_AT_low_pc'):
                            fun_low_pc = int(attr["attr_desc"], 16)
                        elif (aname == 'DW_AT_high_pc'):
                            fun_high_pc = fun_low_pc + int(attr["attr_desc"], 16)
                    inlined_funcs.append((abst_origin,
                                          header.get_offset(fun_low_pc),
                                          header.get_offset(fun_high_pc)))
        """

        res[oid] = {"functions": functions,
                    "inlined_functions": inlined_funcs}
    return res
