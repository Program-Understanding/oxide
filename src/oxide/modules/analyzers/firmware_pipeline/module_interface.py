""""
Copyright 2023 National Technology & Engineering Solutions",
of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS,",
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

DESC = "Performs feature extraction on binary extracting features relevant to conditional statements."
NAME = "lb_feature_extraction"

# imports
import logging

from typing import Dict, Any, List

import networkx as nx

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    """Documentation for this module
    private - Whether module shows up in help
    set - Whether this module accepts collections
    atomic - TBD
    """
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """Entry point for analyzers, these do not store in database
    these are meant to be very quickly computed things passed along
    into other modules
    """
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}

    for oid in oid_list:
        file_results= {}
        size = api.retrieve("size", oid)
        strings = api.retrieve("strings", oid)
        padding = api.retrieve("padding", oid)

        # Disasmemblers
        ghidra_disasm = api.retrieve('ghidra_disasm', oid)
        angr_disasm = api.retrieve('emu_angr_disasm', oid)
        
        # Preliminary Analysis
        file_results['Entropy'] = api.get_field("binwalk_utils", oid, "entropy")
        file_results['Signature'] = api.get_field("binwalk_utils", oid, "signature")
        file_results['Size'] = size
        file_results['Padding'] = padding
        # Architecture Detection
        file_results['Architecture'] = None
        file_results['Base Address'] = None

        # Disasm Analysis
        file_results['ghidra_disasm'] = ghidra_disasm
        file_results['angr_disasm'] = angr_disasm



        results[oid] = file_results

    return results