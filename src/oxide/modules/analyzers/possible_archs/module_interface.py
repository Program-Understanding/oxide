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

DESC = " This module is a template for analyzer, new analyzers can copy this format"
NAME = "possible_archs"

# imports
import logging

from typing import Dict, Any, List

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    """ Documentation for this module
        private - Whether module shows up in help
        set - Whether this module accepts collections
        atomic - TBD
    """
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True}


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """ Entry point for analyzers, these do not store in database
        these are meant to be very quickly computed things passed along
        into other modules
    """
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        oid_archs = {}

        # Header
        header = api.get_field("object_header", oid, oid)
        arch_header = [header.machine] if header.machine != "Unknown" else None

        if arch_header:
            for arch in arch_header:
                if arch in oid_archs:
                    oid_archs[arch].append("HEADER")
                else:
                    oid_archs[arch] = ["HEADER"]

        # CPU_REC'
        arch_cpu_rec = api.retrieve('cpu_rec', oid, {"mode": "cpu_rec2"})

        if arch_cpu_rec:
            for arch in arch_cpu_rec:
                if arch in oid_archs:
                    oid_archs[arch].append("CPU_REC")
                else:
                    oid_archs[arch] = ["CPU_REC"]

        arch_matches = api.retrieve('strings_components_finder', oid, {"component": "architecture"})
        arch_strings = list(arch_matches.keys()) if arch_matches else None

        if arch_strings:
            for arch in arch_strings:
                if arch in oid_archs:
                    oid_archs[arch].append("STRINGS")
                else:
                    oid_archs[arch] = ["STRINGS"]

        # Strings
        arch_matches = api.retrieve('strings_components_finder', oid, {"component": "architecture", "mode": "possible"})
        arch_core_strings = list(arch_matches.keys()) if arch_matches else None

        if arch_core_strings:
            for arch in arch_core_strings:
                if arch in oid_archs:
                    oid_archs[arch].append("STRINGS_CORE")
                else:
                    oid_archs[arch] = ["STRINGS_CORE"]

        results[oid] = oid_archs

    return results
