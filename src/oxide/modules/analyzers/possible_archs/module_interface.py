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
        archs = {}

        # Header
        try:
            header = api.get_field("object_header", oid, oid)
            archs["ARCH_HEADER"] = [header.machine] if header.machine != "Unknown" else None
        except Exception:
            archs["ARCH_HEADER"] = None
        
        # CPU_REC2
        archs["ARCH_CPU_REC2"] = api.get_field('cpu_rec', oid, 'cpu_rec2', {"mode": "cpu_rec2"})

        # Check Strings
        arch_strings = api.retrieve('strings_components_finder', oid, {"component": "architecture"})
        archs["ARCH_STRINGS"] = list(arch_strings.keys()) if arch_strings else None

        # Check strings for cores
        arch_cores = api.retrieve('strings_components_finder', oid, {"component": "architecture", "mode": "possible"})
        archs["ARCH_CORES"] = list(arch_cores.keys()) if arch_cores else None


        results[oid] = archs

    return results
