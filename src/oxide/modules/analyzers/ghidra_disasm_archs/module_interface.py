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

DESC = ""
NAME = "ghidra_disasm_archs"

# imports
import logging

from typing import Dict, Any, List

from oxide.core import api
# import ghidra_arch_lookup
from ghidra_arch_lookup import ghidra_arch_lookup

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"archs": {"type": str, "mangle": True, "default": "none"}}


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

    archs = opts.get("archs", [])

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        results[oid] = {}
        disasm = {
            "RESULT": "FAIL",
            "PASS": {},
            "FAIL": []
        }
        proccessor_attempts = []

        # Check DISASM w/ no arch
        try:
            disasm_result = api.retrieve('ghidra_disasm', oid)
            if disasm_result is None or disasm_result == {} or disasm_result["original_blocks"] == {}:
                disasm["FAIL"].append("DEFAULT")
            else:
                disasm["PASS"]["DEFAULT"] = {
                    "FEATURES": api.get_field("tiknib_features", oid, oid),
                    "SOURCE": "DEFAULT"
                }
                disasm["RESULT"] = "PASS"
        except:
            disasm["FAIL"].append("DEFAULT")

        # Check FILE ARCHs
        for arch_guess in archs:
            arch_guess = arch_guess.upper()
            if arch_guess in ghidra_arch_lookup:
                ghidra_archs = list(ghidra_arch_lookup[arch_guess].keys())

                for ga in ghidra_archs:
                    if ga not in proccessor_attempts:
                        try:
                            disasm_result = api.retrieve('ghidra_disasm', oid, {"processor": ga})
                            if disasm_result is None or disasm_result["original_blocks"] == {}:
                                disasm["FAIL"].append(ga)
                            else:
                                disasm["PASS"][ga] = {
                                    "FEATURES": api.get_field("tiknib_features", oid, oid, {"processor": ga}),
                                    "SOURCE": arch_guess
                                    }
                                disasm["RESULT"] = "PASS"
                        except:
                            disasm["FAIL"].append(ga)

                        proccessor_attempts.append(ga)
        
        if disasm["RESULT"] == "PASS":
            best = {"arch": [],
                    "functions": 0,
                    "cfg_size": 0,
                    "source": []
                    }
            for arch in disasm["PASS"]:
                disasm_features = disasm["PASS"][arch]["FEATURES"]
                disasm_source = disasm['PASS'][arch]['SOURCE']
                num_functions = disasm_features["num_functions"]
                cfg_size = disasm_features["cfg_features"]["cfg_size"]
                if num_functions > best["functions"]:
                    best.update({
                        'arch': [arch],
                        'functions': num_functions,
                        'cfg_size': cfg_size,
                        'source': [disasm_source]
                    })
                elif num_functions == best["functions"] and num_functions > 0:
                    if cfg_size > best["cfg_size"]:
                        best.update({
                            'arch': [arch],
                            'functions': num_functions,
                            'cfg_size': cfg_size,
                            'source': [disasm_source]
                        })
                    elif cfg_size == best["cfg_size"]:
                        best['arch'].append(arch)
                        best['source'].append(disasm_source)
        else:
            best = None

        results[oid]['DISASM'] = disasm
        results[oid]['SELECTED'] = best

    return results
