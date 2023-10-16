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

DESC = "Extracts chains of same byte extending beyond nine sequence"
NAME = "padding"
USG = " This module is used to analyze data sequences and extract chains of the same byte that extend beyond a specified number of \
consecutive occurences. Users can run the module with a list of OID's to perform analysis on them. The module returns a dictionary \
containing information about the extracted padding for each OID which include the starting byte index, the byte value and the count of \
consecutive occurences."

import logging
import ctypes

from typing import Optional, List, Dict, Any

logger = logging.getLogger(NAME)
logger.debug("init")

import api
import otypes

opts_doc = {"value": {"type": int, "mangle": False, "default": -1},
            "number": {"type": int, "mangle": False, "default": 9}}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "Usage": USG}


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    logger.debug("results()")

    results = {}
    for oid in oid_list:

        padding = {}
        src = api.source(oid)
        data = api.get_field(src, oid, "data", {})
        if not data:
            logger.debug("Not able to process %s", oid)
            continue

        count = 0
        prev_byte = None
        for byte_idx in range(len(data)):
            # current byte matches previous, and byte matches param or dont care
            if ((data[byte_idx] == prev_byte) and ((opts['value'] == -1) or (prev_byte == opts['value']))):
                count += 1
            else:
                if count >= opts["number"]:
                    padding[byte_idx - count] = {'value': prev_byte, 'value(byte)': hex(prev_byte), 'count': count}
                count = 0

            prev_byte = data[byte_idx]

        results[oid] = padding

    return results
