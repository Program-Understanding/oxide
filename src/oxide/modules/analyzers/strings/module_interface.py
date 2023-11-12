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

DESC = "Identify ascii-strings in file"
NAME = "strings"
USG = "This module returns a dictionary with a list of the ASCII strings found in each binary file withing the collection along with their respective \
offsets in the file keys and the extracted string as values. "

# imports
import logging
from collections import defaultdict

from typing import Dict, Any, List

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"min_len": {"type": int, "mangle": False, "default": 4},
            "encoding": {"type": str, "mangle": False, "default": 'S'}}


def documentation() -> Dict[str, Any]:
    """ Config options for file
    """
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": True,
            "atomic": True, "usage": USG}


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """ Entry point for analyzers, these do not store in database
        these are meant to be very quickly computed things passed along
        into other modules
    """
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        data = api.get_field(api.source(oid), oid, "data")
        if not data:
            results[oid] = {}
            continue

        offset = 0
        strings = defaultdict(str)
        for char in data:
            # FIXME:: encoding handling here
            if not 32 <= char <= 126:
                # maintain current offset into file
                if offset in strings:
                    # if end of word move offset to current offset
                    offset += len(strings[offset])
                offset += 1
                continue

            strings[offset] += chr(char)

        strings = dict(filter(lambda elem: len(elem[1]) > opts['min_len'], strings.items()))
        results[oid] = strings

    return results
