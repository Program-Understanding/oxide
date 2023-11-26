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

DESC = " This module produces a histogram of the bytes in a file."
NAME = "byte_histogram"
USG = "This module returns a histogram that shows the frequency distribution of byte values across all the binary files in the collection \
It represents this information as a dictionary with the byte value being the key and the frequency count being the key value"

import logging
from collections import defaultdict
from typing import Dict, Optional, List

from oxide.core.libraries.histogram import build_histo, merge_histo
from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> str:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage": USG}


def mapper(oid: str, opts: dict, jobid=False) -> Optional[str]:
    logger.debug("mapper()")
    src = api.source(oid)
    if api.exists(NAME, oid, opts):
        return oid

    data = api.get_field(src, oid, "data")
    if not data:
        return None

    out_histo = build_histo(data)
    api.store(NAME, oid, out_histo, opts)
    return oid


def reducer(intermediate_output: List[str], opts: dict, jobid: str) -> Dict[str, int]:
    logger.debug("reducer()")
    out_histo = defaultdict(int)

    for oid in intermediate_output:
        if oid:
            histo = api.retrieve(NAME, oid, opts)
            out_histo = merge_histo(histo, out_histo)
    api.store(NAME, jobid, out_histo, opts)

    return out_histo
