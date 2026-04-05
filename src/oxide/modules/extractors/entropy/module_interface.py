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

DESC = "This module extracts entropy values from binary files."
NAME = "entropy"
USG = "The module calculates the overall entropy of a file and stores it. Returns a dictionary with the entropy value which can be used by other modules. For visualization with chunks and graphs, use the entropy_graph analyzer."

import logging
from typing import Any, Dict

from oxide.core import api
from oxide.core.libraries import histogram

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage": USG}


def process(oid: str, opts: dict):
    logger.debug("process(%s)", oid)

    data = api.get_field("files", oid, "data")
    if not data:
        logger.debug("No data for oid (%s)", oid)
        return False

    result = histogram.calc_entropy(data)
    if not result:
        logger.debug("Failed to calculate entropy for oid (%s)", oid)
        return False

    entropy_data = {"entropy": result}
    return api.store(NAME, oid, entropy_data, opts)
