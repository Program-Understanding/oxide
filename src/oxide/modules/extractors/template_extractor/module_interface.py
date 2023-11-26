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
NAME = "template_extractor"
CATEGORY = ""  # used for filtering of modules e.g. disassemblers like ida

import logging

from typing import Dict, Any

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}
"""
options dictionary defines expected options, including type, default value, and whether
presence of option distinguishes a version of output (mangle).

An example of option
{"version": {"type": int, "mangle": True, "default": -1}
where 'version' is guarenteed to be passed into opts of process
    it has type int, with default value -1, and caching of results only relevant to this value
        template_extract --version=1 vs template_extract --version=2
    would result in running two different times
"""


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": True, "set": False,
            "atomic": True, "category": CATEGORY}


def process(oid: str, opts: dict) -> bool:
    """ Extractors run analysis, do not interact with stdout, and only store to database
        they take in a single oid (as opposed to analyzers which take oid_list)
        and opts is ensured to atleast contain values defined by opts_doc defined above.
    """
    logger.debug("process()")

    """
    src = api.source(oid)
    # if extractor needs file bytes
    data = api.get_field(src, oid, "data", {})
    if not data:
        logger.debug("Not able to process %s", oid)
        return False

    # if extractor needs to inspect executable files header
    header = api.get_field("object_header", oid, oid)
    if not header:
        logger.warning('No header found for %s in %s', oid, NAME)
        return False

    # if extractor needs a file on disk to analyze
    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data)
    """

    result = "Python code goes here"
    if result is None: return False
    api.store(NAME, oid, result, opts)
    return True
