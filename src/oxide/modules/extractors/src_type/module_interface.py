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

DESC = " This module attempts to determine the type of a file."
NAME = "src_type"
USG = "This analyzes a file and tells the user what type of file it is. module returns a dictionary with two key-value pairs source and \
type"

import logging
from oxide.core import api
import file_type

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> None:
    return {"description": DESC, "opts_doc": opts_doc, "set": True, "atomic": True, "usage": USG}


def process(oid: str, opts: dict = {}) -> bool:
    """ Attempt to detect possible types of file.
    """
    logger.debug("process()")
    src = api.source(oid)
    src_type = {"source":src}
    #src_type = api.get_field("src_type", oid, "type")
    logger.debug("Processing file %s", str(oid))
    if src == "collections":
        src_type["type"] = "collection"
    else:
        src_type["type"] = file_type.file_type(api.get_field(src, oid, "data"))

    api.store(NAME, oid, src_type, opts)
    return True
