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

DESC = "This module is a module that handles the metadata when importing collections."
NAME = "collections_meta"

import time
import logging
from typing import Dict, Any

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"notes": {"type": str,  "mangle": False, "default": ""},
            "num_oids": {"type": int, "mangle": False, "default": None},
            "name": {"type": str, "mangle": False, "default": None}}


def documentation() -> Dict[str, Any]:
    return { "description": DESC, "opts_doc": opts_doc, "private": True,
             "set": True, "atomic": False}


def process(oid: str, opts: dict) -> bool:
    logger.debug("Processing collection %s", oid)
    data = {"notes": opts["notes"], "num_oids": opts["num_oids"], "name": opts["name"]}
    api.store(NAME, oid, data, opts)

    # Add creation time tag
    tags = {"creation_time": int(time.time())}
    api.apply_tags(oid, tags)

    return True
