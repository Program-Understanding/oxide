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

DESC = "This module is a source module that handles the metadata when importing files."
NAME = "file_meta"

import os
import time
import hashlib
import logging
from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"file_location":{"type": str,  "mangle": False, "default": None},
                     "stat":{"type": dict, "mangle": False, "default": None}}

def documentation():
    return { "description": DESC, "opts_doc": opts_doc, "private": True,
             "set": False, "atomic": True}

def process(oid, opts):
    logger.debug("Processing file %s", oid)
    import_time = int(time.time())
    import_name = os.path.basename(opts["file_location"])  # strip dir from name
    original_path = os.path.abspath(opts["file_location"])
    file_stat   = opts["stat"]
    size        = file_stat["size"]

    data = None
    # Get the existing file info - if any
    if api.exists(NAME, oid, opts):
        data = api.retrieve(NAME, oid, opts, True)

    # If file info doesn't exist create new
    if not data:
        metadata = {import_time: {import_name: file_stat}}
        data = {"metadata": metadata, "names": set([import_name]),
                "original_paths": set([original_path]), "size": size
               }
    else:
        # If data already exists append
        if "size" not in data:
            data["size"] = size
        data["metadata"][import_time] = {import_name: file_stat}
        data["names"].add(import_name)
        if "original_paths" not in data:
            data["original_paths"] = set()
        data["original_paths"].add(original_path)

    api.store(NAME, oid, data, opts)

    # Add import time tag
    tags = {"import_time": import_time}
    api.apply_tags(oid, tags)

    return True
