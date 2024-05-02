DESC = ""
NAME = "size"
USG = ""

import logging
from oxide.core import api
import os
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage":USG}

def process(oid, opts):
    result = {}
    original_path = api.retrieve("original_path", oid)

    path = original_path[oid].pop()

    result = os.path.getsize(path)

    api.store(NAME, oid, result, opts)
    return True

