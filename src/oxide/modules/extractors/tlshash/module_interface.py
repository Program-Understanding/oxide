DESC = " TLSH of a file"
NAME = "tlshash"

import logging
import tlsh
import api
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True}

def process(oid, opts):
    f_dict = {}
    names = api.get_field("file_meta", oid, "names")
    logger.debug("process(%s)", names)
    data = api.get_field("files", oid, "data")

    hash = {"hash":tlsh.hash(data)}
    logger.debug("Storing")
    api.store(NAME, oid, hash, opts)
    return True
