DESC = "This module is a source module that handles importing source code."
NAME = "sourcecode"
META = "file_meta"

import logging

from typing import Dict, Any

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"file_contents":{"type": bytes,  "mangle": False, "default": b""}}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": True,
            "set": False, "atomic": True, "meta": META}


def process(oid: str, opts: dict) -> bool:
    if len(opts['file_contents']) == 0:
        return True
    logger.debug("Processing file %s", oid)
    data = {"data": opts["file_contents"]}
    api.store(NAME, oid, data, opts)
    return True
