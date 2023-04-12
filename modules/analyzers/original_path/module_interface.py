DESC = "Returns the original path of imported binary"
NAME = "original_path"

import logging

from typing import Dict, Any, List

from core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True}


def results(oid_list: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    logger.debug("results()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        paths = api.get_field("file_meta", oid, "original_paths")
        results[oid] = paths

    return results
