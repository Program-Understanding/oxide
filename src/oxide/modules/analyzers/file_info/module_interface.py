DESC = "Generate information about a given file."
NAME = "file_info"
USG = ""

import os
import hashlib
import operator
import logging

from typing import Dict, Any, List

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "Usage": USG}


def results(oid_list: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    logger.debug("results()")

    oid_list = api.expand_oids(oid_list)
    results = {}

    for oid in oid_list:
        result = {
            "CATEGORY": None,
            "SRC_TYPE": None,
            "SIZE": None,
            "NAMES": None
        }
        names = api.get_field("file_meta", oid, "names")
        exts = [os.path.splitext(name)[1] for name in names]

        src_type = api.get_field("src_type", oid, "type")
        
        size = api.get_field("file_meta", oid, 'size')

        category = None

        if 'ELF' in src_type or "PE" in src_type or "MACHO" in src_type or ('ZIP' in src_type and '.jar' in exts):
            category = 'executable'

        elif 'ZIP' in src_type or "GZIP" in src_type or "TAR" in src_type or "BZ2" in src_type:
            category = 'archive'

        elif ('PNG' in src_type or "JPG" in src_type or "GIF" in src_type or "MP3" in src_type or
           'TIFF' in src_type or "BMP" in src_type or "WAV" in src_type or
           "OGG" in src_type):
            category = 'media'

        elif 'PDF' in src_type:
            category = 'documentation'

        elif 'TTF' in src_type or 'XML' in src_type:
            category = 'resource'

        # TEXT FILES, BASED ON FILE EXTENSION ONLY
        elif (".c" in exts or ".cpp" in exts or ".cxx" in exts or ".java" in exts or ".rs" in exts or
           ".go" in exts):
            category = 'source'

        result["CATEGORY"] = category
        result["SRC_TYPE"] = src_type
        result['NAMES'] = names
        result['SIZE'] = size

        results[oid] = result
    return results
