""" Triage - Module_interface.py
"""
DESC = "Group file types and extensions into groupings of files."
NAME = "triage"
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
    CATEGORIES = ["source", "orchestration", "executable", "media", "archive", "documentation", "resource"]
    DESCRIPTIONS = ["Code artifacts, software", "Scripting", "Binary Executable artifacts, software",
                    "Images, Audio, Multimedia files", "Compressed file format",
                    "Informational and text-based content", "Auxillary resource files"]
    for i, category in enumerate(CATEGORIES):
        results[category] = {'total': 0, 'verbose': [], 'desc': DESCRIPTIONS[i]}

    accounted_for = 0
    a = 0
    for oid in oid_list:
        # print(a != accounted_for, '\n\n')
        res = {}
        names = api.get_field("file_meta", oid, "names")
        exts = [os.path.splitext(name)[1] for name in names]
        # print(exts)
        if 'ext' in opts and opts['ext'] not in [ex.lower() for ex in exts]:
            continue
        print("names: ", names)
        print(oid)

        src_type = api.get_field("src_type", oid, "type")
        print("types: ", src_type)

        a = accounted_for
        if 'ELF' in src_type or "PE" in src_type or "MACHO" in src_type or ('ZIP' in src_type and '.jar' in exts):
            results['executable']['total'] += 1
            accounted_for += 1
            results['executable']['verbose'].append(oid)
            continue

        if 'ZIP' in src_type or "GZIP" in src_type or "TAR" in src_type or "BZ2" in src_type:
            results['archive']['total'] += 1
            accounted_for += 1
            results['archive']['verbose'].append(oid)
            continue

        if ('PNG' in src_type or "JPG" in src_type or "GIF" in src_type or "MP3" in src_type or
           'TIFF' in src_type or "BMP" in src_type or "WAV" in src_type or
           "OGG" in src_type):
            results['media']['total'] += 1
            accounted_for += 1
            results['media']['verbose'].append(oid)
            continue

        if 'PDF' in src_type:
            results['documentation']['total'] += 1
            accounted_for += 1
            results['documentation']['verbose'].append(oid)
            continue

        if 'TTF' in src_type or 'XML' in src_type:
            results['resource']['total'] += 1
            accounted_for += 1
            results['resource']['verbose'].append(oid)
            continue

        # TEXT FILES, BASED ON FILE EXTENSION ONLY
        if (".c" in exts or ".cpp" in exts or ".cxx" in exts or ".java" in exts or ".rs" in exts or
           ".go" in exts):
            results['source']['total'] += 1
            accounted_for += 1
            results['source']['verbose'].append(oid)
            continue

    if 'verbose' not in opts:
        for category in CATEGORIES:
            del results[category]['verbose']
    results['total'] = len(oid_list)
    results['total_accounted_for'] = f"{accounted_for * 100 / len(oid_list):0.3f}%"
    return results
# b'PK\x03\x04\x14\x00\x08\x00\x08\x00\xed5' jar
