DESC = ""
NAME = "linux_detection_firmline"
USG = ""

import logging
from oxide.core import api
import os
import re
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage":USG}

def process(oid, opts):
    result = {}
    string_references = api.retrieve("strings", oid)[oid]

    strings = [value for value in string_references.values()]

    terms = ['uimage', 'u-boot', 'squashfs', 'linux']

    for term in terms:
        if any(term.lower() in bwt.lower() for bwt in strings):
            result = "Linux"

    if any('filesystem' in t.lower()
           and not re.match('^.*, from [^,]* filesystem', t)
           for t in strings):
        result = "Linux"

    else:
        result = "Non-Linux"

    api.store(NAME, oid, result, opts)
    return True

