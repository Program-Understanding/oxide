
DESC = "Strings Comparer"
NAME = "strings_comparer"
USG = "This module compares a dictionary of common components to strings"
AUTHOR = "Tullis Nelson"

import logging
import glob
import shutil
import os
from oxide.core import api
import re
from components import components as pro



logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage": USG}


def process(oid, opts):

    logger.debug("process(strings)")
    results_strings = {}
    strings_retrieved = api.retrieve("strings", oid)[oid]

    strings = [value for value in strings_retrieved.values()]

    for term in pro:
        if any(term.lower() in bwt.lower() for bwt in strings):
            results_strings[term] = "True"
            
    
    if not results_strings:
        logger.debug("No strings found")

    if results_strings is None: return False
    api.store(NAME, oid, results_strings, opts)
    return True
