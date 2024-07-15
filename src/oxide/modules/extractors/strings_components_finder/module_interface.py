
DESC = "Strings Components Finder"
NAME = "strings_components_finder"
USG = "This module is a extractor module that finds common device components in strings."
AUTHOR = "Tullis Nelson, Grayson Sparks"

import logging

from oxide.core import api

import json


logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage": USG}

with open("src/oxide/modules/extractors/strings_components_finder/components.json") as json_file:
        data = json.load(json_file)

def process(oid, opts):

    logger.debug("process(strings)")
    results_strings = {}
    strings_retrieved = api.retrieve("strings", oid)[oid]

    strings = [value for value in strings_retrieved.values()]

    for string in strings:
        if string in data:
            data.get(string)
            results_strings[string] = "True"
                 
    
    if not results_strings:
        logger.debug("No strings found")

    if results_strings is None: return False
    api.store(NAME, oid, results_strings, opts)
    return True
