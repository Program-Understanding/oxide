import sys
import os
from oxide.core import api 
import logging 
import xmltodict
import pprint

NAME = "VALID_GHIDRA_ARCHITECTURES"
DESC = "Returns the valid architectures supported\
        by the linked version of Ghidra" 
USG = "This plugin does not take any arguments"

logger = logging.getLogger(NAME)
logger.debug("init")

def ghidra_archs(args, opts:dict) -> dict:
    print(sys.path)
    if len(args) != 0: 
        raise ShellSyntaxError("No arguments are needed")
    result = {}
    path = api.ghidra_path

    if not path:
        logger.warning('No ghidra path was set or configured to None')
        return False
    
    processor_definitions = []
    processor_path = os.path.join(path, "Ghidra", "Processors")
    for root, dirs, files in os.walk(processor_path):
        for file in files:
            if file.endswith(".ldefs"):
                with open(os.path.join(root, file), "r") as f:
                    data = xmltodict.parse(f.read())
                processor_definitions.append((file.split(".")[0], data))
    
    for processor, lang_defs in processor_definitions:
        lang_result = {}
        langs = lang_defs["language_definitions"]["language"]
        if not isinstance(langs, list):
            langs = [langs]
        for lang in langs:
            lang_result[lang["@id"]] = {
                "endian": lang["@endian"],
                "size": lang["@size"],
                "variant": lang["@variant"],
                "version": lang["@version"],
                "desc": lang["description"]
            }
        result[processor] = lang_result
     
    pprint.pprint(result)

exports = [ghidra_archs]