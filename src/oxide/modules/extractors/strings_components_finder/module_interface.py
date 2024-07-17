
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

#------------------------------------------------------------------------LOAD JSON DATA-----------------------
def load_file(file_name):
    with open("src/oxide/modules/extractors/strings_components_finder/" + file_name) as json_file:
        data = json.load(json_file)
    return data


'''def iterate_data(data, strings):
    dothis:'''


#------------------------------------------------------------------------PROCESS------------------------------
def process(oid, opts):
    cores_set = {}
    ic_set = {}
    arch_set = {}
    componets_found_dict = {}

    core_data = load_file("cpu_cores.json")
    ic_data = load_file("integrated_circuit_devices.json")
    arch_data = load_file("architectures.json")

    logger.debug("process(strings)")

    strings_retrieved = api.retrieve("strings", oid)[oid]
    strings = [value for value in strings_retrieved.values()]

    for string in strings:
        if string in ic_data:
            if not string in componets_found_dict:
                componets_found_dict[string] = "device"
        
        if string in core_data:
            if not string in componets_found_dict:
                componets_found_dict[string] = "core"
            for item in core_data.get(string):
                if not item in componets_found_dict:
                    componets_found_dict[item] = "device"
        
        if string in arch_data:
            if not string in arch_set:
                arch_set[string] = "instruction set architecure"
            for core in arch_data.get(string):
                if not core in core_data:
                    cores_set[item] = "core"
                for device in core_data.get(core):
                    if not device in ic_data:
                        ic_set[device] = "device"


                 
    
    if not components_str_set:
        logger.debug("No strings found")

    if components_str_set is None: return False
    api.store(NAME, oid, components_str_set, opts)
    return True
