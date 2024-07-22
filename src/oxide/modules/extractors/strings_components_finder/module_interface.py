
DESC = "Strings Components Finder"
NAME = "strings_components_finder"
USG = "This module is a extractor module that finds common device components in strings."
AUTHOR = "Tullis Nelson, Grayson Sparks"

import logging
from oxide.core import api
import json
from pathlib import Path




logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage": USG}

#------------------------------------------------------------------------LOAD JSON DATA-----------------------
def load_file(file_name):
    path = Path(__file__).parent / file_name
    with open(path) as json_file:
        data = json.load(json_file)
    return data


#------------------------------------------------------------------------PROCESS------------------------------
def process(oid, opts):
    
    cores_to_IC_data = load_file("cores_to_IC.json")
    IC_devices_data = load_file("IC_devices.json")
    arch_to_cores_data = load_file("arch_to_cores.json")
    IC_to_arch_data = load_file("IC_to_arch.json")
    cores_to_arch_data = load_file("cores_to_arch.json")

    logger.debug("process(strings)")

    strings_retrieved = api.retrieve("strings", oid)[oid]
    strings_list = [value for value in strings_retrieved.values()]
    
    components_found_dict = {}
    strings = set(strings_list)
    
    processed_architectures = set()
    processed_cores = set()
    processed_devices = set()


    for string_orig in strings:
        string = string_orig.upper()
        if string in arch_to_cores_data:
            components_found_dict[string] = "instruction set architecture, explicitly found "
            processed_architectures.update(string)
            processed_cores.update(arch_to_cores_data[string])
        elif string in cores_to_IC_data:
            components_found_dict[string] = "core, explicitly found"
            processed_devices.update(cores_to_IC_data[string])
        elif string in IC_devices_data:
            components_found_dict[string] = "device, explicitly found"

    for core in processed_cores:
        if core in cores_to_IC_data and core not in components_found_dict:
            components_found_dict[core] = "core, possibility"
            processed_devices.update(cores_to_IC_data[core])
        if core in cores_to_arch_data and cores_to_arch_data[core] not in processed_architectures:
            components_found_dict[cores_to_arch_data[core]] = "instruction set architecture, possibility"

    for device in processed_devices:
        if device in IC_devices_data and device not in components_found_dict:
            components_found_dict[device] = "device, possibility"
        if device in IC_to_arch_data and IC_to_arch_data[device] not in processed_architectures:
            components_found_dict[IC_to_arch_data[device]] = "instruction set architecture, possibility"
    
    if len(components_found_dict.keys()) == 0:
        logger.debug("No strings found")
        components_found_dict["Complete"] = "No Components Found"


    if components_found_dict is None: return False
    api.store(NAME, oid, components_found_dict, opts)
    return True
