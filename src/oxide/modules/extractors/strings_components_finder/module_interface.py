'''

WARNING:
MUST "pip install pyahocorasick" FOR THIS MODULE TO FUNCTION PROPERLY

If testing for possible components, it is common for the terminal space fill up; all solutions may not be visible.

Must run this module with a component option. 
"--component=architecture" , "--component=core" , "--component=device" 
Possible components: "run strings_components_finder --mode=possible &YOUR_COLLECTION | show"
Explicit components only: "run strings_components_finder &YOUR_COLLECTION | show"

'''

DESC = "Strings Components Finder"
NAME = "strings_components_finder"
USG = "This module is a extractor module that finds common device components in strings."
AUTHOR = "Tullis Nelson, Grayson Sparks"

import logging
import ahocorasick
from oxide.core import api
import json
from pathlib import Path



logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"mode": {"type": str, "mangle": True, "default": "explicit"},
            "component": {"type": str, "mangle": True, "default": "none" }
            }

def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage": USG}

#------------------------------------------------------------------------LOAD JSON DATA-----------------------
def load_file(file_name):
    folder_name = "json_data"
    path = Path(__file__).parent / folder_name / file_name
    with open(path) as json_file:
        data = json.load(json_file)
    return data


#------------------------------------------------------------------------AHOCORASICK ALGO---------------------


def build_automaton(strings): #This function makes a trie from the strings found in a binary file and calculates failure and output links.
    component_automaton = ahocorasick.Automaton()
    for index, string in enumerate(strings):
        component_automaton.add_word(string, (index, string))
    return component_automaton



def search_components_in_strings(strings, components):
    component_automaton = build_automaton(components)
    component_automaton.make_automaton() #This constructs the internal state machine used for efficient pattern matching.
    results = {}

    for string in strings:#This searches the automaton using the ahorasick algorithm over the tree-like structure.
        for end_index, (insert_order, component) in component_automaton.iter(string):
            results[component] = results.setdefault(component, 0) + 1
    return results


#------------------------------------------------------------------------PROCESS------------------------------
def process(oid, opts):
    all_components = load_file("all_components.json")
    cores_to_IC_data = load_file("cores_to_IC.json")
    IC_devices_data = load_file("IC_devices.json")
    arch_to_cores_data = load_file("arch_to_cores.json")
    IC_to_arch_data = load_file("IC_to_arch.json")
    cores_to_arch_data = load_file("cores_to_arch.json")
    IC_to_cores_data = load_file("IC_to_cores.json")
    arch_to_IC_data = load_file("arch_to_IC.json")


    logger.debug("process(strings)")

    strings_retrieved = api.retrieve("strings", oid)[oid]
    strings_list = [value.upper() for value in strings_retrieved.values()]
    strings = set(strings_list)
    if len(strings) == 0: return False


    explicitly_found_dict = {}
    components_found_dict = {}
    components_found_dict = {}
    components_found_dict = {}
    processed_components = {}
    processed_archs = {}
    processed_cores = {}
    processed_devices = {}
    
    processed_components = search_components_in_strings(strings, all_components)
    
    explicitly_found_dict["archs"] = {}
    explicitly_found_dict["cores"] = {}
    explicitly_found_dict["devices"] = {}

    if "mode" in opts:
        mode = str(opts["mode"])
    
    if "component" in opts:
        component = str(opts["component"])
    
    if mode == "explicit":
        for string, occurrence in processed_components.items():
            if string in arch_to_cores_data and component == "architecture":
                components_found_dict[string] = occurrence

            if string in cores_to_IC_data and component == "core":
                components_found_dict[string] = occurrence

            if string in IC_devices_data and component == "device":
                components_found_dict[string] = occurrence


    elif mode == "possible":
        for string, occurrence in processed_components.items():
            occurrence = 0
            if string in arch_to_cores_data:
                processed_archs[string] = ""

            if string in cores_to_IC_data:
                processed_cores[string] = ""

            if string in IC_devices_data:
                processed_devices[string] = ""

        if component == "architecture":
            for core in processed_cores:
                if core in cores_to_arch_data:
                    components_found_dict[cores_to_arch_data[core]] = ""
            for device in processed_devices:
                if device in IC_to_arch_data:
                    components_found_dict[IC_to_arch_data[device]] = ""

        elif component == "device":
            for arch in processed_archs:
                if arch in arch_to_IC_data:
                    for value in arch_to_IC_data[arch]:
                        components_found_dict[value] = ""
            for core in processed_cores:
                if core in cores_to_IC_data:
                    for value in cores_to_IC_data[core]:
                        components_found_dict[value] = ""

        elif component == "core":
            for arch in processed_archs:
                if arch in arch_to_cores_data:
                    for value in arch_to_cores_data[arch]:
                        if value != "":
                            components_found_dict[value] = ""
            for device in processed_devices:
                if device in IC_to_cores_data:
                    for value in IC_to_cores_data[device]:
                        components_found_dict[value] = ""
        


    if len(components_found_dict.keys()) == 0:
        logger.debug("No strings found")

    if components_found_dict is None: return False
    api.store(NAME, oid, components_found_dict, opts)
    return True
