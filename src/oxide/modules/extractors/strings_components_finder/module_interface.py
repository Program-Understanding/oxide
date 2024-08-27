'''

WARNING:
MUST "pip install pyahocorasick" FOR THIS MODULE TO FUNCTION PROPERLY

If testing for possible components, it is common for the terminal space fill up; all solutions may not be visible.

Possible components: "run strings_components_finder --option=possible &YOUR_COLLECTION | show"
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

opts_doc = {"option": {"type": str, "mangle": False, "default": "explicit"}}

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

    strings_retrieved = api.retrieve("strings", oid)[oid] #This api call retrieves the strings of the test file using the strings analyzer module.
    strings_list = [value.upper() for value in strings_retrieved.values()]
    strings = set(strings_list)
    if len(strings) == 0: return False


    explicitly_found_dict = {}
    possibly_found_dict = {}
    components_found_dict = {}
    processed_components = {}
    processed_architectures = set()
    processed_cores = set()
    processed_devices = set()
    
    processed_components = search_components_in_strings(strings, all_components)

    if "option" in opts:
        option = str(opts["option"])

    if option == "possible":
    #This loop checks if any of the file's strings are found in the components dataset.
        for string, occurence in processed_components.items(): 
            occurence = str(occurence)
            if string in arch_to_cores_data:
                explicitly_found_dict[string] = "instruction set architecture explicitly found " + occurence + " time/s"
                processed_architectures.add(string)
            elif string in cores_to_IC_data:
                explicitly_found_dict[string] = "core explicitly found " + occurence + " time/s"
                processed_cores.add(string)
            elif string in IC_devices_data:
                explicitly_found_dict[string] = "device explicitly found " + occurence + " time/s"
                processed_devices.add(string)

    #These loops detect the possible components of the binary file. They do this by using the explicitly found components and retrieving components related to it from the dataset.
        for IC_device in processed_devices:  
            try: architecture = IC_to_arch_data[IC_device]
            except: continue
            if architecture not in explicitly_found_dict and architecture not in possibly_found_dict:
                possibly_found_dict[architecture] = "instruction set architecture possible  ∵  " + IC_device + " device was found"

            try: core = IC_to_cores_data[IC_device]
            except: continue
            if core not in explicitly_found_dict and core not in possibly_found_dict: 
                possibly_found_dict[core] = "core possible  ∵  " + IC_device + " device was found"

        for core in processed_cores:
            try: architecture = cores_to_arch_data[core]
            except: continue
            if architecture not in explicitly_found_dict and architecture not in possibly_found_dict:
                possibly_found_dict[architecture] = "instruction set architecture possible  ∵  " + core + " core was found"

            try: IC_device_list = cores_to_IC_data[core]
            except: continue
            for IC_device in IC_device_list:
                if IC_device not in explicitly_found_dict and IC_device not in possibly_found_dict:
                    possibly_found_dict[IC_device] = "device possible  ∵  " + core + " core was found"

        for architecture in processed_architectures:
            try: core_list = arch_to_cores_data[architecture]
            except: continue
            for core in core_list:
                if core not in explicitly_found_dict and core not in possibly_found_dict:
                    possibly_found_dict[core] = "core possible  ∵  " + architecture + " instruction set architecture was found"

            try: IC_device_list = arch_to_IC_data[architecture]
            except: continue
            for IC_device in IC_device_list:
                if IC_device not in explicitly_found_dict and IC_device not in possibly_found_dict:
                    possibly_found_dict[IC_device] = "device possible  ∵  " + architecture + " instruction set architecture was found"
        components_found_dict = {**possibly_found_dict}             
    else:
        for string, occurence in processed_components.items(): 
            occurence = str(occurence)
            if string in arch_to_cores_data:
                explicitly_found_dict[string] = "instruction set architecture explicitly found " + occurence + " time/s"
                processed_architectures.add(string)
            elif string in cores_to_IC_data:
                explicitly_found_dict[string] = "core explicitly found " + occurence + " time/s"
                processed_cores.add(string)
            elif string in IC_devices_data:
                explicitly_found_dict[string] = "device explicitly found " + occurence + " time/s"
                processed_devices.add(string)
        components_found_dict = {**explicitly_found_dict} 

 

    if len(components_found_dict.keys()) == 0:
        logger.debug("No strings found")

    if components_found_dict is None: return False
    api.store(NAME, oid, components_found_dict, opts) #This api call stores our results for the cache
    return True
