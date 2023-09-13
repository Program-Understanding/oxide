"""
Copyright 2023 National Technology & Engineering Solutions
of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS,
the U.S. Government retains certain rights in this software.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE. 
"""

DESC = " This module matches features to the Capa Rules dataset"
NAME = "capa_match"
#Status: Still in work

# imports
import logging
import yaml
import os
from typing import Dict, Any, List
from core import api
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}
Global_Checklist = []
def documentation() -> Dict[str, Any]:
    """ Documentation for this module
        private - Whether module shows up in help
        set - Whether this module accepts collections
        atomic - TBD
    """
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True}

def boolean_filter(current_value, matching_features, global_features, scope, **kwargs):
    key,value = list(current_value.items())[0]
    # N or more handle
    if 'or more' in key:
        n = key.split(' ')[0]
        key = 'or more'
        bool_test = function_handler[key](value, matching_features, global_features, scope, n = n)
    elif 'count' in key:
        return False
        # temp = key.strip(')').split('(')
        # key = temp[0]
        # value_to_count = temp[1::]
        # n = value
        # bool_test = function_handler[key](value_to_count, matching_features, scope, n = n)
    else:
        try:
            bool_test = function_handler[key](value, matching_features, global_features, scope)
        except Exception as e:
            if key == 'not':
                pass
            if e == KeyError:
                print("This key could not be parsed.")
            Global_Checklist.append(key)
            bool_test = False

    return bool_test

# Logic operations within the algorithm
def parse_and(current_values: list, matching_features, global_features, scope, **kwargs):
    for current_value in current_values: 
        bool_test = boolean_filter(current_value, matching_features, global_features, scope)
        if bool_test == False:
            return False
    return True

def parse_or(current_values: list, matching_features, global_features, scope, **kwargs):
    bool_list = []
    for current_value in current_values: 
        bool_test = boolean_filter(current_value, matching_features, global_features, scope)
        bool_list.append(bool_test)
        if any(bool_list):
            return True
    return False

def parse_N_or_more(current_values: list, matching_features, global_features, scope, **kwargs):
    bool_list = []
    n = int(kwargs.get('n'))
    for current_value in current_values: 
        bool_test = boolean_filter(current_value, matching_features, global_features, scope)
        bool_list.append(bool_test)
        if bool_list.count(True) >= n:
            return True
    return False

def parse_optional(current_values: list, matching_features, global_features, scope, **kwargs):
    bool_list = []
    for current_value in current_values: 
        bool_test = boolean_filter(current_value, matching_features, global_features, scope)
        bool_list.append(bool_test)
        if bool_list.count(True):
            return True
    return None

def parse_count(current_values: list, matching_features, global_features, scope, **kwargs):
    bool_list = []
    n = str(kwargs.get('n'))
    if 'or more' in n:
        n = int(n.split(' ')[0])
        if getattr(matching_features, current_values[0]).count(current_values[1]) >= n:
            return True
    else:
        n = int(n)
        if getattr(matching_features, current_values[0]).count(current_values[1]) >= n:
            return True       
    return False
# Parses anything that would not need to be recursed. Most likely literals. A lot of these could
# be condensed into one function. I have left them seperate for testing and debugging.
def parse_string(value: str, matching_features: list, global_features, scope, *args):
    # strings = matching_features.string
    # for element in strings:
    #     if value == element:
    #         return True
    return False

def parse_substring(value: str, matching_features: list, global_features, scope, *args):
    # for element in matching_features.string:
    #     if value in element:
    #         return True
    return False

def parse_api(value: str, scoped_features, global_features, scope, *args):
    if scope == 'function':
        for block_addr in scoped_features['blocks']:
            for instruction_addr in scoped_features['blocks'][block_addr]['instructions']:
               if scoped_features['blocks'][block_addr]['instructions'][instruction_addr]['instruction_features']['api'] == None:
                continue
               elif value == scoped_features['blocks'][block_addr]['instructions'][instruction_addr]['instruction_features']['api']['func_name']: 
                   return True
               
    elif scope == 'basic block':
        matching_features = scoped_features['instructions']
        for instruction in matching_features:
            if value == matching_features[instruction]['instruction_features']['api']:
                return True
    return False

def parse_os(value: str, matching_features: list, global_features, scope, *args):
    if value == global_features['os']:
        return True
    return False

def parse_number(value: str | int | float, matching_features: list, global_features, scope, *args) -> bool:
    # if value is str:
    #     value = value.split(" ")[0]
    #     if '0x' in value:
    #         value = int(value, 16)
    # for element in matching_features.number:
    #     if value == element:
    #         return True
    return False

def parse_characteristic(value: str, matching_features: list, global_features, scope, *args):
    for element in matching_features.characteristic:
        if value == element:
            return True
    return False

def parse_mnemonic(value: str, matching_features: list, global_features, scope, *args):
    for element in matching_features.mnemonic:
        if value == element:
            return True
    return False

def parse_property_write(value: str, matching_features: list, global_features, scope, *args):
    for element in matching_features.property_write:
        if value == element:
            return True
    return False

def parse_property_read(value: str, matching_features: list, global_features, scope, *args):
    for element in matching_features.property_read:
        if value == element:
            return True
    return False

def parse_section(value: str, matching_features: list, global_features, scope, *args):
    for element in matching_features.section:
        if value == element:
            return True
    return False


# Handles functions so that new keys could be added quickly.
function_handler = {
    # Logic Functions
    'and': parse_and, 
    'or': parse_or,
    'or more': parse_N_or_more,
    'optional': parse_optional,
    'count': parse_count,

    # Non List Functions 
    'string': parse_string,
    'substring': parse_substring,
    'api': parse_api,
    'os': parse_os,
    'number': parse_number,
    'characteristic': parse_characteristic,
    'mnemonic': parse_mnemonic,
    'property/write': parse_property_write,
    'property/read': parse_property_read,
    'section': parse_section
}

# Parses the initial rule to start the recursion chain.
def parse_rule(rule_features, scoped_features, global_features, scope):

    for initial_items in rule_features:
        for key, value in initial_items.items():
            try:
                output = function_handler[key](value, scoped_features, global_features, scope)
            except Exception as e:
                if e == KeyError:
                    print("This key could not be parsed.")
                Global_Checklist.append(key)
                print(e)
                return False
            if output == True: 
                return True
    return False

# Loads the individual rule.
def rules_engine(scoped_features, rule_path):
    
    with open(rule_path, "r") as stream:
        try:
            loaded_rule = yaml.safe_load(stream)
            
        except yaml.YAMLError as exc:
            print(exc)
        
    # pprint.pprint(loaded_rule['rule']['features'])
    global_features = scoped_features['global_features']
    scope = loaded_rule['rule']['meta']['scope']
    output = []
    if scope == 'file':
        pass
        # output += parse_rule(loaded_rule['rule']['features'], scoped_features, scope)
    elif scope == 'function':
        for function_address, function_data in scoped_features['functions'].items():
            if function_data['function_data']['name'] == 'main':
                pass
            if 'blocks' in function_data:
                output += (function_address, parse_rule(loaded_rule['rule']['features'], function_data, global_features, scope))
    elif scope == 'basic block':
        pass
        # for function in scoped_features['functions']:
        #     if 'blocks' in scoped_features['functions'][function]:
        #         for basic_block_address, basic_block_data in scoped_features['functions'][function]['blocks'].items():
        #             # print(basic_block_address)
        #             output += (basic_block_address, parse_rule(loaded_rule['rule']['features'], basic_block_data, scope))
    if output == True:
        print('\n')
        print('found output')
        # file_name = matching_features.name
        # oid = matching_features.oid
        # offset = matching_features.offset
        # name = loaded_rule['rule']['meta']['name']
        # if 'att&ck' in loaded_rule['rule']['meta']:
        #     vector = loaded_rule['rule']['meta']['att&ck'][0].replace("::", "\n\t- ")
        # elif 'mbc' in loaded_rule['rule']['meta']:
        #     vector = loaded_rule['rule']['meta']['mbc'][0].replace("::", "\n\t- ")
        # else:
        #     vector = 'No descriptor'
        # print("File Name: {}\nOID: {}\nStarting Offset: {}\nRule Name: {}\nAttack Vector: {}\n".format(file_name, oid,offset, name, vector))

def match_capa_rules(oid):
    scoped_features = api.retrieve('scoped_features', oid, oid)[oid]
    rule_directory = 'datasets/capa_rules'
    matched_rules = []
    rules_list = [os.path.join(dirpath,f) for (dirpath, dirnames, filenames) in os.walk(rule_directory) for f in filenames]
    for rule in rules_list:
        if rule == 'datasets/capa_rules/collection/get-current-user-on-linux.yml':
            pass
        if rule.endswith('.yml'):   
            matched_rules.append(rules_engine(scoped_features, rule))
    return matched_rules

def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    logger.debug("process()")
    for oid in oid_list:
        match_capa_rules(oid)

    return results
