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

from oxide.core import api

from typing import Dict, Any, List, Union


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
        for instruction_addr in scoped_features['instructions']:
            if scoped_features['instructions'][instruction_addr]['instruction_features']['api'] == None:
                continue
            elif value == scoped_features['instructions'][instruction_addr]['instruction_features']['api']['func_name']:
                return True
    return False


def parse_os(value: str, matching_features: list, global_features, scope, *args):
    if value == global_features['os']:
        return True
    return False

def parse_number(value: Union[str, int, float], matching_features: list, global_features, scope, *args) -> bool:
    # if value is str:
    #     value = value.split(" ")[0]
    #     if '0x' in value:
    #         value = int(value, 16)
    # for element in matching_features.number:
    #     if value == element:
    #         return True
    return False

def parse_characteristic(value: str, matching_features: list, global_features, scope, *args):
    # for element in matching_features.characteristic:
    #     if value == element:
    #         return True
    return False

def parse_mnemonic(value: str, matching_features: list, global_features, scope, *args):
    # for element in matching_features.mnemonic:
    #     if value == element:
    #         return True
    return False

def parse_property_write(value: str, matching_features: list, global_features, scope, *args):
    # for element in matching_features.property_write:
    #     if value == element:
    #         return True
    return False

def parse_property_read(value: str, matching_features: list, global_features, scope, *args):
    # for element in matching_features.property_read:
    #     if value == element:
    #         return True
    return False

def parse_section(value: str, matching_features: list, global_features, scope, *args):
    # for element in matching_features.section:
    #     if value == element:
    #         return True
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
            output_bool = False
            if function_data['function_data']['name'] == 'main':
                pass
            if 'blocks' in function_data:
                output_bool = parse_rule(loaded_rule['rule']['features'], function_data, global_features, scope)
                if output_bool:
                    output += [
                        loaded_rule['rule']['meta'],
                        function_address,
                        function_data['function_data']['name'],
                        scope,
                        global_features
                    ]
    elif scope == 'basic block':
        for function_address, function_data in scoped_features['functions'].items():
            output_bool = False
            if 'blocks' in function_data:
                for block_address, block_data in function_data['blocks'].items():
                    output_bool = parse_rule(loaded_rule['rule']['features'], block_data, global_features, scope)
                    if output_bool:
                        output += [
                            loaded_rule['rule']['meta'],
                            function_address,
                            function_data['function_data']['name'],
                            scope,
                            global_features
                        ]
    return output

def match_capa_rules(oid):
    scoped_features = api.retrieve('scoped_features', oid, oid)[oid]
    rule_directory = 'datasets/capa_rules'
    matched_rules = []
    rules_list = [os.path.join(dirpath,f) for (dirpath, dirnames, filenames) in os.walk(rule_directory) for f in filenames]
    for rule in rules_list:
        if rule.endswith('.yml'):
            matched_rule = rules_engine(scoped_features, rule)
            if matched_rule:
                matched_rules.append(matched_rule)
    return matched_rules

def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    logger.debug("process()")
    matched_rules = []
    for oid in oid_list:
        matched_rules += match_capa_rules(oid)
    results = {}
    for rule in matched_rules:
        if 'att&ck' in rule[0]:
            results[rule[0]['name']] = {
                # 'namespace': rule[0]['namespace'],
                'attack_tactic': rule[0]['att&ck'][0].split("::")[0],
                'attack_technique': rule[0]['att&ck'][0].split("::")[1],
                'scope': rule[3],
                "address_found": rule[1],
                "function_found": rule[2],
                "os": rule[4]["os"],
                'arch': rule[4]['arch'],
                'format': rule[4]['format']
            }
        else:
            results[rule[0]['name']] = {
                # 'namespace': rule[0]['namespace'],
                'attack_tactic': "Unknown",
                'attack_technique': "Unknown",
                'scope': rule[3],
                "address_found": rule[1],
                "function_found": rule[2],
                "os": rule[4]["os"],
                'arch': rule[4]['arch'],
                'format': rule[4]['format']
            }
    return results
