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

DESC = " This module extracts features at the file, function, basic block and instruction levels and formats them into a single dictionary."
NAME = "scoped_features"

# imports
import logging
from typing import Dict, Any, List

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

# Note - This is still being figured out as modules are implemented into Oxide.
# Current structure is to split the scopes. Likely to swap to splitting everything into each function.
def documentation() -> Dict[str, Any]:
    """ Documentation for this module
        private - Whether module shows up in help
        set - Whether this module accepts collections
        atomic - TBD
    """
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True}

def extract_features(oid, object_header, functions, basic_blocks, instructions):
    #Global Features
    global_features = {
        'os': None,
        'arch': object_header.machine,
        'format': object_header.type
    }
    if global_features['format'] == 'ELF': global_features['os'] = 'linux'

    # File_Features
    file_features = {
    }

    # Temp implementation. Need to pull from inst.
    file_features['string'] = list(api.retrieve("strings", oid).get(oid).items())
    file_features['export'] = []
    file_features['import'] = []
    for value in object_header.imports.values():
        for imp in value:
            file_features['import'].append(imp)
    file_features['function-name'] = [functions[f].get('name') for f in functions]
    file_features['sections'] = object_header.section_names

    # Function Features - {Function Address: Feature,}
    function_features = {
            'loop': {},
            'recursive_call': {},
            'calls_from': {},
            'calls_to': {}
            }

    # Basic Block Features - {Block Address: Feature,}
    basic_block_features = {
            'tight_loop': {},
            'stack_string': {},
            }

    # Instruction Features - {Instruction Address: Feature,}
    instruction_features = {
            'namespace': {},
            'class': {},
            'api': api.retrieve("function_calls", oid),
            'property': {},
            'number': {},
            'string': {},
            'bytes': {},
            'offset': {},
            'mnemonic': api.retrieve("mnemonics_operands", oid, {'option': 'mnemonic'}),
            'operand': api.retrieve("mnemonics_operands", oid, {'option': 'operand'}),
            }

    formatted_features = {}
    formatted_features["global_features"] = global_features
    formatted_features["file_features"] = file_features
    formatted_features["functions"] = {}
    for function_addr, function_data in functions.items():
        formatted_features['functions'][function_addr] = {
            'function_data': function_data,
            'function_features': {key: function_features[key].get(function_addr, None) for key in function_features.keys()}
        }
        block_list = []
        for b in function_data['blocks']:
            if b in basic_blocks:
                block_list.append(b)
            elif b-4 in basic_blocks:
                block_list.append(b-4)
        formatted_features['functions'][function_addr]['blocks'] = {}
        for block_address in block_list:
            # This check shouldnt be needed but there a few issues with mapping the blocks.
            # if block_address in basic_blocks:
            formatted_features['functions'][function_addr]['blocks'][block_address] = {
                'block_data': basic_blocks[block_address],
                'block_features': {key: basic_block_features[key].get(block_address, None) for key in basic_block_features.keys()}
            }
            formatted_features['functions'][function_addr]['blocks'][block_address]['instructions'] = {}
            # '''
            # if formatted_features['functions'][function_addr]['blocks'][block_address]['block_data']['dests'] != None: #Checking to see if there is any dests
            #     for member in formatted_features['functions'][function_addr]['blocks'][block_address]['block_data']['members']: #We want to see if there is a call within the members
            #         if member[1][0:4] == "call":
            #             formatted_features['functions'][function_addr]['function_features']['calls_to'] = {} #Set the calls_to to a dict
            #             for dest in formatted_features['functions'][function_addr]['blocks'][block_address]['block_data']['dests']: #For each dest in the block add to the calls_to
            #                 formatted_features['functions'][function_addr]['function_features']['calls_to'][dest] = member[1][6:] #Will be the vaddr or some variables for the call
            #             break'''

            for instruction_address, instruction_data in formatted_features['functions'][function_addr]['blocks'][block_address]['block_data']['members']:
                formatted_features['functions'][function_addr]['blocks'][block_address]['instructions'][instruction_address] = {
                    'instruction_data': instruction_data,
                    'instruction_features': {key: instruction_features[key].get(instruction_address, None) for key in instruction_features.keys()}
                }
    return formatted_features

def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    logger.debug("process()")
    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        file_meta = api.get_field('object_header', oid, oid)
        if not file_meta:
            logger.debug("Not able to process (%s)", oid)
            results[oid] = None
        object_header= api.get_field("object_header", oid, oid)
        functions = api.get_field("ghidra_disasm", oid, "functions")
        basic_blocks = api.get_field("ghidra_disasm", oid, "original_blocks")
        instructions = api.get_field("ghidra_disasm", oid, "instructions")
        result = extract_features(oid, object_header, functions, basic_blocks, instructions)
        results[oid] = result
    return results
