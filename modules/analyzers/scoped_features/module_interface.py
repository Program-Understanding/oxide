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

from core import api

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
    
    # File_Features
    # Need modules: export
    file_features = {}

    # Temp implementation. Need to pull from inst.
    file_features['string'] = list(api.retrieve("strings", oid).get(oid).items())
    file_features['export'] = []
    file_features['import'] = []
    for value in object_header.imports.values():
        for imp in value:
            file_features['import'].append(imp)
    file_features['function-name'] = [functions[f].get('name') for f in functions]
    file_features['sections'] = object_header.section_names

    # Function Features - This is currently boilerplate, subject to change.
    # Need modules: loop, recursive_call, calls_from, calls_to
    function_features = {}
    for function_offset, function_data in functions.items():
        function_features[function_offset] = {
            'loop': None,
            'recursive_call': None,
            'calls_from':  None,
            'calls_to': None
            }


    # Basic Block Features - Most likely will pull addresses from functions.
    basic_block_features = {}
    for bb_offset, bb_data in basic_blocks.items():
        basic_block_features[bb_offset] = {
            'tight_loop': None,
            'stack_string': None,
            }
        

    # Instruction Feature - Most likely will pull this information from the blocks.
    instruction_features = {}
    for inst_offset, inst_data in instructions.items():
        instruction_features[inst_offset] = {
            'namespace': None,
            'class': None,
            'api': None,
            'property': None,
            'number': None,
            'string': None,
            'bytes': None,
            'offset': None,
            'mnemonic': None,
            'operand': None,
            }
        
    extracted_features = {
        'file_features': file_features, 
        'function_features': function_features, 
        'basic_block_features': basic_block_features, 
        'instruction_features': instruction_features}
    return extracted_features

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
