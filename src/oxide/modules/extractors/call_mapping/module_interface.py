DESC = " This module maps calls_to and calls_from for each function"
NAME = "call_mapping"
CATEGORY = ""  # used for filtering of modules e.g. disassemblers like ida

import logging

from typing import Dict, Any

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"version": {"type": int, "mangle": True, "default": -1}}

def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY}

#This will iterate over a list of functions and find all calls_to. It will then add that to a dictionary and iterate back through the calls_to and assign them correctly to the correct calls_to
def call_mapping(functions, basic_blocks):

    call_mapping = {}
    function_addresses = functions.keys()
    #Generating calls_to
    for function_addr, function_data in functions.items():
        call_mapping[function_addr] = {'calls_to': {}, 'calls_from': {}}
        for block_addr in function_data['blocks']:
            for instruction_offset, instruction in basic_blocks[block_addr]['members']:
                if instruction[:4] == 'call':
                    for offset in basic_blocks[block_addr]['dests']:
                        if offset in function_addresses:
                            called_file_offset = offset
                            call_mapping[function_addr]['calls_to'][called_file_offset] = functions[called_file_offset]['name']

    #using the calls_to to map out a calls_from
    for calling_function_addr, calls in call_mapping.items():
        for called_file_offset, called_function_address in calls['calls_to'].items():
            for function_addr, function_data in functions.items():
                if function_addr == called_file_offset:
                    call_mapping[function_addr]['calls_from'][calling_function_addr] = functions[calling_function_addr]['name']

    return call_mapping

def process(oid: str, opts: dict) -> bool:
    logger.debug("process()")

    functions = api.get_field("ghidra_disasm", oid, "functions")
    basic_blocks = api.get_field("ghidra_disasm", oid, "original_blocks")

    if functions != None or basic_blocks != None:
        result = call_mapping(functions, basic_blocks)

        api.store(NAME, oid, result, opts)
        return result