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

DESC = "Extracts function calls from instructions."
NAME = "function_calls"
CATEGORY = ""  # used for filtering of modules e.g. disassemblers like ida

import logging

from typing import Dict, Any

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY}

def process(oid: str, opts: dict) -> bool:
    logger.debug("process()")
    result = {}
    instructions = api.get_field("ghidra_disasm", oid, "instructions")
    functions = api.get_field("ghidra_disasm", oid, "functions")
    basic_blocks = api.get_field("ghidra_disasm", oid, "original_blocks")

    for insn_address, insn_data in instructions.items():
        if ' ' not in insn_data:
            mnemonic = insn_data
            operands = []
        else: (mnemonic, operands) = insn_data.split(maxsplit=1)
        if (mnemonic == 'CALL' or mnemonic == 'call') and "0x" in operands:
            v_address = operands[2:]
            for function in functions:
                if v_address == functions[function].get('vaddr'):
                    result[insn_address] = {
                        "func_addr": function,
                        "func_name": functions[function].get('name')
                    }

    if result is None: return False
    api.store(NAME, oid, result, opts)
    return True
