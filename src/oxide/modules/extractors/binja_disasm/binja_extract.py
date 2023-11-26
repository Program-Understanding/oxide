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

import time
import logging
import binaryninja as bn  # If this fails, module will not load, requires enterprise or api licnse

from typing import Dict

# ------------------------------- Tool N+M: Binary Ninja -------------------------------------

NAME = "binja_disasm"
logger = logging.getLogger(NAME)


def _get_offset(bv, addr: int):
    return bv.get_data_offset_for_address(addr)


def _binja_analyze(fname: str) -> Dict:
    output = {'functions': {}, 'blocks': {}, 'insns': {}}
    with bn.open_view(fname) as bv:
        logger.debug(f"Opening {bv.file.filename} which has {len(list(bv.functions))} functions")
        # For each function
        for function in bv.functions:
            output['functions'][function.start] = {'name': function.name, 'clobbered_regs': str(function.clobbered_regs), 'returns': str(function.can_return), 'convention': str(function.calling_convention), 'calls': function.callee_addresses, 'num_args': len(function.parameter_vars), 'return_regs': str(function.return_regs), 'signature': str(function.function_type)}

            # 'return_vals': function.get_reg_value_at_exit(function.return_regs)}
            # For each basic block
            for bb in function.basic_blocks:
                # Record Block
                members = []
                logger.debug("BB:{}, out:{}, returns: {}".format(bb.start, [block.target.start for block in bb.outgoing_edges], not bb.can_exit))
                for inst in bb.disassembly_text:
                    logger.debug("INSTRUCTION: {} text:{}".format(inst.address, str(inst)))
                    output['insns'][_get_offset(bv, inst.address)] = str(inst)
                    members.append((_get_offset(bv, inst.address), str(inst)))
                output['blocks'][_get_offset(bv, bb.start)] = {'members': members, 'dests': [block.target.start for block in bb.outgoing_edges]}
    return output


def extract(file_test, header):
    """processes an exectuable with binary ninja headless api, and disassembles code
        input -
                file_test (filename)- exectuable x86,64 parsable with binary ninja
    """
    start = time.time()

    # cfg is json output of control flow graph
    output_map = {}
    output_map["meta"] = {}
    output_map["instructions"] = {}
    output_map["original_blocks"] = {}
    output_map["canon_blocks"] = {}
    output_map["functions"] = {}

    output = _binja_analyze(file_test)

    if output is None:
        logging.info("BinaryNinja produced no output.")
        return None

    # Marshall output into output_map
    if 'insns' in output:
        output_map['instructions'] = output['insns']
    if 'blocks' in output:
        output_map['original_blocks'] = output['blocks']
    if 'functions' in output:
        output_map['functions'] = output['functions']

    end = time.time()
    output_map["meta"]["time"] = end - start

    # Offsets Obtained
    return output_map
