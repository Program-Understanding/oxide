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

try:
    import r2pipe
except OSError:
    raise Exception("r2pipe no shared library")

# ------------------------------- Tool 2: Radare -------------------------------------

NAME = "radare_disasm"
logger = logging.getLogger(NAME)


def _get_function_offset(fun: dict):
    # radare function JSON changed across versions (offset -> addr)
    # Use the legacy key first, then fall back to newer address keys
    for key in ("offset", "addr", "vaddr"):
        if key in fun and fun[key] is not None:
            return fun[key]
    return None


def _canonize_blocks(output_map: dict) -> None:
    block_offsets = list(output_map["original_blocks"].keys())

    # Instruction offsets, removing meta tag
    instructions = list(output_map["instructions"].keys())
    instructions.remove("meta")
    sorted_instructions = sorted(instructions)

    rep_call_blocks = []

    # Find call/rep and create new basic block on next instruction
    for block_key in block_offsets:
        if block_key == "meta":
            continue

        mems = output_map["original_blocks"][block_key]["members"]

        for i in range(len(mems)):
            if ("rep" in mems[i][1] or "call" in mems[i][1] or "ret" in mems[i][1]) and (i != len(mems) - 1):
                rep_call_blocks.append(mems[i + 1][0])

    # Create new canonical blocks removing duplicate references to blocks, smallest possible
    for block_key in block_offsets:
        if block_key == "meta":
            continue

        # Create new block in canonical dictionary, no original basic blocks will be removed
        # only finer granularity
        output_map["canon_blocks"][block_key] = {}
        canon_block = output_map["canon_blocks"][block_key]

        # Get each basic block in original blocks member list
        member_list = output_map["original_blocks"][block_key]["members"]

        canon_block["members"] = []
        for idx in range(len(member_list)):
            # Keep first instruction, and subsequent until found in basic blocks
            if idx == 0 or (member_list[idx][0] not in block_offsets and member_list[idx][0] not in rep_call_blocks):
                canon_block["members"].append(member_list[idx])
            else:
                # Stop inserting at split block
                canon_block["dests"] = [member_list[idx][0]]
                break

        # If no split block found, maintain jump targets
        if idx == len(member_list) - 1:
            canon_block["dests"] = output_map["original_blocks"][block_key]["dests"]

        last_inst = canon_block["members"][-1]
        if "call" in last_inst[1]:
            canon_block["dests"].append(sorted_instructions[sorted_instructions.index(last_inst[0]) + 1])


def _add_block_to_save(bb_offset: int, bb: dict, header_interface, block_map: dict):
    # Create dictionary for fields of basic block
    block_map[bb_offset] = {}
    block_map[bb_offset]["members"] = []

    # Populate member list for each basic block
    if bb.get("size", 0) > 0:
        for op in bb.get("ops", []):
            if op.get("type") == "invalid":
                continue

            # Some r2 builds give partial op entries so skip instead of failing
            if "offset" not in op or "opcode" not in op:
                continue

            block_map[bb_offset]["members"].append((header_interface.get_offset(int(op["offset"])), op["opcode"]))

    # Instruction sucessors, always jump target first (can we have fail without jump)
    basic_block_destinations = []
    if "jump" in bb and bb["jump"] is not None:
        basic_block_destinations.append(header_interface.get_offset(int(bb["jump"])))
    if "fail" in bb and bb["fail"] is not None:
        basic_block_destinations.append(header_interface.get_offset(int(bb["fail"])))

    logger.debug(basic_block_destinations)
    # Only set control flow on last block, all others are call edges
    block_map[bb_offset]["dests"] = sorted(basic_block_destinations)


def record_function(fun_map: dict, fun: dict, blocks: list, header_interface) -> None:
    """ Populate information in function dictionary
        Parameters -
            fun_map (dict): mapping of function name to features
    """
    # populate function information
    fun_offset = _get_function_offset(fun)
    # Skip unsupported/partial function records when no address key
    if fun_offset is None:
        return

    offset = header_interface.get_offset(fun_offset)
    if offset is None:
        return

    fun_map[offset] = {}
    fun_map[offset]["name"] = fun.get("name", str(fun_offset))
    fun_map[offset]["signature"] = fun.get("signature", fun_map[offset]["name"])

    logger.debug(fun)
    if "nlocals" in fun:
        fun_map[offset]["num_locals"] = fun["nlocals"]
    fun_map[offset]["returning"] = not fun.get("noreturn", False)
    fun_map[offset]["convention"] = fun.get("calltype", "")
    fun_map[offset]["num_args"] = fun.get("nargs", 0)
    fun_map[offset]["cyclo_complexity"]  = fun.get("cc", 0)

    fun_map[offset]["calls"] = []
    if "callrefs" in fun:
        for callref_dict in fun["callrefs"]:
            if "addr" in callref_dict:
                fun_map[offset]["calls"].append(header_interface.get_offset(callref_dict["addr"]))

    fun_map[offset]["blocks"] = blocks


def extract(file_test, header):
    """processes an exectuable with radare2/r2pipe, and disassembles code
        input -
                file_test (filename)- exectuable x86,64 parsable with radare2/r2pipe
    """
    start = time.time()

    try:
        # disable stderr flags=["-2"]
        r2 = r2pipe.open(file_test, flags=['-2'])
    except Exception:  # Radare does not use custom exception
        print('r2pipe exception')
        return {}

    # r2.cmd("e anal.jmptbl=1")  # this is enabled by default
    # https://r2wiki.readthedocs.io/en/latest/options/e/values-that-e-can-modify/anal/

    # Perform full analysis in radare2
    r2.cmd("aaa")

    # cfg is json output of control flow graph
    output_map = {}
    output_map["meta"] = {}
    output_map["instructions"] = {}
    output_map["original_blocks"] = {}
    output_map["canon_blocks"] = {}
    output_map["functions"] = {}

    if not header.known_format:
        logger.info("File Sample is of unknown format, Radare returning empty output.")
        return None

    # Product json, then parse as json into object
    output = r2.cmdj("aflj")

    if not output:
        logging.info("Radare produced no output.")
        return None

    # switch_workinglist = []
    for fun in output:
        fun_offset = _get_function_offset(fun)
        if fun_offset is None:
            # Keep processing remaining functions even if one record uses an unknown schema
            logger.debug("Skipping function without offset fields: %s", fun)
            continue

        # Navigate to function, analyze function, retrieve control flow graph
        r2.cmd("s " + str(fun_offset))
        logger.debug("analyzing %s" % fun_offset)

        # Relocatables have offset 0. Skip these functions
        if fun_offset == 0:
            continue

        r2.cmd("af")
        local_cfg = r2.cmdj("agj")

        # Local cfg returns as [] case, example binary gh0st
        if len(local_cfg) == 0:
            continue

        blocks = local_cfg[0].get("blocks", [])
        block_offsets = []
        # Iterate Radare json control flow graph output, record offset, byte, mnemonics
        for bb in blocks:
            if "offset" not in bb:
                continue

            bb_offset = header.get_offset(bb["offset"])
            if bb_offset is None:
                continue

            block_offsets.append(bb_offset)
            ops = bb.get("ops", [])

            # switch_op = None
            # if "switchop" in bb:
            #    switch_op = bb["switchop"]
            if bb.get("size", 0) > 0:
                for op in ops:
                    if op.get("type") == "invalid":
                        continue

                    if "offset" not in op or "opcode" not in op:
                        continue

                    inst_offset = header.get_offset(int(op["offset"]))
                    if inst_offset is None:
                        return None
                    output_map["instructions"][inst_offset] = op["opcode"]

            _add_block_to_save(bb_offset, bb, header, output_map["original_blocks"])
        record_function(output_map["functions"], fun, block_offsets, header)

    end = time.time()
    output_map["meta"]["time"] = end - start

    # Offsets Obtained
    return output_map
