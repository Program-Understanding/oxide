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

DESC = "Util functions to grab and translate angr disassembly, shared code between fst and emulated angr analysis"

import logging
# Temporarily Suppress Warnings
cle_logger = logging.getLogger("cle")
cle_logger.setLevel(50)
root_logger = logging.getLogger()
current_level = root_logger.level
root_logger.setLevel(50)
import angr
root_logger.setLevel(current_level)
project_logger = logging.getLogger("angr.project")
project_logger.setLevel(50)

NAME = "angr_utils"
logger = logging.getLogger(NAME)

# ------------------------------- Tool 3: angr ---------------------------------------


def get_angr_offset(header_interface) -> int:
    if header_interface.type == "MACHO":
        # Special Case:: angr always loads at 0x100000000, default for macho
        return 0x100000000
    else:
        # otherwise need to use header info
        return -1


def _get_bb_offsets(cfg_nodes, header_interface):
    bb_offsets = []

    # Get list of basic block offset
    for node in cfg_nodes:
        if node.block is not None:
            load_addr = get_angr_offset(header_interface)

            # Check for MACHO
            if load_addr == -1:
                offset = header_interface.get_offset(node.block.addr)
            else:
                offset = node.block.addr - load_addr

            bb_offsets.append(offset)
    return bb_offsets


def _add_block_to_save(bb, header_interface, block_map, members, bb_offsets):
    # Blocks offset
    node_addr = header_interface.get_offset(bb.block.addr)

    duplicate = False
    if node_addr in block_map:
        logger.debug("DUPLICATE FOUND!!!! %s" % node_addr)
        duplicate = True
    else:
        block_map[node_addr] = {}

    # Block sucessors, intrerpret Graph node successors
    basic_block_dests = []
    for node in bb.successors:
        if node.addr is None:
            # TODO:: understand this conditional
            continue
        if header_interface.get_offset(node.addr) is not None:
            basic_block_dests.append(header_interface.get_offset(node.addr))
        else:
            basic_block_dests.append("EXTERNAL:%s" % (node.addr))

    # Resolve fact some edges are to external functions, and de-duplicate
    # TODO:: in case of duplicate merge destinations
    block_map[node_addr]["dests"] = sorted(list(set(basic_block_dests)), key=str)

    # Sorted Instruction Virtaul Addresses,
    # TODO:: in case of duplicate, check members
    block_map[node_addr]["members"] = sorted(members)


def init_angr_project(file_test, header_interface):
    # cannot rebase image to header field (avoiding hardcoded for consistency) in Macho
    if header_interface.type == "MACHO":
        logger.info("Macho found while using angr, ignoring rebase")
        options = {}
    else:
        options = {"force_rebase": True, "base_addr": header_interface.image_base}
    p = angr.Project(file_test, load_options={"auto_load_libs": False}, main_opts=options)

    # Change from 'WARNING' to 'CRITICAL' to supress messages about mach-o and decode errors
    # docs.python.org/3/library/logging.html#level
    cle_logger = logging.getLogger("cle")
    cle_logger.setLevel(50)
    angr_logger = logging.getLogger("angr")
    angr_logger.setLevel(50)
    claripy_logger = logging.getLogger("claripy")
    claripy_logger.setLevel(50)
    pyvex_logger = logging.getLogger("pyvex.lifting.libvex")
    pyvex_logger.setLevel(50)
    pyvex_logger = logging.getLogger("pyvex.lifting.util")
    pyvex_logger.setLevel(50)
    identifier_logger = logging.getLogger("angr.analyses.identifier.identify")
    identifier_logger.setLevel(50)
    return p


def process_functions(cfg, header_interface, output_map):
    """ From CFG, enumerate functions and extract features.
        Unused members
            Some of these may only work effectively on 32 bit
            binary_name is binary that contains function
            info is {} ?
            code_constants are list of literals found in code
                Too much output, and not relevant for comparison
            arguments should be list of arguments passed to function
                did not work with debug O2
            string_refs are list of references to strings
                always none, possibly due to exceptions
            registers_read_after ???
            prototype
    """
    # get list of functions from control flow graph, knowledge base
    function_list = cfg.kb.functions
    for vaddr, fun in function_list.items():
        # https://docs.angr.io/built-in-analyses/cfgi
        vaddr = header_interface.get_offset(vaddr)
        output_map["functions"][vaddr] = {}
        cur_fun = output_map["functions"][vaddr]
        cur_fun["name"] = fun.name
        cur_fun["demangled_name"] = fun.demangled_name
        cur_fun["blocks"] = [header_interface.get_offset(bb.addr) for bb in fun.blocks]
        cur_fun["functions_called"] = [func.name for func in fun.functions_called() if func]
        cur_fun["functions_called"] = list(set(cur_fun["functions_called"]))
        cur_fun["arguments"] = fun.arguments

        """
        try:
            cur_fun["code_constants"] = fun.code_constants
        except angr.errors.SimTranslationError:
            logging.error("angr ran into error, computing code constants inside of function {}".format(fun.name))
        """
        """
        try:
            cur_fun["string_refs"] = fun.string_references()
        except angr.errors.SimEngineError:
            logging.error("angr ran into error computing string references inside of function {}, likely sim procedure".format(fun.name))
        except TypeError:
            logging.error("angr ran into error computing string references inside of function {}".format(fun.name))
        """

        cur_fun["returning"] = fun.returning


def process_cfg(cfg, header_interface):
    output_map = {}
    output_map["meta"] = {}
    output_map["instructions"] = {}
    output_map["original_blocks"] = {}
    output_map["canon_blocks"] = {}
    output_map["functions"] = {}

    if not header_interface.known_format:
        logger.info("File Sample is of unknown format, angr returning empty output.")
        return None

    cfg_nodes = cfg.graph.nodes()

    # List of starting addresses of basic block, used in collecting accurate basic blocks
    bb_offsets = _get_bb_offsets(cfg_nodes, header_interface)

    # Crawl subroutines, and child basic blocks to find instructions
    for node in cfg_nodes:
        # FIXME::Debug why this exists, Handle case where basic block is Null,
        if node.block is not None:
            members = []

            # Sort through capstone structure for basic block
            try:
                for inst in node.block.capstone.insns:
                    load_addr = get_angr_offset(header_interface)

                    if load_addr == -1:
                        offset = header_interface.get_offset(inst.address)
                    else:
                        offset = inst.address - load_addr
                    if not offset: offset = inst.address

                    insn_str = inst.insn.mnemonic + ("  " if inst.insn.op_str != '' else "") + inst.insn.op_str
                    # Save instruction to list, and relate to basic block offset
                    output_map["instructions"][offset] = insn_str
                    members.append((offset, insn_str))
            except KeyError:
                logger.debug("Decode error in capstone instructions")
                continue

            _add_block_to_save(node, header_interface, output_map["original_blocks"], members, bb_offsets)

    process_functions(cfg, header_interface, output_map)

    return output_map
