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

""" Script for visualization and creating DOT format graphs and PNG from CFG

"""

import itertools

import networkx as nx
import logging
import os
import warnings

# In case graphviz layout is preferred, this is an option 'graphviz_layout' as well
from networkx.drawing.nx_agraph import write_dot, to_agraph

logger = logging.getLogger('Coverage')

def _cfg_to_networkx(block_map: dict):
    """ Take in canonical basic block graph, and produce networkx graph from edges
        Input -
            block_map - canonical basic block dictionary, offset -> (members, dests)
        Output -
            bb_graph - networkx graph representing control flow graph
    """
    bb_graph = nx.DiGraph()
    bb_graph.add_nodes_from(block_map.keys())

    for block in block_map:
        if block == "meta":
            continue

        bb_graph.add_edges_from(itertools.product([block], block_map[block]["dests"]))

    return bb_graph

def _compare_to_networkx(block_map: dict, ref_map: dict):
    """ Take in canonical basic block graph, and produce networkx graph from edges
        Input -
            block_map - canonical basic block dictionary, offset -> (members, dests)
        Output -
            bb_graph - networkx graph representing control flow graph
    """
    bb_graph = nx.DiGraph()

    # Set node as red if reference tool is missing basic block
    tool_unique = [item for item in block_map.keys() if item not in ref_map.keys()]
    remaining_blocks = [item for item in block_map.keys() if item not in tool_unique]

    #print([(bb, {'color': 'green'}) for bb in tool_unique])
    #print(remaining_blocks)
    bb_graph.add_nodes_from([(bb, {'color': 'red'}) for bb in tool_unique])
    bb_graph.add_nodes_from(remaining_blocks)

    for block in block_map:
        if block == "meta":
            continue

        bb_graph.add_edges_from(itertools.product([block], block_map[block]["dests"]))

    return bb_graph


def _save_dot_and_png(bb_graph: nx.DiGraph, oid:str, tool: str, bb_type: str) -> None:
    """ From directed networkx graph, save png and dot format files.
    """
    if bb_type == "canon_blocks":
        file_prefix = "cbb"
    elif bb_type == "original_blocks":
        file_prefix = "obb"
    else:
        logger.error("Invalid basic block key passed to output map, in save_dot_and_png")

    mapping = {}
    for n_id in bb_graph.nodes():
        if n_id == "meta" or isinstance(n_id, str):
            continue
        mapping[n_id] = hex(n_id)

    renamed_graph = nx.relabel_nodes(bb_graph, mapping)

    # Suppress warning for lage graph being format as neato
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        # Write out to dot text file for later
        write_dot(bb_graph, "data/coverage/%s_%s_%s.dot" % (oid, file_prefix, tool))

        # set to DOT format and save PNG
        A = to_agraph(renamed_graph)
        A.layout("dot")
        A.draw("data/coverage/%s_%s_%s.png" % (oid, file_prefix, tool))
        # plft.show()

def get_file_offset(vaddr, header_interface):
    if header_interface.type == "ELF":
        if header_interface.etype == "Shared object file":
            # If shared object, rebase off 32 or 64 bit
            if header_interface.is_64bit() is True:
                load_addr = 0x100000
            else:
                load_addr = 0x10000 # 0x8048000
        else:
            # non-PIE, so use header info
            return header_interface.get_offset(vaddr)
    elif header_interface.type == "MACHO":
        load_addr = 0x100000000
    elif header_interface.type == "PE":
        if header_interface.is_64bit():
            load_addr = 0x140010000
        else:
            load_addr = 0x400c00
    return vaddr - load_addr

def reachability_from_addr(args, opts) -> None:
    """ Compute Reachability graph from basic blocks, and start address
        $ reachability_from_addr <oid> <addr in hex>
        Args:
            oid - Program under test, id
            address - virtual address or offset of interest
    """
    if len(args) < 2:
        logger.error("usage: reachability_from_addr <oid> <addr>")
        return

    valid, invalid = api.valid_oids(args)
    valid = api.expand_oids(valid)
    oid = valid.pop()

    str_addr = args[1]
    int_addr = int(args[1], 16)

    out_map = api.retrieve("ghidra_disasm", oid)
    function_map = api.retrieve("objdump", oid)['functions']

    header = api.retrieve("object_header", oid)['header']

    if out_map is not None:
        # Networkx computation on original blocks
        block_map = out_map["original_blocks"]
        bb_graph = _cfg_to_networkx(block_map)
        if bb_graph.has_node(int_addr):
            reachable_pc = []
            reachable_blocks = [int_addr] + list(nx.descendants(bb_graph, int_addr))
            for bb in reachable_blocks:
                if bb in out_map['original_blocks']:
                    reachable_pc += [ inst[0] for inst in out_map['original_blocks'][bb]['members']]
                else:
                    reachable_pc += ["EXTERNAL"+hex(bb)]
            print([ addr if isinstance(addr, str) else hex(addr) for addr in reachable_pc])
            print(len(reachable_pc))
            for i in reachable_blocks:
                offset = get_file_offset(i, header)
                if offset in function_map:
                    print(hex(i), function_map[offset])


def graphic_from_cfg(args, opts) -> None:
    """ Traverse tools, and grab basic blocks to create networkx graphs
    """
    logger.info("Initializing Graphs and Exporting PNG to images/")
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    valid = api.expand_oids(valid)

    # Create data directory if one does not exist
    os.makedirs('data/', exist_ok=True)
    os.makedirs('data/coverage', exist_ok=True)

    for oid in valid:
        # For each tool that is available, fetch saved results
        #tool_list = ['ghidra_disasm', 'fst_angr_disasm', 'ida_disasm', 'bap_disasm', 'emu_angr_disasm', 'radare_disasm', 'objdump']  # 'bap_bwoff'
        tool_list = ['ghidra_disasm']
        for tool in tool_list:
            out_map = api.retrieve(tool, oid)
            if out_map is not None:

                # Networkx computation on original blocks
                block_map = out_map["original_blocks"]

                bb_graph = _cfg_to_networkx(block_map)
                _save_dot_and_png(bb_graph, oid, tool, "original_blocks")

                # Networkx computation on canonical blocks
                block_map = out_map["canon_blocks"]

                bb_graph = _cfg_to_networkx(block_map)
                _save_dot_and_png(bb_graph, oid, tool, "canon_blocks")


def visual_compare(args, opts):
    """ Traverse tools, and grab basic blocks to create networkx graphs
    """
    logger.info("Initializing Graphs and Exporting PNG to images/")
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    valid = api.expand_oids(valid)

    if 'ref' not in opts:
        logger.info('No reference tool provided, returning.')
        return

    # Create data directory if one does not exist
    os.makedirs('data/', exist_ok=True)
    os.makedirs('data/coverage', exist_ok=True)

    for oid in valid:
        # For each tool that is available, fetch saved results
        tool_list = ['ghidra_disasm', 'fst_angr_disasm', 'ida_disasm', 'bap_disasm', 'emu_angr_disasm', 'radare_disasm', 'objdump']
        # remove reference from tool list if present
        modified_tool_list = [item for item in tool_list if item not in [opts['ref']]]

        ref_map = api.retrieve(opts['ref'], oid)
        ori_ref_map = ref_map['original_blocks']

        for tool in tool_list:
            out_map = api.retrieve(tool, oid)
            if out_map is not None:

                # Networkx computation on original blocks
                block_map = out_map["original_blocks"]

                bb_graph = _cfg_to_networkx(block_map)
                # bb_graph = _compare_to_networkx(block_map, ori_ref_map)
                _save_dot_and_png(bb_graph, oid, '{0}v{1}'.format(opts['ref'], tool), "original_blocks")

exports = [graphic_from_cfg, visual_compare, reachability_from_addr]
