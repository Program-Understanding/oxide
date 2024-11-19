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

DESC = "CFG"
NAME = "control_flow_graph"
USG = "CFG"
import logging
from typing import Dict, Any, List


from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"disassembler": {"type": str, "mangle": False, "default": "ghidra_disasm"},
            "order_by_node": {"type": bool, "mangle": False, "default": False}
            }


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "Usage": USG}

def generate_cfg(oid: str, opts: dict):
    disasm_output = api.get_field("ghidra_disasm", oid, "functions")
    if not disasm_output:
        logger.error("Failed to extract disassembly")
        return None
    
    original_blocks = api.get_field("ghidra_disasm", oid, "original_blocks")

    cfg = {
        "nodes": [],
        "edges": [],
        "function_calls": {},
        "block_calls": {},
        "functions": {}
    }
    if opts["order_by_node"]:
        cfg["nodes"] = {}
    node_ids = set()

    # Add nodes to cfg
    for block_addr, block_info in original_blocks.items():
        if opts["order_by_node"]:
            if not block_addr in cfg["nodes"]:
                cfg["nodes"][block_addr] = block_info["members"]
        else:
            block_node = {
                "block id": block_addr,
                "instructions": block_info["members"]
            }
            cfg["nodes"].append(block_node)
        node_ids.add(block_addr)
            
    # Add edges to cfg
    for block_addr, block_info in original_blocks.items():
        for dest in block_info["dests"]:
            edge = {
                "from": block_addr,
                "to": dest
            }
            cfg["edges"].append(edge)
            if dest not in node_ids:
                # Add placeholder node for missing destination
                if opts["order_by_node"]:
                    if not block_addr in cfg["nodes"]:
                        cfg["nodes"][block_addr] = [disasm_output.get(dest, "Ghidra issue")]
                else:
                    placeholder_node = {
                        "id": dest,
                        "instructions": [disasm_output.get(dest, "Ghidra issue")]
                    }

                    cfg["nodes"].append(placeholder_node)
                node_ids.add(dest)

    # Add function call edges and function call info
    for func_name, func_info in disasm_output.items():
        if func_name == 'meta':
            continue
        cfg["function_calls"][func_name] = {
            "called_by": [],
            "calls": []
        }
        for block_addr in func_info['blocks']:
            if block_addr in original_blocks:
                for dest in original_blocks[block_addr]['dests']:
                    if dest in disasm_output:
                        edge = {
                            "from": func_name,
                            "to": disasm_output[dest]['name']
                        }
                        cfg["edges"].append(edge)
                        cfg["function_calls"][func_name]["calls"].append(disasm_output[dest]['name'])
                        if disasm_output[dest]['name'] not in cfg["function_calls"]:
                            cfg["function_calls"][disasm_output[dest]['name']] = {
                                "called_by": [],
                                "calls": []
                            }
                        cfg["function_calls"][disasm_output[dest]['name']]["called_by"].append(func_name)

    # Add block call info and function association
    for block_addr, block_info in original_blocks.items():
        cfg["block_calls"][block_addr] = {
            "called_by": [],
            "calls": block_info["dests"],
            "function": None
        }
        for dest in block_info["dests"]:
            if dest not in cfg["block_calls"]:
                cfg["block_calls"][dest] = {
                    "called_by": [],
                    "calls": [],
                    "function": None
                }
            cfg["block_calls"][dest]["called_by"].append(block_addr)

    # Extract functions, basic blocks, and disassembly
    f_dict = {}
    names = api.get_field("file_meta", oid, "names")
    logger.debug("process(%s)", names)

    funs = api.get_field("ghidra_disasm", oid, "functions")
    if not funs:
        return False
    bbs = api.get_field("ghidra_disasm", oid, "original_blocks")
    insns = api.get_field("disassembly", oid, oid)
    if insns and "instructions" in insns:
        insns = insns["instructions"]
    else:
        return False

    range = sorted(insns.keys())
    logger.info("Instruction range: %d - %d", range[0], range[-1])

    extracts = {}
    for f in funs:
        if f == 'meta':
            continue
        fname = funs[f]['name']
        extracts[fname] = funs[f]
        blocks = funs[f]['blocks']
        extracts[fname]['instructions'] = {}
        for b in blocks:
            if b not in bbs:
                continue
            for insn_offset, insn_text in bbs[b]['members']:
                if insn_offset not in insns.keys():
                    logger.error("Basic Block member not found: %s", insn_offset)
                    continue
                extracts[fname]['instructions'][insn_offset] = insn_text
            # Associate block with function
            if b in cfg["block_calls"]:
                cfg["block_calls"][b]["function"] = fname
        range = sorted(extracts[fname]['instructions'].keys())
        if range:
            extracts[fname]["start"] = range[0]
        else:
            extracts[fname]["start"] = None

    cfg["functions"] = extracts

    return cfg



def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}

    for oid in oid_list:
        cfg = generate_cfg(oid, opts)
        if cfg is not None:
            results[oid] = cfg
        
    return results
