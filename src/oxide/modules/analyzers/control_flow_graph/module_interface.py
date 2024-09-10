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

opts_doc = {"disassembler": {"type": str, "mangle": False, "default": "ghidra_disasm"}}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "Usage": USG}

def generate_cfg(oid: str, opts: dict):
    disasm_output = api.get_field("ghidra_disasm", oid, "functions")
    if not disasm_output:
        logger.error("Failed to extract disassembly")
        return None
    
    instructions = api.get_field("ghidra_disasm", oid, "instructions")
    original_blocks = api.get_field("ghidra_disasm", oid, "original_blocks")

    cfg = {
        "nodes": [],
        "edges": []
    }

    node_ids = set()

    # Add nodes to cfg
    for block_addr, block_info in original_blocks.items():
        block_node = {
            "id": block_addr,
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
                placeholder_node = {
                    "id": dest,
                    "instructions": [disasm_output.get(dest, "Ghidra issue")]
                }
                
                cfg["nodes"].append(placeholder_node)
                node_ids.add(dest)

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