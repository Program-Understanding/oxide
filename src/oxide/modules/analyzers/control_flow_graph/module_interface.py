AUTHOR="Cam Stanford"
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
    names = api.get_field("file_meta", oid, "names")
    logger.debug("process(%s)", names)

    funs = api.retrieve("function_extract", oid)
    if not funs:
        return False
    cfg["functions"] = funs

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
