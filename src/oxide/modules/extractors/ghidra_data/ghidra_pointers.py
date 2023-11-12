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

""" Wrapper for scripts for Ghidra to extract global and local variables (pointers)
"""

import logging

from oxide.core.libraries.ghidra_utils import get_file_offset

SRC_VER = 0.1
OFFSETS_OFF = False

NAME = "ghidra_data"
logger = logging.getLogger(NAME)

LOAD_ADDR = 0

# --------------------------- Tool 5: Ghidra -----------------------------------------


"""
    Persistent bugs:
        Ghidra 9.2.2 produces address "1000:0000" while 9.0.2 "00400000"
"""


def _extract_stack_pointers(ghidra_export: dict, header_interface) -> dict:
    """ From XML export, parse each functions stack frames

    Args:
        ghidra_export (dict): XML dump of Ghidra database, specifically of interest
                              STACK_FRAME from FUNCTIONS
    """
    stack_ptrs = {}
    fun_count = 1
    for fun, info in ghidra_export["FUNCTIONS"].items():
        if "STACK_FRAME" in info:
            for stack_var, var_info in info["STACK_FRAME"].items():
                if stack_var in ["RETURN_ADDR_SIZE", "LOCAL_VAR_SIZE", "PARAM_OFFSET", "BYTES_PURGED"]:
                    # Skip return addr on stack
                    continue
                vaddr = int(fun, 16)
                # print("var_info", get_file_offset(vaddr, header_interface, LOAD_ADDR), stack_var, var_info)
                size = int(var_info["SIZE"][2:], 16)
                # normalize stack offset to be positive
                offset = (-1 * int(stack_var[1:], 0)) if (stack_var[0] == "-") else int(stack_var, 0)
                # For each function, find mapping of functions
                stack_ptrs[fun_count] = {"fun": get_file_offset(vaddr, header_interface, LOAD_ADDR),
                                         "offset": offset,
                                         "size": size}
                fun_count += 1
    return stack_ptrs


def _extract_global_pointers(ghidra_export: dict, header_interface) -> dict:
    """ From XML export, parse global data values

    Args:
        ghidra_export (dict): XML dump of Ghidra database, specifically of interest
                              DATA (location and size)
    """
    global_data = {}
    for vaddr, info in ghidra_export["DATA"].items():
        try:
            vaddr = int(vaddr, 16)
            # print(info)
            # size in hex
            size = int(info["SIZE"][2:], 16)
            if vaddr is None:
                pass
                # print("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
                # print("NONE", vaddr, info)
                # print("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
            global_data[get_file_offset(vaddr, header_interface, LOAD_ADDR)] = {"size": size, "type": info['DATATYPE']}
        except ValueError:
            # print(vaddr.split(":"), info)
            continue

    # .shstrtab
    # .strtab

    return global_data


def _extract_indirect_control(ghidra_cfg: dict) -> dict:
    """ From control flow graph extracted, parse for indirect
        jumps and destinations

    Args:
        ghidra_cfg (dict): Mapping of offsets in binary to basic blocks
                           with members and destinations
    """
    def intersection(lst1, lst2):
        return list(set(lst1) & set(lst2))

    indirect_control = {}

    control_flow = ["CALL", "jmp", "je", "jne", "js", "jns", "jg", "jge", "jl", "jle", "ja", "jae", "jb", "jbe"]
    reg_list = ["ax", "al"   # ?x covers 64, 32, and 16 bit regs
                "bx", "bl",  # must ignore high bits without using capstone
                "cx", "cl",
                "dx", "dl",
                "si", "di", "sp", "bp", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]  # these cover all variants

    # TODO:: move to capstone, call overwrites al, so use CALL replacement
    # remove meta field of cfg
    if "meta" in ghidra_cfg: del ghidra_cfg["meta"]
    for _, bb_info in ghidra_cfg.items():
        last_inst_offset, last_inst_in_bb = bb_info["members"][-1]  # last instruction in member, disassembly text
        # update last_inst_in_bb
        last_inst_in_bb = last_inst_in_bb.replace("call", "CALL")
        if len(intersection(control_flow, last_inst_in_bb.split())) > 0:
            if any(reg in last_inst_in_bb for reg in reg_list):
                # destination corresponds to values
                indirect_control[last_inst_offset] = {"inst": last_inst_in_bb, "values": bb_info["dests"]}
    return indirect_control


def extract(header_interface, ghidra_export, ghidra_cfg, load_addr):
    """ Runs instruction extraction from ghidraHEADLESS using a java language
        script.

        Input -
            file_test (file) - Sample using bap.run() which runs analyses
            header_interface (header) - header object using header utiility lib

        Returns -
            output_map (dict) - dictionary containing facts extracted from tool
    """
    global LOAD_ADDR
    LOAD_ADDR = load_addr

    output_map = {}
    output_map["meta"] = {}
    output_map["global_data"] = {}
    output_map["local_data"] = {}
    output_map["indirect_control"] = {}
    # dynamic_allocation
    # other

    output_map["local_data"] = _extract_stack_pointers(ghidra_export, header_interface)
    output_map["global_data"] = _extract_global_pointers(ghidra_export, header_interface)
    output_map["indirect_control"] = _extract_indirect_control(ghidra_cfg)

    # If everything is empty, than an issue occured
    if ((0 == len(output_map["local_data"])) and (0 == len(output_map["global_data"])) and
      (0 == len(output_map["indirect_control"]))):
        logger.error("Ghidra found no pointers, or export parsing failed.")
        return None

    return output_map
