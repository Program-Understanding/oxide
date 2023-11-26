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

import struct


def resolve_destination_operand( insn, header, file_data, funcs = {} ):
    destination_op = insn["operands"].get("operand_0", None)
    if destination_op == None:
        return None
    dest = None
    if header.is_64bit():
        address_length = 8
    else:
        address_length = 4

    if 'type.reg' in destination_op:
        pass  # dest = decode_register_usage(insn, funcs)
    if 'type.imm' in destination_op:
        dest = destination_op['type.imm']
    if 'type.mem' in destination_op:
        # no registers involved; this is an exlicit address.
        if 'base' not in destination_op['type.mem'] and 'segment' not in destination_op['type.mem'] \
              and 'index' not in destination_op['type.mem']:
            dest = header.get_offset(destination_op['type.mem']['displacement'])
    """
    if destination_op["type"] == "eff_addr":
        ea = destination_op["data"]
        if (ea["base"] == None) and (ea["idx"] == None):
            # no registers involved; let's discover the dest addr
            # this is the contents of memory at location ea['disp']
            offset = header.get_offset(ea['disp'])
            if not offset or offset+address_length > len(file_data):
                return None
            if address_length == 4:
                dest_addr = struct.unpack("=L", file_data[offset:offset+address_length])[0]
            else:
                dest_addr = struct.unpack("=Q", file_data[offset:offset+address_length])[0]
            if dest_addr != 0:
                dest = dest_addr
    elif destination_op["type"] in ("reg"):
        dest = decode_register_usage(insn, funcs)
    elif destination_op["type"] not in ['seg_off']:
        dest = destination_op["data"]
    """
    return dest

"""
def decode_register_usage(insn, funcs):
    addr = insn["addr"]
    func = None
    for f in funcs:
        if addr >= funcs[f]["start"] and addr < funcs[f]["end"]:
            func = f
            break
    if not func: return None
    register = insn.get("d_op", None)
    found = False
    val = None
    insns = list(funcs[f]["insns"])
    insns.reverse()
    index = 0
    while(addr != insns[index]["addr"]):
        index += 1
    insns = insns[index:]
    for i in insns:
        if i["mnem"] in ("mov") and i.get("d_op", None) == register:
            found = True
            operand = i.get("s_ops")[0]["data"]
            if isinstance(operand, int):
                val = operand
            elif "disp" in operand:
                val = operand["disp"]
            break
    return val
"""

def instruction_to_string(insn):
    ''' Return an ASCII representation of instruction.
    '''
    buf = insn["mnemonic"] + " " + insn["op_str"]
    return buf

def get_slice(opts):
    start = stop = 0
    if isinstance(opts["slice"], int):
        start = opts["slice"]
        return start, stop

    slice = opts["slice"].split(":")
    if len(slice) == 1:
        start = stop = slice[0]
    elif len(slice) == 2:
        if slice[0]:
            start = int(slice[0])
        if slice[1]:
            stop = int(slice[1])
    else:
        raise SyntaxError("Invalid slice")
    return start, stop
