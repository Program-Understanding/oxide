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

# ida_info_out.py
from __future__ import print_function
import sys

# moritzraabe.de/2017/01/15/ida-pro-anti-disassembly-basic-blocks-and-idapython/
# hex-rays.com/products/ida/support/idapython_docs/

# from sets import Set

import idaapi
import idautils
from idc import *
from ida_auto import auto_wait


def list_to_string(lst):
    out_list = "["
    if len(lst) > 0:
        out_list += '"%X"' % (lst[0])
    if len(lst) > 1:
        for mem in lst[1:]:
            out_list += ',"%X"' % (mem)
    out_list += "]"
    return out_list


def tars_to_string(lst):
    out_list = "{"
    if len(lst) > 0:
        out_list += '"%X":%s' % (lst[0][0], list_to_string(lst[0][1]))
    if len(lst) > 1:
        for mem in lst[1:]:
            out_list += ',"%X":%s' % (mem[0], list_to_string(mem[1]))
    out_list += "}"
    return out_list


def get_destination_from_addr(addr, h):
    dests = set()
    coderef_normal = idautils.CodeRefsFrom(addr, True)
    coderef_control = idautils.CodeRefsFrom(addr, False)

    for crf in coderef_normal:
        dests.add(crf)
    for crf in coderef_control:
        dests.add(crf)

    return list(dests)


def main():
    print("Starting")

    ea = get_screen_ea()
    # Necessary to allow auto-analysis to complete
    auto_wait()

    if len(ARGV) < 2:
        print("No outpufile provided {}".format(ARGV))
        return

    h = open(ARGV[1],'w')

    for func in idautils.Functions():
        # Print function addresses
        print(hex(func))
        print('Function:' + hex(func), file=h)
        # hex-rays.com/products/ida/support/sdkdoc/group___f_c__.html
        # https://hex-rays.com/products/ida/support/sdkdoc/classfunc__t.html
        function = idaapi.get_func(func)
        fname = get_func_name(func)

        print('RESULT_F: ["%X", "%s"]\n\n' % (func, fname), file=h)

        flowchart = idaapi.FlowChart(function)
        for bb in flowchart:
            bb_start = bb.start_ea

            members = []
            dests = []
            # Issue, was collecting destination only from last address
            for head in idautils.Heads(bb.start_ea, bb.end_ea):
                # flags: 1 is force code, 2 is multi-line (https://www.hex-rays.com/products/ida/support/idadoc/273.shtml)
                print('RESULT_I: ["%X", "%s"]\n\n'%(head, (generate_disasm_line(head, 0).replace('"',"'").replace('\\', ''))), file=h)
                members.append(head)
                insn_type = print_insn_mnem(head)
                # Tricky to encode destination, with only instruction knowing successors
                # Cannot filter on 2+ destination, as non-returning calls
                # Solution store dictionary, keep general mnemonics, original basic block, merge all, canonical split out
                if insn_type in ["call"]:
                    mem_tars = get_destination_from_addr(head, h)
                    dests.append((head, mem_tars))

            member_str = list_to_string(members)

            # Dedup if block ends with call
            if insn_type not in ["call"]:
                mem_tars = get_destination_from_addr(head, h)
                dests.append((head, mem_tars))

            destination_str = tars_to_string(dests)

            print('RESULT_B: ["%X", %s, %s]\n\n' % (bb_start, destination_str, member_str), file=h)

    print("Done")


if __name__ == '__main__':
    main()
