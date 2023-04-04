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

# Parsing of IDA pro functions for instructions and basic blocks based on: moritzraabe.de/2017/01/15/ida-pro-anti-disassembly-basic-blocks-and-idapython/
# API documentation: hex-rays.com/products/ida/support/idapython_docs/

from sets import Set

import idaapi
import idautils
from idc import *

def list_to_string(lst):
    out_list = "["
    if len(lst) > 0:
        out_list+= '"%X"' % (lst[0])
    if len(lst) > 1:
        for mem in lst[1:]:
            out_list += ',"%X"'%(mem)
    out_list += "]"
    return out_list


def tars_to_string(lst):
    out_list = "{"
    if len(lst) > 0:
        out_list+= '"%X":%s' % (lst[0][0], list_to_string(lst[0][1]))
    if len(lst) > 1:
        for mem in lst[1:]:
            out_list += ',"%X":%s'%(mem[0], list_to_string(mem[1]))
    out_list += "}"
    return out_list


def get_destination_from_addr(addr, h):
    dests = set()
    coderef_normal = idautils.CodeRefsFrom(addr,True)
    coderef_control = idautils.CodeRefsFrom(addr,False)

    for crf in coderef_normal:
        dests.add(crf)
    for crf in coderef_control:
        dests.add(crf)

    return list(dests)


def main():
    print("Starting")

    ea = ScreenEA()
    # Necessary to allow auto-analysis to complete
    Wait()

    if len(ARGV) < 2:
        sys.exit(0)

    h = open(ARGV[1],'w')

    for func in idautils.Functions():
        # Print function addresses
        print(hex(func))
        print('Function:' + hex(func), file=h)
        # hex-rays.com/products/ida/support/sdkdoc/group___f_c__.html
        # https://hex-rays.com/products/ida/support/sdkdoc/classfunc__t.html
        function = idaapi.get_func(func)
        fname = GetFunctionName(func)

        print('RESULT_F: ["%X", "%s", "%s"]\n\n' % (func, fname, function.llabels), file=h)

        flowchart = idaapi.FlowChart(function)
        for bb in flowchart:
            bb_start = bb.startEA

            members = []
            dests = []
            # Issue, was collecting destination only from last address
            for head in idautils.Heads(bb.startEA, bb.endEA):
                print('RESULT_I: ["%X", "%s"]\n\n'%(head, (GetDisasm(head).replace('"',"'").replace('\\', ''))), file=h)
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
    sys.exit(0)


if __name__ == '__main__':
    main()
