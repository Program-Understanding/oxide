# IDA-VIS.py
from __future__ import print_function
import sys

# moritzraabe.de/2017/01/15/ida-pro-anti-disassembly-basic-blocks-and-idapython/
# hex-rays.com/products/ida/support/idapython_docs/


import idaapi
import idautils
from idc import *

# hOOK WITH cODEMAP
# github.com/c0demap/codemap
# Incorperate Graph Slick
# Incoperate Rizzo

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


def get_target_from_addr(addr, h):
    targets = set()
    coderef_normal = idautils.CodeRefsFrom(addr,True)
    coderef_control = idautils.CodeRefsFrom(addr,False)

    for crf in coderef_normal:
        targets.add(crf)
    for crf in coderef_control:
        targets.add(crf)

    return list(targets)


def main():
    print("Starting")


    ea = get_screen_ea()

    # Disable macros
    ida_ida.inf_set_af2(ida_ida.inf_get_af2() & ~AF2_MACRO)
    auto_wait()

    if len(ARGV) < 2:
        sys.exit(0)

    h = open(ARGV[1],'w')

    i = 0
    for func in idautils.Functions():
        i += 1
        # Print function addresses
        print(hex(func))
        print('Function:' + hex(func), file=h)
        # hex-rays.com/products/ida/support/sdkdoc/group___f_c__.html
        # https://hex-rays.com/products/ida/support/sdkdoc/classfunc__t.html
        function = idaapi.get_func(func)
        fname = get_func_name(func)
        #took out function.llabels
        print('RESULT_F: ["%X", "%s"]\n\n' % (func, fname), file=h)

        flowchart = idaapi.FlowChart(function)
        for bb in flowchart:
            bb_start = bb.start_ea

            members = []
            targets = []
            # Issue, was collectin target only from last address
            for head in idautils.Heads(bb.start_ea, bb.end_ea):
                print('RESULT_I: ["%X", "%s"]\n\n'%(head, (GetDisasm(head).replace('"',"'").replace('\\', ''))), file=h)
                members.append(head)
                insn_type = print_insn_mnem(head)
                # Tricky to encode target, with only instruction knowing successors
                # Cannot filter on 2+ target, as nonerturning calls
                # Solution store dictionary, keep general mnemonics, original basic block, merge all, canonical split out
                if insn_type in ["call"]:
                    mem_tars = get_target_from_addr(head, h)
                    targets.append((head, mem_tars))

            member_str = list_to_string(members)

            # Dedup if block ends with call
            if insn_type not in ["call"]:
                mem_tars = get_target_from_addr(head, h)
                targets.append((head, mem_tars))

            target_str = tars_to_string(targets)

            print('RESULT_B: ["%X", %s, %s]\n\n'%(bb_start, target_str, member_str), file=h)

    print("Done")
    sys.exit(0)


if __name__ == '__main__':
    main()
