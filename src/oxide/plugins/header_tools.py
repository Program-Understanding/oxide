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

""" Plugin: Utility functions for analyzing file headers
"""
import capstone
import operator
from collections import defaultdict

from oxide.core import progress, api
import re_lib


def header_stats(args, opts):
    """
        Show some basic statistics on the headers for each file passed in.
        Syntax: header_stats %<oid> ...
    """
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")

    oids = api.expand_oids(valid)

    for oid in oids:
        header = api.get_field("object_header", [oid], oid)
        if not header:
            print("%s (%s) - No header found." % (name(oid), oid))
        else:
            file_size = api.get_field("file_meta", oid, "size")
            src_type = api.get_field("src_type", oid, "type")
            entry_string = ""
            for e in header.entry_addrs:
                entry_string += "%s (%s)  " % (hex(e), (e))
            dlls = 0
            imported_functions = 0
            if header.imports:
                dlls = len(header.imports)
                for i in header.imports:
                    imported_functions += len(header.imports[i])
            print("%s (%s) - %s (%d bytes)" % (name(oid), oid, src_type, file_size))
            print(" - Number of Sections: %s, %d imported libraries with %d funcitons "
                    % (len(header.section_info), dlls, imported_functions))
    return oids


def imports(args, opts):
    """
        Displays the import table
        Syntax: imports <oid>
    """
    args, invalid = api.valid_oids(args)
    oids = api.expand_oids(args)
    if not oids:
        raise ShellSyntaxError("Must provide an oid")

    for oid in oids:
        print("\n  - Import Table for %s %s " % (name(oid), oid))

        header = api.get_field("object_header", oid, oid)
        if not header:
            print("  --------------------------")
            print("   <EMPTY HEADER>")
            print("  --------------------------")
            continue

        src_type = api.get_field("src_type", oid, "type")
        if "PE" in src_type:
            pe_import_table(header, opts)
        elif "ELF" in src_type:
            elf_import_table(header, opts)
        elif "MACHO" in src_type:
            macho_import_table(header, opts)
        else:
            print("  - Source type %s is unsupported" % (src_type))
    return oids


def imports_histogram(args, opts):
    """ Display histogram of imports for PE files across a collection, and compute similarity of imports
            e.g. calculate number of unique imports included in N2% of dataset
            considers Functions, Functions associate to a specific DLL, and DLLs
        First calculates size of list of functions that are shared between a collection
        then adds fuzzy threshold to rule out rare outliers
        Syntax: imports <oid>
    """
    args, invalid = api.valid_oids(args)
    oids = api.expand_oids(args)
    if not oids:
        raise ShellSyntaxError("Must provide an oid")

    # Number of files that share a set of imports
    if 'threshold' in opts:
        THRESHOLD = opts['threshold'] / 100
    else:
        THRESHOLD = 90 / 100
    # % of imports searching for in common, leave some epsilon out to avoid long runtimes
    THRESHOLD2 = 0.95

    # Set up global data structures to store intermediate analysis
    lib_hist = defaultdict(int)
    func_hist = defaultdict(int)
    importname_hist = defaultdict(int)
    common_functions = set()
    all_imports = defaultdict(set)  # file to imports
    importname_map = defaultdict(set)  # function to set of libaries it came from

    for oid in oids:
        # for each file in collection
        header = api.get_field("object_header", oid, oid)
        if not header:
            continue

        src_type = api.get_field("src_type", oid, "type")
        if "PE" in src_type:
            file_imports = extract_pe_imports(header, opts)
            lib_seen = set()

            if not file_imports:
                continue
            for lib, func in file_imports:
                if isinstance(func, int):
                    continue
                if lib not in lib_seen:
                    lib_hist[lib] += 1
                    lib_seen.add(lib)
                func_hist[(lib, func)] += 1  # increment count for library+function
                importname_hist[func] += 1  # Ignores the specific library from which function imported
                importname_map[func].add(lib)  # Notes which libraries each function can be imported from to get idea possibilities
                all_imports[oid].add(func)  # note functions included in this file
        else:
            print("  - Source type %s is unsupported" % (src_type))

    # keep list of functions from most imported to least
    sorted_funcs = sorted(importname_hist.items(), key=operator.itemgetter(1), reverse=True)
    import plotly.express as px
    import pandas as pd
    # Create datastructure and interactive visualization for popular imported functions for a dataset
    df = pd.DataFrame(dict(
        functions = range(len(sorted_funcs)),
        popularity = [tup[1] for tup in sorted_funcs]
    ))
    fig = px.line(df, x="function", y="popularity", title="popularity (imported in file) of each function")
    fig.write_image('shared_function_popularity.png')
    i = 0
    while i < len(sorted_funcs):
        shared = 0
        # check number of files that meet threshold from functions in set of common functions
        for oid in oids:
            if all_imports[oid].issubset(common_functions):
                shared += 1
        # are we done
        if shared >= (len(oids) * THRESHOLD):
            break

        common_functions.add(sorted_funcs[i][0])
        i += 1
    else:
        # End of loop condition, if sucessfully breaks this else condition is skipped
        # TODO:: this can be made more clear through refactoring loop conditions
        print('not fully shared')
    print("fully shared {} percent of files: ".format(THRESHOLD * 100), len(common_functions), "/", len(sorted_funcs))

    importname_copy = importname_hist.copy()
    sorted_funcs = sorted(importname_copy.items(), key=operator.itemgetter(1), reverse=True)
    common_functions = set()
    working_fun_set = []
    sharing_files = set()
    while True:
        # print("functions that increase sharing", len(common_functions))
        # check current shared
        for oid in oids:
            # imports for my file, minus shared, do we have less than n% left
            if len(all_imports[oid] - common_functions) <= (len(all_imports[oid]) * (1 - THRESHOLD)):
                if oid not in sharing_files:
                    working_fun_set.append(len(common_functions))
                    sharing_files.add(oid)
                    # update all references
                    for func in all_imports[oid]:
                        importname_copy[func] -= 1

        # print(len(sharing_files), len(oids))
        # are we done
        if (len(sharing_files) / len(oids)) >= THRESHOLD2 :
            break

        # remove previous most popular
        del importname_copy[sorted_funcs[0][0]]
        sorted_funcs = sorted(importname_copy.items(), key=operator.itemgetter(1), reverse=True)

        if not sorted_funcs:
            print('not fully shared')
            break
        # DEBUG print("adding", sorted_funcs[0][0])
        funcs_that_max_coverage.add(sorted_funcs[0][0])

    if len(sharing_files) == len(working_fun_set):
        df = pd.DataFrame(dict(
            files = range(len(sharing_files)),
            functions = working_fun_set
        ))
        fig = px.line(df, x="files", y="functions", title="functions largely shared within {} files".format(THRESHOLD*100))
        fig.write_image('common_functions_{}.png'.format(THRESHOLD * 100))
        print("{} percent in common in {} percent of the files: ".format(THRESHOLD * 100, THRESHOLD2 * 100), len(common_functions), "/", len(importname_hist))

    """ Printing most popular (up to 25) libraries/functions to user
    import pprint
    pprint.sorted = lambda x, key=None: x
    a = sorted(lib_hist.items(), key=operator.itemgetter(1), reverse=True)
    y = 0
    for x in a:
        y += 1
        if y > 25:
            break
        print(x)
    print('total libraries', len(a))
    a = sorted(func_hist.items(), key=operator.itemgetter(1), reverse=True)
    y = 0
    for x in a:
        y += 1
        if y > 25:
            break
        print(x)
    print('union_f', len(a))
    a = sorted(importname_hist.items(), key=operator.itemgetter(1), reverse=True)
    y = 0
    for x in a:
        y += 1
        if y > 25:
            break
        print(x)
    print("total functions sans library: ", len(a))
    """
    return oids


def destination_operands(args, opts):
    """ Display the value and library/function for call instructions
            e.g. display mapping of addresses to the associated library call 0x400000 -> printf
        Syntax: destination_operands <oid>
    """
    args, invalid = api.valid_oids(args)
    oids = api.expand_oids(args)
    if not oids:
            raise ShellSyntaxError("Must provide an oid")
    for oid in oids:
        insns = api.get_field("disassembly", oid, oid)
        if insns and "instructions" in insns:
            insns = insns["instructions"]
        else: break
        data = api.get_field("files", oid, "data")
        header = api.get_field("object_header", [oid], oid)
        if not insns: continue
        for i in insns:
            if "operand_0" in insns[i]['operands']:
                if "call" in insns[i]['groups'] or "jump" in insns[i]['groups']:
                    if "type.mem" in insns[i]['operands']['operand_0']:
                        print(header.get_rva(i), i, insns[i]['mnemonic'], re_lib.resolve_destination_operand(insns[i], header, data), insns[i]['operands']['operand_0'])


def instruction_offsets(args, opts):
    """
        Check the validity of the instruction offsets found by disassemblers.
            Sanity check across a collection looking for errors
        Syntax: instruction_offsets <oid>
    """
    args, invalid = api.valid_oids(args)
    oids = api.expand_oids(args)
    if not oids:
            raise ShellSyntaxError("Must provide an oid")

    cap = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32)
    for oid in oids:
        print("\n  - Instruction Offsets for %s %s " % (name(oid), oid))
        file_size = api.get_field("file_meta", oid, "size")
        data = api.get_field("files", oid, "data")
        header = api.get_field("object_header", [oid], "header")
        if not header:
            print("%s (%s) - No header found." % (name(oid), oid))
        else:
            obj_insns = api.get_field("objdump", oid, "instructions")
            dis_insns = api.get_field("disassembly", oid, "insns")
            ghi_insns = api.get_field("ghidra_disasm", oid, "instructions")
            angr_insns = api.get_field("fst_angr_disasm", oid, "instructions")
            emu_angr_insns = api.get_field("emu_angr_disasm", oid, "instructions")
            rvas = list(obj_insns.keys())
            for addr in rvas:
                if type(addr) == str:
                    continue
                offset = header.get_offset(addr)
                print(offset, " : ", obj_insns[addr])
                if not offset or offset > file_size: print("BAD OFFSET\n")
                if offset in ghi_insns:
                    i = ghi_insns[offset]
                    print("%s" %(i))
                else:
                    print("Insn not found in Ghidra.")
                if angr_insns and offset in angr_insns:
                    i = angr_insns[offset]
                    print(i)
                else:
                    print("Insn not found in angr.")
                if emu_angr_insns and offset in emu_angr_insns:
                    i = emu_angr_insns[offset]
                    print(i)
                else:
                    print("Insn not found in Emulated/SymExe angr.")


def instruction_compare(args, opts):
    """
        Displays a comparison chart for all disasemblers
        Syntax: instruction_compare <oid>
    """
    args, invalid = api.valid_oids(args)
    oids = api.expand_oids(args)
    if not oids:
            raise ShellSyntaxError("Must provide an oid")

    for oid in oids:
        print("\n  - Instruction Offsets for %s %s " % (name(oid), oid))
        file_size = api.get_field("file_meta", oid, "size")
        data = api.get_field("files", oid, "data")
        header = api.get_field("object_header", [oid], "header")
        if not header:
            print("%s (%s) - No header found." % (name(oid), oid))
        else:
            obj_insns = api.get_field("objdump", oid, "instructions")
            if obj_insns: obj_offs = obj_insns.keys()
            else: obj_offs = set()
            print("Objdump found %d instructions."%len(obj_offs))

            ghi_insns = api.get_field("ghidra_disasm", oid, "instructions")
            if ghi_insns: ghi_offs = ghi_insns.keys()
            else: ghi_offs = set()
            print("Ghidra found %d instructions."%len(ghi_offs))

            angr_insns = api.get_field("fst_angr_disasm", oid, "instructions")
            if angr_insns: angr_offs = angr_insns.keys()
            else: angr_offs = set()
            print("angr found %d instructions."%len(angr_offs))

            emu_angr_insns = api.get_field("emu_angr_disasm", oid, "instructions")
            if emu_angr_insns: emu_angr_offs = emu_angr_insns.keys()
            else: emu_angr_offs = set()
            print("Emulated angr found %d instructions."%len(emu_angr_offs))


exports = [header_stats, imports, imports_histogram, instruction_offsets, instruction_compare, destination_operands]

##################### UTILS ############################


def name(oid):
    if api.exists("file_meta", oid):
        return api.get_field("file_meta", oid, "names").pop()
    elif api.exists("collections_meta", oid):
        return api.get_colname_from_oid(oid)
    return None


def macho_import_table(header, opts):
    print("  --------------------------")
    print("  - Import Address Table :")
    if not header.imports:
        print("    + No import table")

    else:
        entries = list(header.imports.keys())
        entries.sort()
        for entry in entries:
            print("    - Lib: ", entry)
            if "verbose" in opts:
                names = list(header.imports[entry].keys())
                names.sort()
                for name in names:
                    value = header.imports[entry][name]["n_value"]
                    print("      - %s   :   %s (%s)" % ( name, hex(value), value))


def elf_import_table(header, opts):
    print("  --------------------------")
    print("  - Import Address Table :")
    if not header.imports:
        print("    + No import table")

    else:
        entries = list(header.imports.keys())
        entries.sort()
        for entry in entries:
            print("    - Lib: ", entry)
            if "verbose" in opts:
                names = list(header.imports[entry].keys())
                names.sort()
                for name in names:
                    value = header.imports[entry][name]["value"]
                    print("      - %s   :   %s (%s)" % ( name, hex(value), value))


def pe_import_table(header, opts):
    print("  --------------------------")
    print("  - Import Address Table :")
    if not header.imports:
        print("    + No import table")
    else:
        for entry in header.imports:
            print("    - DLL: ", entry)
            if "verbose" in opts and "function_names" in header.imports[entry]:
                for imp in header.imports[entry]["function_names"]:
                    print("      - %s"%(imp))

    print("  --------------------------")
    print("  - Delay Import Address Table:")
    if not header.delay_imports:
        print("    + No delay import table")
    else:
        for entry in header.delay_imports:
            print("    - DLL: ", entry)
            if "verbose" in opts and "function_names" in header.delay_imports[entry]:
                for imp in header.delay_imports[entry]["function_names"]:
                    print("      - %s"%(imp))
        print("  --------------------------")


def extract_pe_imports(header, opts):
    file_imports = set()
    if header.imports:
        for lib in header.imports:
            if not header.imports[lib]: continue
            if "function_names" in header.imports[lib] and header.imports[lib]["function_names"]:
                for func in header.imports[lib]["function_names"]:
                    file_imports.add((lib, func))

    if header.delay_imports:
        for lib in header.delay_imports:
            if not header.delay_imports[lib]: continue
            if "function_names" in header.delay_imports[lib] and header.delay_imports[lib]["function_names"]:
                for func in header.delay_imports[lib]["function_names"]:
                    file_imports.add((lib, func))
    return file_imports
