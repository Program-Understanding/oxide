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

"""Plugin: re_tools - Functions to help reverse engineer an x86 file
"""

import os, tempfile, struct, capstone

from oxide.core import api
from oxide.core.libraries.re_lib import instruction_to_string, get_slice
from oxide.core.oshell import OxideShell, ShellSyntaxError

myshell = OxideShell()
current_file = None
default_height = 20
default_width = 8
""" Available colors are 'red', 'blue', 'green', 'cyan', 'magenta'
    Available effects are 'bold' and 'underline'
"""
def re_init(args, opts):
    """
        Initializes the RE plugin with a file to analyze
        Syntax: re_init %<oid> --height=<int> --width=<int>
                re_int | show # to display the current file
    """
    global current_file
    valid, invalid = api.valid_oids(args)
    oids = api.expand_oids(valid)

    if len(oids) == 0 and current_file:
        print("  - RE file set to %s %s" % (name(current_file), current_file))
        return [current_file]
    elif len(oids) == 0:
        raise ShellSyntaxError("The RE file is not set.")
    elif len(oids) > 1:
        raise ShellSyntaxError("The RE plugin only works with one file at a time.")

    current_file = oids[0]
    print("  - RE file set to %s %s" % (name(current_file), current_file))

    if "width" in opts:
        try:
            global default_width
            default_width = int(opts["width"])
            print("  - RE default width set to %d" % default_width)
        except ValueError:
            raise ShellSyntaxError("Invalid width")

    if "height" in opts:
        try:
            global default_height
            width = int(opts["height"])
            print("  - RE default height set to %d" % default_height)
        except ValueError:
            raise ShellSyntaxError("Invalid height")
    return [current_file]

def dos_stub(args, opts):
    """
        Disassembles the DOS header for PE files.
        Syntax: header <oid> ... [--verbose]
    """
    args, invalid = api.valid_oids(args)
    args = api.expand_oids(args)
    if not args:
        if current_file:
            args = [current_file]
        else:
            raise ShellSyntaxError("Must provide an oid")

    cap = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_16)
    for oid in args:
        src_type = api.get_field("src_type", oid, "type")
        if "PE" not in src_type:
            print(oid, " is not a PE file.")
            continue
        header = api.retrieve("pe", oid)
        if "dos_header" in header:
            if "dos_stub" in header["dos_header"]:
                stub = header["dos_header"]["dos_stub"]
                insns = cap.disasm(stub, 0)
                for n, i in enumerate(insns):
                    print(i)
                    if n == 6: break
                print(stub[14:])
        else:
            print("DOS stub not found.")

    return []

def header(args, opts):
    """
        Displays header info
        Syntax: header <oid> ... [--verbose]
    """
    args, invalid = api.valid_oids(args)
    args = api.expand_oids(args)
    if not args:
        if current_file:
            args = [current_file]
        else:
            raise ShellSyntaxError("Must provide an oid")
    headers = []

    for oid in args:
        src_type = api.get_field("src_type", oid, "type")
        if "PE" in src_type:
            pe_header(oid, opts)
        elif "ELF" in src_type:
            elf_header(oid, opts)
        elif "MACHO" in src_type:
            macho_header(oid, opts)
        elif "OSX Universal Binary" in src_type:
            osx_header(oid, opts)
        else:
            print("  - Source type %s is unsupported" % (src_type))

    return []


def sections(args, opts):
    """
        Displays sections
        Syntax: sections <oid> ... [--verbose]
    """
    args, invalid = api.valid_oids(args)
    args = api.expand_oids(args)
    if not args:
        if current_file:
            args = [current_file]
        else:
            raise ShellSyntaxError("Must provide an oid")

    for oid in args:
        header = api.get_field("object_header", [oid], oid)
        if not header:
            print("   <EMPTY HEADER>")
            print("  --------------------------")
            continue

        print(" - Sections for %s %s" % (name(oid), oid))
        print_sections(header, opts)


def import_table(args, opts):
    """
        Displays the import table
        Syntax: import_table <oid>
    """
    args, invalid = api.valid_oids(args)
    args = api.expand_oids(args)
    if not args:
        if current_file:
            args = [current_file]
        else:
            raise ShellSyntaxError("Must provide an oid")

    for oid in args:
        print("  - Import Table for %s %s " % (name(oid), oid))

        header = api.get_field("object_header", [oid], oid)
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


def ordinal_file_exists():
    return os.path.isfile(os.path.join(api.reference_dir, "ordinal_map"))


def entry_point(args, opts):
    """
        Displays the entry point
        Syntax: pe_header <oid> ...
    """
    args, invalid = api.valid_oids(args)
    args = api.expand_oids(args)
    if not args:
        if current_file:
            args = [current_file]
        else:
            raise ShellSyntaxError("Must provide an oid")

    for oid in args:
        bbs = api.get_field("basic_blocks", oid, oid)
        h = api.get_field("object_header", oid, oid)
        disasm = api.get_field("disassembly", oid, oid)
        if "instructions" in disasm: disasm = disasm["instructions"]
        entry = h.get_entry_points().pop()
        new_disasm = None
        if entry in bbs:
            offsets = bbs[entry]['members']
            new_disasm = {i:disasm[i] for i in offsets}
        if new_disasm:
            print("  Entry point disassembly for %s %s" % (name(oid), oid))
            print("  -------------------------------------")
            print_disassembly(oid, new_disasm, {}, {}, 0 , 0, default_height)
            print("  -------------------------------------")
        else:
            print("  %s could not be disassembled." % name(oid))
    return []


def disassembly(args, opts):
    """
        Displays the disassembly for a file
        Syntax: disassembly <oid> [--slice=<beg>:<end>]
    """
    args, invalid = api.valid_oids(args)
    args = api.expand_oids(args)
    if not args:
        if current_file:
            args = [current_file]
        else:
            raise ShellSyntaxError("Must provide an oid")

    start = stop = 0
    height = default_height
    if "slice" in opts:
        start, stop = get_slice(opts)

    if "height" in opts:
        try:
            width = int(opts["height"])
        except ValueError:
            raise ShellSyntaxError("Invalid height")
    mod_opts = {}
    if "module" in opts:
        mod_opts["module"] = opts["module"]
    for oid in args:
        disasm = api.get_field("disassembly", oid, oid, mod_opts)
        if "instructions" in disasm: disasm = disasm["instructions"]
        #comments = api.get_field("disassembly", [oid], "comments", mod_opts)
        functions = api.retrieve("function_extract", oid)
        if not functions:
            print("  No functions found for %s %s" % (name(oid), oid))
            continue
        fbreaks = get_fbreaks(functions)
        system_calls = api.get_field("map_calls", oid, "system_calls")
        internal_functions = api.get_field("map_calls", oid, "internal_functions")
        function_calls = dict()
        if system_calls is None:
            print("  System calls could not be determined for %s %s" % (name(oid), oid))
        else:
            function_calls.update(list(system_calls.items()))

        if internal_functions is None:
            print("  Internal functions could not be determined for %s %s" % (name(oid), oid))
        else:
            function_calls.update(list(internal_functions.items()))

        if disasm:
            print("  Disassembly for %s %s" % (name(oid), oid))
            print("  -------------------------------------")
            print_disassembly(oid, disasm, function_calls, fbreaks, start, stop, height)
            print("  -------------------------------------")
        else:
            print("  %s could not be disassembled." % name(oid))

def rva_offset(args, opts):
    """
        Convert from RVA to an offset
        Syntax: rva_offset <rva>
    """
    args, invalid = api.valid_oids(args)
    args = api.expand_oids(args)
    if not args:
        if current_file:
            args = [current_file]
        else:
            raise ShellSyntaxError("Must provide an oid or run re_init to set a file")

    oid = args[0]
    offsets = []
    for val in invalid:
        if val.startswith("0x"):
            try:
                rva = int(val, 16)
            except:
                raise ShellSyntaxError("Unrecognized address %s" % val)
        else:
            try:
                rva = int(val)
            except:
                raise ShellSyntaxError("Unrecognized address %s" % val)

        offset = convert_rva_offset(oid, rva)
        if offset is None:
            raise ShellSyntaxError("Unrecognized address %s" % val)

        offsets.append(offset)
        print(" %s (%s) : %s (%s)"%(hex(rva), rva, hex(offset), offset))
    return offsets

def strings(args, opts):
    """
        A variation on the typical Unix strings command. Looks for
        all sequences of 4 or more Asccii printable characters.
        Prints out the offsets followed by the matched string.
        Does not require that the strings end with a Null character,
        \\x00. The file option allows you to specify an output file
        that the strings will be written to.
        Returns None.
        Syntax: strings <oid_1> <oid_2> ... <oid_n> [--file=<outputfile>]
    """
    args, invalid = api.valid_oids(args)
    args = api.expand_oids(args)
    if not args:
        if current_file:
            args = [current_file]
        else:
            raise ShellSyntaxError("Must provide an oid or run re_init to set a file")
    for oid in args:
        strings = api.get_field("strings", oid, oid, opts)
        if not strings:
            print(" - No strings for", oid)
        else:
            print(" - Strings for", oid)

            write_file = False
            if "file" in opts:
                fd = open(opts["file"], "w")
                write_file = True
                print(" - Writting strings to file %s " % opts["file"])
            i = 0
            s = ""
            offsets = list(strings.keys())
            offsets.sort()
            for offset in offsets:
                if (offset - i) < 4:
                    s += strings[offset]
                else:
                    if len(s) > 1:
                        if write_file:
                            fd.write("Offset:%s\t%s\n" % (i, s))
                        else:
                            print("Offset:%s\t%s" % (i, s))
                    s = strings[offset]
                i = offset
        print()

def offset_rva(args, opts):
    """
        Convert from an offset to an RVA
        Syntax: rva_offset <offset>
    """
    args, invalid = api.valid_oids(args)
    args = api.expand_oids(args)
    if not args:
        if current_file:
            args = [current_file]
        else:
            raise ShellSyntaxError("Must provide an oid or run re_init to set a file")

    oid = args[0]
    rvas = []
    for val in invalid:
        if val.startswith("0x"):
            try:
                offset = int(val, 16)
            except:
                raise ShellSyntaxError("Unrecognized address %s" % val)
        else:
            try:
                offset = int(val)
            except:
                raise ShellSyntaxError("Unrecognized address %s" % val)

        rva = convert_offset_rva(oid, offset)
        if rva is None:
            raise ShellSyntaxError("Unrecognized address %s" % val)

        rvas.append(rva)
        print(" %s (%s) : %s (%s)"%(hex(offset), offset, hex(rva), rva))

    return rvas


def hex_dec(args, opts):
    """
        Convert hexadecimal value to decimal
        Syntax: hex_dec <hex number>
    """
    if not args:
        raise ShellSyntaxError("Cannot convert empty value.")
        return
    try:
        print("%s"%int(args[0], 16))
    except:
        raise ShellSyntaxError("Not able to convert %s to a decimal value. " % args[0])

def dec_hex(args, opts):
    """
        Convert decimal value to hexadecimal
        Syntax: dec_hex <decimal number>
    """
    if not args:
        raise ShellSyntaxError("Cannot convert empty value.")
        return
    try:
        print("%s"%hex(int(args[0])))
    except:
        raise ShellSyntaxError("Not able to convert %s to a hex value. " % args[0])

def get_val(args, opts):
    """
        Get the value of bytes at offset, interpreted as little-endian
                Requires a default file to have been set.
                Format values are:
                    c = 1 byte char
                    b = 1 byte signed
                    B = 1 byte unsigned
                    h = 2 bytes signed
                    H = 2 bytes unsigned
                    i = 4 bytes signed
                    I = 4 bytes unsigned
                    q = 8 bytes signed
                    Q = 8 bytes unsigned
                Each character may be preceeded by an number of occurances.
                For example 4h2b is equivalent to hhhhbb
        Syntax: get_val <offset> <format_string>
    """
    if len(args) != 2:
        raise ShellSyntaxError("offset and count required")
    offset = int(args[0])
    format = args[1]
    if not current_file:
        raise ShellSyntaxError("Must set default file using re_init")
    data = api.get_field("files", current_file, "data")
    if offset > len(data):
        raise ShellSyntaxError("Offset is beyond the end of the file")
    format = "=" + format
    size = struct.calcsize(format)
    output = struct.unpack(format, data[offset:offset+size])
    for n in output:
        print(n)


def hex_view(args, opts):
    """
        Print the hex values of a file and the disassebmly
        Syntax: hex_print %<oid> --slice=<start>:<stop> --width=<int> --height=<int> --less
                    [--module=[linear_disassembler]]
    """
    args, invalid = api.valid_oids(args)
    args = api.expand_oids(args)
    if not args:
        if current_file:
            args = [current_file]
        else:
            raise ShellSyntaxError("Must provide an oid or use re_init to set file.")

    oid = args[0]
    labels = []
    new_args = []
    mod_opts = {}
    if "module" in opts:
        mod_opts["module"] = opts["module"]
    if "interactive" in opts:
        mod_opts["interactive"] = opts["interactive"]

    disasm = api.get_field("disassembly", oid, oid, mod_opts)
    if "instructions" in disasm: disasm = disasm["instructions"]
    #comments = api.get_field("disassembly", [oid], "comments", mod_opts)
    #if comments:
    #    labels.append(comments)
    start = stop = 0
    width = default_width
    height = default_height

    if "slice" in opts:
        start, stop = get_slice(opts)

    if "width" in opts:
        try:
            width = int(opts["width"])
        except ValueError:
            raise ShellSyntaxError("Invalid width")

    if "height" in opts:
        try:
            height = int(opts["height"])
        except ValueError:
            raise ShellSyntaxError("Invalid height")

    less = False
    if "less" in opts:
        less = True

    heatoid = None
    if "heatmap" in opts:
        heatoid, invalid = api.valid_oids([opts["heatmap"]])
    for arg in args: # First separate lables from other items
        if isinstance(arg, dict) and "data" not in arg:
                labels.append(arg)
        else:
            new_args.append(arg)

    for arg in new_args:
        src = api.source(arg)
        if isinstance(arg, dict) and "data" in arg: # arg is the output of 'run files <oid>'
            print_hex_string(arg["data"], labels, disassm, heatoid, start, stop, width, height, less)
        elif isinstance(arg, str) and src and api.exists(src, arg): # oid was passed
            data = api.get_field(src, arg, "data")
            print_hex_string(data, labels, disassm, heatoid, start, stop, width, height, less)
        elif isinstance(arg, str):
            print_hex_string(arg, labels, disassm, heatoid, start, stop, width, height, less)
        else:
            print("  - Can't print arg %s" % arg)

'''def calls(args, opts):
    """
        Displays the function calls for a file
        Syntax: calls <oid> ...
    """
    args, invalid = api.valid_oids(args)
    args = api.expand_oids(args)
    if not args:
        if current_file:
            args = [current_file]
        else:
            raise ShellSyntaxError("Must provide an oid")

    for oid in args:

        internal_functions = api.get_field("map_calls", oid, "internal_functions")
        if not internal_functions:
            print("  No internal functions found for %s %s" % (name(oid), oid))
        else:
            names = list(set(internal_functions.values()))
            names.sort()
            print("  Internal functions calls for %s %s" % (name(oid), oid))
            print("  -------------------------------------")
            for f in names:
                print("  -",f)
            print("  -------------------------------------")

        system_calls = api.get_field("map_calls", oid, "system_calls")
        if not system_calls:
            print("  No system calls found for %s %s" % (name(oid), oid))
        else:
            names = list(set(system_calls.values()))
            names.sort()
            print("  System functions calls for %s %s" % (name(oid), oid))
            print("  -------------------------------------")
            for f in names:
                print("  -",f)
            print("  -------------------------------------")
'''

def parse_relocations(args, opts):
    if args:
        oid = args[0]
    elif current_file:
        oid = current_file
    else:
        raise ShellSyntaxError("Requires an OID.")
    src = api.source(oid)
    data = api.get_field(src, oid, "data", {})
    if not data:
        logger.debug("Not able to process%s",oid)
        return False
    src_type = api.get_field("src_type", oid, "type")
    if "ELF" in src_type:
        # Parse Elf
        header = api.retrieve("elf", oid)
        for relocation_section in header["relocations"]:
            print("")
            print("--------------------")
            print("SECTION NAME: " + relocation_section)
            print("--------------------")

            relocs = header["relocations"][relocation_section]["relocation_info"]
            for rel in relocs:
                print("Offset: "+ str(rel))
                print("RVA: " + str(relocs[rel]["rva"]))
                print("Info: " + str(relocs[rel]["info"]))
                print("Symbol Index: " + str(relocs[rel]["sym_index"]))
                print("Relocation Type: " + str(relocs[rel]["reloc_type"]))
                if "sym_val" in relocs[rel].keys():
                    print("Symbol Value: " + str(relocs[rel]["sym_val"]))
                if "sym_name" in relocs[rel].keys():
                    print("Symbol Name: " + str(relocs[rel]["sym_name"]))
                #print("Version: " + str(relocs[rel]["version"]))
                print()
    elif "PE" in src_type:
        # Parse PE
        header = api.retrieve("pe", oid)
        x = 1
        for i in header["relocations"]:
            print ("")
            print ("-----------")
            print ("Section #" + str(x))
            print ("-----------")
            print ("Page_RVA: ")
            print (i["page_rva"])
            print ("Block_Size: ")
            print (i["block_size"])
            print ("")
            print ("---Relocations---")
            for j in i["relocations"]:
                print("RVA Offset:")
                print(i["page_rva"] + j[1])
                print("Actual Offset:")
                print(j[1])
                print("Type:")
                print(j[0])
            x = x + 1
        else:
            print("Relocations only works for PE and ELF.")

exports = [re_init, header, entry_point, disassembly, rva_offset, offset_rva,
           hex_view, import_table, strings, dec_hex, hex_dec, get_val,
           sections, parse_relocations, dos_stub,
          ]

################## UTILITIES ###################################################
def print_sections(header, opts, indent=False):
    if hasattr(header, "num_embedded"):
        print(" - Embedded files: %s" % (header.num_embedded))
        for i, f in enumerate(header.embedded):
            #print " ---------------------------------------"
            print(" - Embedded sections for file: %s " % (i+1))
            print_sections(f, opts, indent=True)
            print(" ---------------------------------------")
        return

    tab = ""
    if indent:
        tab = "\t"

    print("%s  --------------------------" % (tab))
    print("%s  - Number of Sections: %s  " % (tab, len(header.section_info)))

    if "verbose" in opts:
        secs = header.section_info
        offsets = [secs[s]["section_offset"] for s in secs]
        offsets.sort()
        for o in offsets:
            for s in secs:
                if secs[s]['section_offset'] == o:
                    print("%s    - Section %s           "      % (tab, str(s)))
                    print("%s      - Exec?            %s"      % (tab, str(secs[s]['section_exec'])))
                    print("%s      - Start offset:    %s (%s)" % (tab, hex(secs[s]['section_offset']), secs[s]['section_offset']))
                    print("%s      - Start RVA:       %s (%s)" % (tab, hex(secs[s]['section_addr']), secs[s]['section_addr']))
                    print("%s      - Section Length:  %s (%s)" % (tab, hex(secs[s]['section_len']), secs[s]['section_len']))
    else:
        header.section_names.sort()
        print("%s  - Sections: %s" %  (tab, ", ".join([str(s) for s in header.section_names])))


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


def osx_header(oid, opts):
    header = api.get_field("object_header", oid, oid)
    src = api.source(oid)
    file_size = api.get_field("file_meta", oid, "size")
    names = api.get_names_from_oid(oid)
    print("  OSX Universal Header for %s %s" % (name(oid), oid))
    if not header:
        print("   <EMPTY>")
        print("  --------------------------")
        return

    print("  - File Size:      %s" % (file_size))
    print("  - Magic:          %s" % (header.magic))
    print("  - Big Endian:     %s" % (header.big_endian))
    print("  - Embedded Files: %s" % (header.num_embedded))
    for header in header.embedded:
        print("  -------------------------------------")
        print_macho_header(header, oid, opts, embedded=True)
        print("  -------------------------------------")
        print()

def macho_header(oid, opts):
    header = api.get_field("object_header", oid, oid)
    print_macho_header(header, oid, opts)


def print_macho_header(header, oid, opts, embedded=False):
    src = api.source(oid)
    file_size = api.get_field("file_meta", oid, "size")
    names = api.get_names_from_oid(oid)

    indent = False
    tab = ""
    if embedded:
        indent = True
        tab = "\t"

    if embedded:
        print("%s  Embedded Macho-O Header for %s %s" % (tab, name(oid), oid))
    else:
        print("  Macho-O Header for %s %s" % (name(oid), oid))

    if not header:
        print("   <EMPTY>")
        print("  --------------------------")
        return

    entry_string = ""
    for e in header.get_entry_points():
        entry_string += "%s (%s)  " % (hex(e), (e))

    print("%s  - File Size:    %s" % (tab, file_size)) # FIXME get embedded file size
    print("%s  - Addr Size:    %s" % (tab, header.insn_mode))
    print("%s  - Magic:        %s" % (tab, header.magic))
    print("%s  - Big Endian:   %s" % (tab, header.big_endian))
    print("%s  - Machine:      %s" % (tab, header.machine))
    print("%s  - UUID:         %s" % (tab, header.uuid))
    print("%s  - Entry points: %s"   % (tab, entry_string))
    print_sections(header, opts, indent)
    macho_import_table(header, opts)


def elf_header(oid, opts):
    header = api.get_field("object_header", oid, oid)
    src = api.source(oid)
    file_size = api.get_field("file_meta", oid, "size")
    names = api.get_names_from_oid(oid)
    print("  ELF Header for %s %s" % (name(oid), oid))

    if not header:
        print("   <EMPTY>")
        print("  --------------------------")
        return

    addr_size = "32 bit"
    if header.is_64bit():
        addr_size = "64 bit"

    entry_string = ""
    for e in header.get_entry_points():
        entry_string += "%s (%s)  " % (hex(e), (e))

    print("  - File Size:    %s"      % (file_size))
    print("  - Addr Size:    %s"      % (addr_size))
    print("  - Image Base:   %s (%s)" % (hex(header.image_base), header.image_base))
    print("  - Image Size:   %s "     % (header.image_size))
    print("  - Code Size:    %s "     % (header.code_size))
    print("  - Code Base:    %s (%s)" % (hex(header.code_base), header.code_base))
    print("  - Machine:      %s"      % (header.machine))
    print("  - OS Version:   %s"      % (header.os_version))
    print("  - Entry points: %s"      % (entry_string))
    print_sections(header, opts)
    elf_import_table(header, opts)


def pe_header(oid, opts):
    header = api.get_field("object_header", oid, oid)
    src = api.source(oid)
    file_size = api.get_field("file_meta", oid, "size")
    names = api.get_names_from_oid(oid)
    print("  PE Header for %s %s" % (name(oid), oid))

    if not header:
        print("   <EMPTY>")
        print("  --------------------------")
        return

    addr_size = "32 bit"
    if header.is_64bit():
        addr_size = "64 bit"

    entry_string = ""
    for e in header.get_entry_points():
        entry_string += "%s (%s)  " % (hex(e), (e))

    print("  - File Size:      %s"      % (file_size))
    print("  - Addr Size:      %s"      % (addr_size))
    print("  - Image Base:     %s (%s)" % (hex(header.image_base), header.image_base))
    print("  - Image Size:     %s "     % (header.image_size))
    print("  - Code Size:      %s "     % (header.code_size))
    print("  - Code Base:      %s (%s)" % (hex(header.code_base), header.code_base))
    print("  - Data Base:      %s (%s)" % (hex(header.data_base), header.data_base))
    print("  - File Alignment: %s"      % (header.file_alignment))
    print("  - Image Version:  %s"      % (header.image_version))
    print("  - Linker Version: %s"      % (header.linker_version))
    print("  - OS Version:     %s"      % (header.os_version))
    print("  - Entry points:   %s"      % (entry_string))

    print_sections(header, opts)
    pe_import_table(header, opts)


def print_internal_functions(names):
    oid = current_file
    functions = api.retrieve("function_extract", oid)
    if functions:
        fbreaks = get_fbreaks(functions)
        name_to_offset = {}
        for offset in functions:
            name_to_offset[functions[offset]["name"]] = offset

    system_calls = api.get_field("map_calls", oid, "system_calls")
    internal_functions = api.get_field("map_calls", oid, "internal_functions")
    if not system_calls:
        print("  No system calls found for %s %s" % (name(oid), oid))

    if not internal_functions:
        print("  No internal functions found for %s %s" % (name(oid), oid))

    function_calls = dict( list(system_calls.items()) + list(internal_functions.items()))
    for fn in names:
        if fn not in name_to_offset:
            print(" %s not a function in %s %s" % (fn, name(oid), oid))
            continue

        print(" Function %s for %s %s" % (fn, name(oid), oid))
        print("  -------------------------------------")
        print_disassembly(oid, functions[name_to_offset[fn]]['instructions'], function_calls, fbreaks, start=0, stop=0, height=32)
        print("  -------------------------------------")


def name(oid):
    if api.exists("file_meta", oid):
        return api.get_field("file_meta", oid, "names").pop()
    elif api.exists("collections_meta", oid):
        return api.get_colname_from_oid(oid)
    return None


def convert_rva_offset(oid, rva):
    header = api.get_field("object_header", oid, oid)
    if isinstance(rva, str) and rva.startswith("0x"):
        try:
            rva = int(rva, 16)
        except:
            raise ShellSyntaxError("Unrecognized address %s" % rva)
    else:
        try:
            rva = int(rva)
        except:
            raise ShellSyntaxError("Unrecognized address %s" % rva)
    return header.get_offset(rva)


def convert_offset_rva(oid, offset):
    header = api.get_field("object_header", oid, oid)
    if isinstance(offset, str) and offset.startswith("0x"):
        try:
            offset = int(offset, 16)
        except:
            raise ShellSyntaxError("Unrecognized address %s" % rva)
    else:
        try:
            offset = int(offset)
        except:
            raise ShellSyntaxError("Unrecognized address %s" % offset)
    return header.get_rva(offset)


def get_fbreaks(funcs):
    fbreaks = {}
    fstarts = {}
    fends = {}
    for f in funcs:
        if not funcs[f]["start"]: continue
        fstarts[funcs[f]["start"]] = "Begin internal_function_" + str(funcs[f]["start"])
    #    fends[funcs[f]["end"]] = "End internal_function_" + str(funcs[f]["start"])
    #for e in fends:
    #    fbreaks[e] = [fends[e]]
    for s in fstarts:
        if s in fbreaks:
            fbreaks[s].append(fstarts[s])
        else:
            fbreaks[s] = [fstarts[s]]
    return fbreaks

def print_disassembly(oid, disasm, comments, f_breaks, start, stop, height=default_height):
    if not disasm:
        return
    if isinstance(disasm, dict):
        keys = list(disasm.keys())
        keys.sort()
        h=1
        if not stop:
            stop = disasm[keys[-1]]["address"]
        for k in keys:
            addr = disasm[k]["address"]
            if addr < start or addr > stop:
                continue

            if addr in f_breaks:
                for m in f_breaks[addr]:
                    print("******** ", m, " ********")

            print(hex(addr), " :  ", instruction_to_string(disasm[k]), end=' ')
            if comments and k in comments:
                print("  :  ", comments[k])
            else:
                print()

            if not h % height: # Only show <height> lines at a time
                if input().strip().lower().startswith("q"):
                    break
            h+=1

    elif isinstance(disasm, list):
        h = 1
        for insn in disasm:
            addr = insn["address"]
            offset = convert_rva_offset(oid, addr)
            if (not stop or ( addr >= start and addr <= stop)) and insn:
                print(hex(addr), " :  ", instruction_to_string(insn), end=' ')
                if comments and offset in comments:
                    print("  :  ", comments[offset])
                else:
                    print()
            if not h % height: # Only show <height> lines at a time
                if input().strip().lower().startswith("q"):
                    break
            h+=1


def print_hex_string(s, labels, disassm, heatoid, start, stop, width=default_width, height=default_height, less=False):
    y = start
    h = y + height
    n = y + 1
    ls = "" # Used for less
    line = ""
    heatmap = None
    if heatoid:
        heatmap = get_heatmap(s, heatoid)
        print("Using heatmap = ", heatoid)
    if not stop:
        stop = len(s)
    for c in s[start:stop]:
        if not (n-1) % width:
            ls += str(y).ljust(width)
        if not heatmap:
            ls += str(hex(ord(c))).replace("0x","").rjust(2,"0") + " "
            line += myshell.colorize(str(hex(ord(c))).replace("0x","").rjust(2,"0"), "red") + " "
        else:
            if heatmap[n] < 1:
                line += str(hex(ord(c))).replace("0x","").rjust(2,"0") + " "
            elif heatmap[n] < 2:
                line += myshell.colorize(str(hex(ord(c))).replace("0x","").rjust(2,"0"), "red") + " "
            elif heatmap[n] < 50:
                line += myshell.colorize(str(hex(ord(c))).replace("0x","").rjust(2,"0"), "green") + " "
            else:
                line += myshell.colorize(str(hex(ord(c))).replace("0x","").rjust(2,"0"), "blue") + " "

        if not (n) % width:
            line += " |  "
            ls += " | "
            for i in s[y:n]:
                if ord(i) >= 32 and ord(i) <= 126: # Check for printable char
                    line += i
                    ls += i
                else:
                    line += "."
                    ls += "."

            line += add_labels(y, n, labels, disassm, color=True)
            ls += add_labels(y, n, labels, disassm, color=False)
            ls += "\n"
            if not less:
                print(myshell.colorize(str(y).ljust(width), "green"), line)

            h+=1
            if not less and not (h) % height: # Only show <height> lines at a time
                if input().strip().lower().startswith("q"):
                    break

            line = ""
            y=n
        n+=1

    if y+1!=n: # Fixup the last line
        line+= " "*(width-(n-y-1))*3 + " |  "
        line+= "".join([i for i in s[y:n]])
        ls += " "*(width-(n-y-1))*3 + " |  "
        ls += "".join([i for i in s[y:n]])
        line += add_labels(y, n, labels, disassm, color=True)
        ls += add_labels(y, n, labels, disassm, color=False)

    if less:
        tf = tmp_file(ls)
        os.system("less " + tf )
        os.remove(tf)
    else:
        print(str(y).ljust(8), line)
        print()

def get_heatmap(s, heatoid):
    n = 3
    histo = api.retrieve("byte_ngrams", heatoid, {"n":n})
    heatmap = [0]*len(s)
    for i in range(len(s)-n):
        gram = s[i]
        for j in range(1,n):
            gram += ","+s[i+j]
        if gram in histo:
            heatmap[i] = histo[gram]
    return heatmap


def add_labels(y, n, labels, disassm, color=False):
    l = []
    s = ""
    if disassm:
        for i in range(y,n):
            if i in disassm:
                l.append(instruction_to_string(disassm[i]))
        if l and color:
            s = " | " + myshell.colorize(" : ".join(l), "magenta")
        elif l:
            s = " | " + " : ".join(l)

    l = []
    for label in labels: # List of dictionaries
        l.extend([l.append(label[i]) for i in range(y,n) if i in labels])

    if l:
        s += " # " + ", ".join(l)

    return s

def tmp_file(data):
    fname = tempfile.mktemp(suffix='.txt', prefix='re_tmp_', dir=api.scratch_dir)
    fd = file(fname, 'w')
    fd.write(data)
    fd.close()
    return fname
