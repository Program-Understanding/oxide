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

""" Objdump processing script for instructions, largely just reference for linear dis
"""
import subprocess
import platform
import logging
import time

name = "objdump"
logger = logging.getLogger(name)
if platform.system() == "Darwin":
    objdump_cmd = "gobjdump"
else:
    objdump_cmd = "objdump"

# ------------------------------- Tool 1: Objdump -----------------------------------


def get_objdump_offsets(header_interface):
    pass


def _scribe_version(output_map):
    for _iter in output_map:
        output_map[_iter]["meta"] = {}
        output_map[_iter]["meta"]["tool_ver"] = "v2.3.0"
        output_map[_iter]["meta"]["name"] = "Objdump"


def _objdump_record_inst_offsets(dasm_line, output_map, header_interface):
    """ add processed objdump line to list of instructions, limited to LINUX objdump implementation
            This may be version of objdump related, but observed mismatch when DARWIN objdump used
        Input -
            dasm_line (String) - Ascii representation of instruction
            inst_to_save (List of tuples) - current set of instructions iteratively added to
    """
    # Convert virtual address to artifact offset and saves bytes and save to output file
    dasm_list = dasm_line.split("\t")

    # invalid instruction line
    if len(dasm_list) < 2:
        return

    # Remove bytes
    del dasm_list[1]

    # Get address by stripping off ':'
    inst_addr = dasm_list[0][:-1].strip()

    if header_interface.type == "ELF":
        if header_interface.etype == "Shared object file":
            # If shared object, rebase off 32 or 64 bit
            if header_interface.is_64bit() is True:
                load_addr = 0
            else:
                load_addr = 0
            dasm_list[0] = int(inst_addr, 16) - load_addr
        else:
            # non-PIE, so use header info
            dasm_list[0] = header_interface.get_offset(int(inst_addr, 16))
    elif header_interface.type == "MACHO":
        load_addr = 0x100000000
        dasm_list[0] = int(inst_addr, 16) - load_addr
    elif header_interface.type == "PE":
        dasm_list[0] = header_interface.get_offset(int(inst_addr, 16))

    # clean up assembly line
    if (len(dasm_list) > 1):
        dasm_list[1] = dasm_list[1].replace("        ", " ")
    else:
        return

    output_map["instructions"][dasm_list[0]] = " ".join(dasm_list[1:])

# -------------------------------- ELF Processing ------------------------------------


def _objdump_disassembly(file_test):
    """ processes a exectuable with objdump, and disassembles code
        input -
                file_test (filename)- exectuable x86,64 parsable with objdump
        output -f
                exec_sections (string)- plaintext of disassembly from objdump
    """
    # Output objdump only look at executable sections
    cmd = [objdump_cmd, "-d", file_test]

    # Determine if objdump returns valid output or error code 1
    try:
        objref = subprocess.check_output(cmd, universal_newlines=True, stderr=subprocess.STDOUT)
    except subprocess.CalledProcessError:
        return None

    return objref


def _objdump_executable_sections(file_test):
    """ processes a exectuable with objdump, and parses exectuable sections
        input -
                file_test (filename)- exectuable x86,64 parsable with objdump
        output -
                exec_sections (list)- list of section names that are executable
    """
    # initialize list of sections
    exec_sections = []

    # Process file headers using objdump to find exectuable sections
    cmd = [objdump_cmd, "-h", file_test]
    obj_sections = subprocess.check_output(cmd, universal_newlines=True)
    section_lines = obj_sections.split("\n")

    # start header parsing after column description
    section_index = 3

    while section_index < (len(section_lines)-1):
            section_header = section_lines[section_index].split()
            section_permission = section_lines[section_index+1].split()
            if "CODE" in section_permission:
                    exec_sections.append(section_header[1])
            section_index += 2
    return exec_sections


def _objdump_noncompiler_sections(header_output):
    """ takes -h output from objdump, and parses for exectuable sections from code
        input -
            header_output (string) - string of -h output
        output -
            sections_of_interest (list) - list of headers not generated automatically by compiler
    """
    sections_of_interest = []
    for section in header_output:
            if section in [".init", ".plt", ".plt.got", ".fini"]:
                    continue
            else:
                    sections_of_interest.append(section)
    return sections_of_interest


def _objdump_funcs_of_interest(dasm_line, fn):
    """ Enumerate list of functions that are linker related, specific to GCC currently
            Any function not in linker function deemed of interest
    """
    compiler_funcs = []
    compiler_funcs.append("__libc_csu_init:")
    compiler_funcs.append("__libc_csu_fini:")
    compiler_funcs.append("frame_dummy:")
    compiler_funcs.append("__do_global_dtors_aux:")
    compiler_funcs.append("register_tm_clones:")
    compiler_funcs.append("deregister_tm_clones:")
    compiler_funcs.append("_start:")

    dasm_list = dasm_line.split(" ")
    function_name = dasm_list[1].replace("<", "").replace(">", "")
    if function_name not in compiler_funcs:
            # Prepare function for .S comparison
            # print("\t.globl %s" % (function_name[:-1]), file=fn)
            # print("\t.type    %s, @function" % (function_name[:-1]), file=fn)
            # print(function_name, file=fn)
            return True
    else:
            return False


def _objdump_parse_dasm(dasm_output, header_interface, output_map):
    """ takes objdump and parses for non-compiler functions and sections
        intput -
                dasm_output (string) - Output from objdump -d
                sections_of_inaterest (list) - sections that are exectuable from objdump
                    not automatically generated by gcc
                fn (file descriptor) - file to output asm to
        output -
                    (list) - list of disassembly of non-compiler functions
    """
    exec_section = True #False

    dasm_lines = dasm_output.split("\n")

    for dasm_line in dasm_lines:
        if dasm_line != "":
            # sections begin with Dissassembly of section <>
            if dasm_line[0:11] == "Disassembly":
                dasm_list = dasm_line.split(" ")
                section_name = dasm_list[3][:-1]

                # determine if section is executable, use relative location since linear sweep
                #exec_section = section_name in header_interface.section_info
            elif ("..." in dasm_line):
                pass
                # FIXME: Must debug where this comes from
                # print("Ignore '...'")
            # function begins with address/offset
            elif (dasm_line[0] != " " and exec_section is True):
                if len(dasm_line.split(' ')) == 2:
                    addr, name = dasm_line.split(' ')
                    output_map["functions"][header_interface.get_offset(int(addr, 16))] = {"name": name, "vaddr": addr, "blocks": ["Unknown"]}
            # code begins with space/tab
            elif (dasm_line[0] == " " and exec_section is True):
                _objdump_record_inst_offsets(dasm_line, output_map, header_interface)
            # Null lines
            else:
                if dasm_lines.index(dasm_line) <= 1:
                    continue
                pass
    return output_map

# ----------------------------- MACHO Processing -------------------------------------


def _objdump_disassembly_from_file(file_path: str) -> str:
    """ processes a exectuable with objdump, and disassembles code from objdump output > objd.out
        input -
                file_path (filename)- Text output of objdump on sample file
        output -
                exec_sections (string)- plaintext of disassembly from objdump
    """
    # Output objdump only look at executable sections
    try:
        objref = open(file_path, "r").read()
    except FileNotFoundError:
        return None
    return objref


def _objdump_parse_machoinst(dasm_output, output_map):
    """ takes objdump and parses instructions to record
        intput -
                dasm_output (string) - Output from objdump -d
                fn (file descriptor) - file to output asm to
        output -
                    (list) - list of disassembly of non-compiler functions
    """
    dasm_lines = dasm_output.split("\n")
    for dasm_line in dasm_lines:
        if dasm_line != "":
            # code begins with an offset
            colon_index = dasm_line.index(":")
            try:
                int(dasm_line[:colon_index], 16)
                # Define objdump macho load offset
                _objdump_record_inst_offsets(dasm_line, output_map, header_interface)
            except Exception:
                continue


def _objdump_parse_peinst(dasm_output, header_interface, output_map):
    """ takes objdump and parses instructions to record
        intput -
                dasm_output (string) - Output from objdump -d
                fn (file descriptor) - file to output asm to
        output -
                    (list) - list of disassembly of non-compiler functions
    """
    dasm_lines = dasm_output.split("\n")

    for dasm_line in dasm_lines:
        if dasm_line != "" and not (":" in dasm_line):
            if "..." in dasm_line:
                # Unknown what this means
                continue
            logger.info(dasm_line)
            # Offsets are followed by Colon
            colon_index = dasm_line.index(":")
            try:
                # Calculate offset of instruction to write to output map
                virtual_addr = int(dasm_line[:colon_index], 16)

                _objdump_record_inst_offsets(dasm_line, output_map, header_interface)
            except Exception:
                continue


def extract(file_test, header_interface):
    # Define Header interface

    output_map = {}
    output_map["meta"] = {}
    output_map["instructions"] = {}
    output_map["original_blocks"] = {}
    output_map["canon_blocks"] = {}
    output_map["functions"] = {}

    _scribe_version(output_map)

    start = time.time()

    # If running linux, look for objdump file and process this
    """ To get Objdump results, 3 primary cases:
            1) Running oxide in linux, on a mach-o file
                (must parse a objdump result file that was run in macho/osx)
            2) Analyzing a PE file (from OS-X or Linux)
                parse file with specific output format (this may not be tested for macho)
            3) Running oxide in Linux and analyzing an ELF file
                parse file with specific output format
    """
    if (platform.system() == "Linux") and header_interface.type == "MACHO":
        # Workflow to read objd.out file from macho_objdump
        objdout_file = file_test[:file_test.rindex("/") + 1] + "objd.out"
        objd_dasm = _objdump_disassembly_from_file(objdout_file)

        # If objdump file doesn't exist, do not populate instructions
        if objd_dasm is None:
            return None

        # Populate output map
        _objdump_parse_machoinst(objd_dasm, output_map)
    elif (platform.system() == "Linux" or platform.system() == "Darwin") and header_interface.type == "PE":
        logger.info("Detected PE being analyzed from Linux or Darwin Host -  %s" % file_test)

        # Run Objdump on sample
        objd_dasm = _objdump_disassembly(file_test)

        if objd_dasm is None:
            logger.error("Objdump returned an error, excluding objdump")
            return None

        _objdump_parse_peinst(objd_dasm, header_interface, output_map)
    else:
        # Run Objdump on sample
        objd_dasm = _objdump_disassembly(file_test)

        # Populate output map
        _objdump_parse_dasm(objd_dasm, header_interface, output_map)

    end = time.time()
    output_map["meta"]["time"] = end - start

    # Initialize canonical blocks
    #canonize_blocks(output_map)

    return output_map
