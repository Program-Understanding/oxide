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

""" ghidra_utils.py

Shared functions for remapping virtual addresses to offsets, shared between all ghidra modules
"""


def get_file_offset(vaddr: int, header_interface, load_addr: int, offsets_off: bool = False) -> int:
    """ Using object file, convert virtual address to file offset
    """
    if offsets_off is True:
        return vaddr

    # return header_interface.get_offset(vaddr, LOAD_ADDR)
    if header_interface.type == "PE":
        res = header_interface.get_offset(vaddr, load_addr)
    elif header_interface.type == "MACHO":
        res = header_interface.get_offset(vaddr, load_addr)
    elif header_interface.type == "ELF":
        if header_interface.etype != "Shared object file":
            # non-PIE, so use header info
            res = header_interface.get_offset(vaddr, load_addr)
        else:
            # If shared object, rebase off 32 or 64 bit
            if header_interface.is_64bit() is True:
                load_addr = 0x100000
            else:
                load_addr = 0x10000
            res = vaddr - load_addr

    if not res:
        res = vaddr - load_addr
    return res
