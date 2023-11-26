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

DESC = "this module will look at a binary and see what percentage of the binary has been analyzed and what is known about it. Ouputs a coverage.json containing module-specific and overall coverage including padding"
NAME = "bin_coverage"

import logging
import api
import organized_dicts

from typing import Dict, Any

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False, "atomic": True}


def process(oid: str, opts: Dict[str, Any]) -> dict:
    """ 1. Run ghidra first, see what we have and organize it.
	    2. add other modules output to data structure see if there is overlap and correct
	    3. if conflict on overlap then manually do examination on those bytes.
	    4. organize what we have and what we dont have into data structures (darkzone and overlap)
	        * these structures will be organized in both individual bytes as well as groups of
              bytes referring to the same set of data
	    5. once all modules are accounted for we can then make new modules that will parse the
           rest of the binary to get better coverage

        The number we are shooting for it 100%, but obviously this will be hard to do and we wont
        have all infor for all binaries but that will be fine because we can update with the git
        issues.
    """
    modules = {}

    #Get binary data
    src_type = api.get_field("src_type", oid, "type")
    src = api.source(oid)
    modules["data"] = api.get_field(src, oid, "data", {})

    #Get module object
    modules["bin_size"] = api.get_field("file_meta",oid,"size")
    modules["pe"] = api.retrieve("pe", oid)
    modules["elf"] = api.retrieve("elf", oid)
    modules["disasm"] = api.get_field("disassembly", oid, oid)
    modules["ghidra_data"] = api.retrieve("ghidra_data", oid)

    #Modules to be added once working
    modules["dwarf_info"] = None
    modules["rtti"] = None

    # Contiguous regions of null bytes
    modules["padding"] = api.retrieve("padding", oid)

    modules["oid"] = oid

    #Gets organized_dicts' module_organizer object and calls the assemble function which gets binary coverage and outputs it to a json file coverage.json
    return organized_dicts.assemble(modules)
