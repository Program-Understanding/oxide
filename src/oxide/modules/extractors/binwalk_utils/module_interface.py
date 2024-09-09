"""
Copyright 2023 National Technology & Engineering Solutions
of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS,
the U.S. Government retains certain rights in this software.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the SoftwareF is
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

DESC = " This Module provides access to binwalk functions"
NAME = "binwalk_utils"
CATEGORY = ""

# NOTE: Binwalk has a lot of issues on newer versions of python. I had a solution where I edited the source code.
# Ill provide that soon. DM me if you want it.
import logging


from typing import Dict, Any
from oxide.core import api
import binwalk as bwalk
from pathlib import *
from unblob import unblob
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY}

def process(oid:str, opts:dict) -> bool:
    logger.debug("process()")
    results = {}
    data = api.get_field(api.source(oid), oid, "data", {}) 
    file_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(file_name, data) 
    # print(str(file_path))

    scan_results = {}
    scan_results["signature"], scan_results["entropy"]= bwalk.scan(f_name,signature=True, entropy=True, do_plot=False, quiet=True)
    for module in scan_results["signature"].results:
        pass
    results["signature"] = {module.offset: module.description for module in scan_results["signature"].results}
    results["entropy"] = {module.offset: module.entropy for module in scan_results["entropy"].results}
    if results is None: return False
    api.store(NAME, oid, results, opts)
    return True

