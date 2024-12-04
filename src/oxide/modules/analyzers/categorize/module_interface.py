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

DESC = ""
NAME = "categorize"

# imports
import logging

from typing import Dict, Any, List
import os

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    """ Documentation for this module
        private - Whether module shows up in help
        set - Whether this module accepts collections
        atomic - TBD
    """
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True}


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """ Entry point for analyzers, these do not store in database
        these are meant to be very quickly computed things passed along
        into other modules
    """
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        category = None
        src_type = api.get_field("src_type", oid, "type").pop()
        file_name = api.get_field("file_meta", oid, "names").pop()
        file_extension = os.path.splitext(file_name)[1][1:]

        
        if 'ELF' in src_type or "PE" in src_type or "MACHO" in src_type or ('ZIP' in src_type and '.jar' in file_extension):
            category = "executable"    

        if 'ZIP' in src_type or "GZIP" in src_type or "TAR" in src_type or "BZ2" in src_type:
            category = "archive"

        if ('PNG' in src_type or "JPG" in src_type or "GIF" in src_type or "MP3" in src_type or
            'TIFF' in src_type or "BMP" in src_type or "WAV" in src_type or
            "OGG" in src_type):
            category = "media"

        if ".crt" in file_extension:
            category = "certificate"

        if 'PDF' in src_type:
            category = "documentation"

        if 'TTF' in src_type or 'XML' in src_type:
            category = "resource"
        
        if 'Script' in src_type:
            category = "source"

        # TEXT FILES, BASED ON FILE EXTENSION ONLY
        if (".c" == file_extension or ".cpp" == file_extension or ".cxx" == file_extension or ".java" == file_extension or ".rs" == file_extension or
            ".go" == file_extension):
            category = "source"


        results[oid] = category

    return results
