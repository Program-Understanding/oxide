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

desc = " Produce opcode ngrams"
NAME = "opcode_ngrams"
USG = "This module returns a dictionary containing the produced opcode n-grams from a binary file. The dictionary it returns has a string \
that represents an n-gram sequence of opcodes as the key, and the frequency counts of the n-grams serve as the corresponding values in the \
dictionary."

import logging
import api
from histogram import build_ngrams, merge_histo
from collections import defaultdict
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"n":{"type":int, "mangle":True, "default":3}}

def documentation():
    return {"description":desc, "opts_doc":opts_doc, "set":False, "atomic":True}

def mapper(oid, opts, jobid=False):
    logger.debug("mapper()")

    src = api.source(oid)
    if api.documentation(src)["set"]:
        return None
    if api.exists(NAME, oid, opts):
        return oid
    opcodes = api.get_field("opcodes", oid, "opcodes")
    if not opcodes: return None
    out_histo = build_ngrams(opcodes, opts["n"])
    api.store(NAME, oid, out_histo, opts)
    return oid

def reducer(intermediate_output, opts, jobid):
    logger.debug("reducer()")
    out_histo = defaultdict(int)
    for oid in intermediate_output:
        if oid:
            histo = api.retrieve(NAME, oid, opts)
            out_histo = merge_histo(histo, out_histo)
            if oid == jobid:
                return out_histo
    api.store(NAME, jobid, out_histo, opts)
    return out_histo
