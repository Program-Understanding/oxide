DESC = " Makes a file into an image for analysis in machine learning"
NAME = "binwalk_entropy"
USG = " This module takes a collection of binary files and extracts from \
ghidra_disasm the instructions. Opcode from each instruction is used for \
each channel in the image. It stores the image in a numpy array \
returned in a dictionary. The dictionary has the original and resized\
image, where user can set resized image's size"

import binwalk
from binwalk.modules import signature as bw_signature, entropy as bw_entropy
import re
from statistics import median, mean
import logging
from oxide.core import api
from typing import Callable, Union, TypedDict, Optional, List, Dict, Any, Tuple
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"size":{"type": int, "mangle":False,"default":1000,"description":"Size of the generated image. Interpreted as size x size, in order to keep uniformity for use with neural network"},"show":{"type":bool,"mangle":False,"default":False,"description":"Show the generated binary image"}}

def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage":USG}

def process(oid, opts):
    result = {}
    original_path = api.retrieve("original_path", oid)

    path = original_path[oid].pop()

    result = entropy(path)

    api.store(NAME, oid, result, opts)
    return True

def entropy(path):
    results = {}
    results['numbers'] = None
    results['median'] = None
    results['mean'] = None

    scan_result = binwalk.scan(str(path), entropy=True, quiet=True, nplot=True)
    assert len(scan_result) == 1, f"Binwalk scan returned results for {len(scan_result)} instead of 1 module."
    entropy, *_ = scan_result

    numbers = [float(re.sub('[)(]', '', x.description.split()[-1])) for x in entropy.results]

    if numbers:
        results['numbers'] = numbers
        results['median'] = median(numbers)
        results['mean'] = mean(numbers)

    return results


