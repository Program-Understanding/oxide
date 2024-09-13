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

DESC = "binviz"
NAME = "binary_visualizer"
USG = "binviz"
import logging
from typing import Dict, Any, List

import numpy as np
import matplotlib.pyplot as plt
import os
import json


from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "Usage": USG}

def visualize_binary(data: bytes):
    byte_array = np.frombuffer(data, dtype=np.uint8)
    
    side_length = int(np.ceil(np.sqrt(len(byte_array))))
    
    padded_array = np.pad(byte_array, (0, side_length**2 - len(byte_array)), mode='constant')
    
    grid = padded_array.reshape((side_length, side_length)).tolist()
    
    return json.dumps(grid)


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}

    for oid in oid_list:
        src = api.source(oid)
        data = api.get_field(src, oid, "data")
        if data:
            results[oid] = visualize_binary(data)
        else:
            results[oid] = {"status": "no data"}
        
    return results
