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

DESC = " This module calculates the entropy over chunks of a file"
NAME = "entropy_graph"
USG = "The module calculates entropy, the overall entropy, the maximum entropy, and the address of the maximum entropy in a file. The module returns a dictionary containing the entropy values, the addresses, the block size, the overall entropy, the maximum entropy, and the address of the maximum entropy."

import logging

from typing import Dict, Any, List

import numpy as np
from scipy.stats import entropy
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator
from io import BytesIO

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")
chunk_size = 1024

opts_doc = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": True,
            "atomic": True, "usage": USG}

def calculate_entropy(data):
    if len(data) == 0:
        return 0
    counts = np.unique(list(data), return_counts=True)[1]
    ent = entropy(counts, base=2)
    max_ent = np.log2(len(data))
    normalized_ent = ent / max_ent if max_ent > 0 else 0
    return normalized_ent

def read_file_in_chunks(byte_stream, chunk_size):
    while chunk := byte_stream.read(chunk_size):
        yield chunk

def plot_entropy(data, chunk_size):
    entropies = []
    addresses = []
    chunk_number = 0
    for chunk in read_file_in_chunks(data, chunk_size):
        chunk_entropy = calculate_entropy(chunk)
        entropies.append(round(chunk_entropy, 5))
        addresses.append(chunk_number * chunk_size)
        chunk_number += 1

    overall_entropy = np.average(entropies)
    max_entropy = max(entropies)
    max_entropy_address = addresses[entropies.index(max_entropy)]

    return overall_entropy, max_entropy, max_entropy_address, entropies, addresses

def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        data = api.get_field(api.source(oid), oid, "data")
        bytes_data = BytesIO(data)
        if not data:
            logger.debug("no data for oid (%s)", oid)
            results[oid] = None
            continue

        overall_entropy, max_entropy, max_entropy_address, entropies, addresses = plot_entropy(bytes_data, chunk_size)
        result = {
            "entropies": entropies,
            "addresses": addresses,
            "block_size" : f'{addresses.__len__()} blocks of {chunk_size} bytes',
            "overall_entropy": round(overall_entropy,5),
            "max_entropy": round(max_entropy, 5),
            "max_entropy_address": f'0x{max_entropy_address:X}'
        }
        results[oid] = result

    return results