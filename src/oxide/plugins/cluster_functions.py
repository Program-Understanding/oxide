import json
import math
import re
import logging
from collections import Counter, defaultdict
from typing import List, Dict, Tuple, Optional, Any
import os
from pathlib import Path
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import pearsonr
import time
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
from typing import List, Dict, Any
import textwrap

try:
    from rank_bm25 import BM25Okapi
except ImportError:
    BM25Okapi = None


import numpy as np
from sentence_transformers import SentenceTransformer
from transformers import AutoTokenizer

from oxide.core import api

NAME="cluster_functions"

# -------------------------------------------------------------
# Configuration & Setup
# -------------------------------------------------------------
MODEL_ID = ""
tokenizer = 
model = SentenceTransformer(MODEL_ID)
MAX_TOKENS = tokenizer.model_max_length
ALNUM = re.compile(r"[A-Za-z]{3,}")

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(NAME)


def cluster(args, opts):
    results = {}
    oid = args[0]

    # Returns networkX graph of the call_graph
    call_graph = api.retrieve("call_graph", [oid])

    return

def decomp_for_func(oid:str, function_name:str):
    """
    Returns the decompiled code for a given function.

    Inputs:
        oid: the ID of the binary file containing the desired function
        function_name: the name of the desired function

    Returns: 
        a string containing the source code for the function
    """
    result = api.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if result:
        # Find object for this function
        functions_dict = result['decompile']

        if (function_name not in functions_dict.keys()):
            return False        
        function_dict = functions_dict[function_name] 

        # Gather the decompilation lines into a map (they will not be returned in order)
        decomp_map = {}
        for offset_key, offset_value in function_dict.items():
            # For this offset, walk through the lines to add to the decomp line map
            for line_str in offset_value['line']:
                # Extract the line number and code text 
                split = line_str.find(": ")
                line_no_str = line_str[:split]
                line_no = int(line_no_str)
                code = line_str[split + 2:]
                # Find the decomp line for this line number. Create it if not existing.
                decomp_line = decomp_map.get(line_no, None)
                if not decomp_line:
                    decomp_map[line_no] = code

        # Generate a string with all the decompilation line in order
        return_str = ''
        indent_level = 0
        for line_num in sorted(decomp_map.keys()):
            code = str(decomp_map[line_num])
            if '}' in code:
                indent_level -= 1
            return_str += (('    ' * indent_level) + code + '\n')
            if '{' in code:
                indent_level += 1
        return return_str
    else:
        return None