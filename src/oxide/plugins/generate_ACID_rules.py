""" Plugin: Prints out capa results for an oid.
"""
import collections
import os
import json
from typing import Any
from typing import *
from oxide.core import api
import tabulate
import capa.rules
import capa.engine
import capa.features
import capa.render.json
import capa.render.utils as rutils
import capa.render.default
import capa.render.result_document as rd
import capa.features.freeze.features as frzf
from pathlib import *

def generate_acid_rules(args, opts):

    valid, invalid = api.valid_oids(args)
    oids = api.expand_oids(valid)
    result = {}
    for oid in oids:
        acid_results = api.get_field("acid", oid, oid)
        ghidra_disasm = api.retrieve("ghidra_disasm", oid)
        subgraphs = acid_results['Subgraphs']
        descriptions = {}
        for subgraph in subgraphs:
            descriptions[subgraph] = {}
            descriptions[subgraph]['capabilities'] = subgraphs[subgraph]
            function_name = ghidra_disasm['functions'][subgraph]['name']
            descriptions[subgraph]['function_name'] = function_name
        result[oid] = descriptions

    return result


exports = [generate_acid_rules]
