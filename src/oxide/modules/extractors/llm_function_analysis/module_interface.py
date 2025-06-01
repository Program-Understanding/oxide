DESC = ""
NAME = "llm_function_analysis"
CATEGORY = ""  # used for filtering of modules e.g. disassemblers like ida

import logging

from typing import Dict, Any, List, Tuple
import networkx as nx
import textwrap
from oxide.core import api
from llm_service import runner
import prompts
import re
import os

import prompts.tag_context

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"func_name": {"type": str, "mangle": True}}

"""
options dictionary defines expected options, including type, default value, and whether
presence of option distinguishes a version of output (mangle).

An example of option
{"version": {"type": int, "mangle": True, "default": -1}
where 'version' is guarenteed to be passed into opts of process
    it has type int, with default value -1, and caching of results only relevant to this value
        template_extract --version=1 vs template_extract --version=2
    would result in running two different times
"""


PROMPT_TABLE = {
    "tag_context": prompts.tag_context.run,
    "tag": prompts.tag_context.run,
    # add other prompt types as needed
}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY}


def process(oid: str, opts: dict) -> bool:
    logger.debug("process() start for %s", oid)

    func_offset: str = opts["func_offset"]
    prompt_key: str = opts["prompt"]

    # ------------------------------------------------------------
    # 1. Locate the target function by offset
    # ------------------------------------------------------------
    if func_offset is None:
        logger.error("Function offset not provided for %s", oid)
        return False

    # ------------------------------------------------------------
    # 2. Retrieve prompt handler
    # ------------------------------------------------------------
    prompt_func = PROMPT_TABLE.get(prompt_key)
    if prompt_func is None:
        logger.error("Unknown prompt type: %s", prompt_key)
        return False

    tag = prompt_func(oid, func_offset)
    api.store(NAME, oid, tag, opts)
    return True

        