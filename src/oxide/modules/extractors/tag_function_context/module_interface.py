DESC = "Uses an LLM to generate a tag for a given function and its call graph"
NAME = "tag_function_context"
CATEGORY = ""  # used for filtering of modules e.g. disassemblers like ida

import logging

from typing import Dict, Any, List, Tuple
import networkx as nx
import textwrap
from oxide.core import api
from llm_service import runner
import re

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


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY}


def process(oid: str, opts: dict) -> bool:
    logger.debug("process() start for %s", oid)

    func_name: str = opts["func_name"]

    # ------------------------------------------------------------
    # 1. Locate the target function by offset
    # ------------------------------------------------------------
    func_offset = get_func_offset(oid, func_name)
    if func_offset is None:
        logger.error("Function %s not found in summary for %s", func_name, oid)
        return False

    full_graph: nx.DiGraph = api.get_field("call_graph", oid, oid)
    if full_graph.has_node(func_offset):
        children = list(full_graph.successors(func_offset))
    else:
        children = []
        logger.warning(f"Attempted to get successors of missing node {func_offset}")

    sub_nodes = set(children) | {func_offset}
    func_call_graph = full_graph.subgraph(sub_nodes).copy()

    func_decomp = decomp_for_func(oid, func_name)
    if func_decomp is None:
        return False

    excl_tags, shared_tags = descendants_tags(func_call_graph, oid, func_offset)
    tag = tag_target_function(func_decomp, excl_tags, shared_tags, func_offset)

    api.store(NAME, oid, tag, opts)
    return True

def descendants_tags(G: nx.DiGraph, oid: str, root: int) -> List:
    """
    Collect two buckets of tags for the call-tree under *root*.

    Returns
    -------
    (exclusive, shared)
        exclusive : tags whose function has **exactly one in-edge** and that
                    edge comes from *root*            → high-signal
        shared    : tags for every other reachable node (≥1 extra caller) → low-signal
    """
    excl_tags: List[str]   = []
    shared_tags: List[str] = []

    # --- all nodes reachable from *root* (children, grandchildren, …) -----------
    reachable = nx.descendants(G, root)
    for fn in reachable:
        if not valid_function(oid, fn):
            continue

        func_name = get_func_name(oid, fn)
        if not func_name:
            continue

        try:
            tag = api.retrieve("tag_function", oid, {"func_name": func_name})
        except Exception as exc:                  # pragma: no cover – stub error handling
            logger.warning("LLM tag_function failed for %s: %s", func_name, exc)
            continue

        if tag:
            # ---------- exclusive vs shared  ----------------------------------------
            preds = list(G.predecessors(fn))
            if len(preds) == 1 and preds[0] == root:
                excl_tags.append(tag)
            else:
                shared_tags.append(tag)

    excl_tags = list(dict.fromkeys(excl_tags))
    shared_tags = list(dict.fromkeys(shared_tags))

    return excl_tags, shared_tags


def tag_target_function(decomp: str, excl_tags: List, shared_tags: List, root: int, temperature: float = 0.15, max_new_tokens: int = 150) -> str:
    """
    Prompt LLM with root decomp and descendant tags; generate N candidate tags (tag, justification) by sampling the model.
    """
    excl_tag_block = "\n".join(sorted(excl_tags)) or "<no exclusive descendants>"
    shared_tag_block = "\n".join(sorted(shared_tags)) or "<no shared descendants>"
    prompt = textwrap.dedent(f"""
FUNCTION SOURCE:
```c
{decomp}

Exclusive Direct-callee function tags:
{excl_tag_block}

Shared Direct-callee function tags:
{shared_tag_block}

─────────────────────────────────────────────────────────
Your task:
• Read only the C body and the callee tags above.
• Produce exactly one 2-6 word descriptive tag stating clearly what the function *does*.
• Produce exactly one ≤ 15-word justification clearly explaining the chosen tag.

─────────────────────────────────────────────────────────
Rules:
1. Tag must describe the *function's runtime behaviour*.
    ✗ Do **not** mention “reverse engineering”, “C code”, or these instructions.
2. Lower-case words, single spaces, no underscores/hyphens.
3. No hedging, placeholders, or speculation language.
4. If the purpose is completely unclear or uncertain, output exactly:

Tag: unknown
Why: function's behavior unclear from provided information

5. Output exactly two lines, nothing else:

Tag: your tag here
Why: one concise justification
""").strip()

    # Call the model
    response = runner.generate(
        user_input=prompt,
        temperature=temperature,
        max_new_tokens=max_new_tokens
    )

    # Normalize to single text block
    text = (
        "\n".join(response).strip()
        if isinstance(response, list)
        else response.strip()
    )

    # Find, normalize, and return the tag
    for line in text.splitlines():
        if line.lower().startswith("tag:"):
            raw_tag = line.split(":", 1)[1].strip()
            return normalize_tag(raw_tag)

    return None

    
def get_func_offset(oid, name):
    functions = api.get_field("ghidra_disasm", oid, "functions")
    if functions:
        for func in functions:
            if functions[func]['name'] == name:
                return func
    return None
        
def get_func_name(oid, offset):
    functions = api.get_field("ghidra_disasm", oid, "functions")
    if functions:
        for func in functions:
            if func == offset:
                return functions[func]['name']
    return None
        
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
        logger.error("Failed to retrieve ghidra decompilation mapping")
        return None
    
def normalize_tag(raw: str) -> str:
    # replace underscores/hyphens with spaces
    t = raw.replace("_", " ").replace("-", " ")
    # strip all other punctuation
    t = re.sub(r"[^\w\s]", " ", t)
    # collapse whitespace
    t = " ".join(t.split())
    return t.lower()

def valid_function(oid, offset):
    functions = api.get_field("ghidra_disasm", oid, "functions")
    if offset in functions:
        fn_blocks = functions[offset]['blocks']
    else:
        return False
    blocks = api.get_field("ghidra_disasm", oid, "original_blocks")
    num_instructions = 0
    for b in fn_blocks:
        if b in blocks:
            num_instructions += len(blocks[b])
    if num_instructions > 5:
        return True
    return False

def split_child_tags(G: nx.DiGraph, node_tags: dict[int, list[str]], parent: int) -> tuple[list[str], list[str]]:
    """Return (exclusive_tags, shared_tags) for *parent*’s direct callees."""
    ex, sh = [], []
    for child in G.successors(parent):
        tags = node_tags.get(child, [])
        if G.in_degree(child) == 1:       # ← exclusive
            ex.extend(tags)
        else:                             # ← shared
            sh.extend(tags)
    # dedupe but preserve order
    return list(dict.fromkeys(ex)), list(dict.fromkeys(sh))