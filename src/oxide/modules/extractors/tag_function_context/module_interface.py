DESC = "Uses an LLM to generate a tag for a given function and its call graph"
NAME = "tag_function_context"
CATEGORY = ""  # used for filtering of modules e.g. disassemblers like ida

import logging

from typing import Dict, Any, List, Tuple
import networkx as nx
import openai
import os
from oxide.core import api
import subprocess
import tiktoken

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"func_name": {"type": str, "mangle": True},
            "n": {"type": int, "mangle": True, "default": 5}
            }

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
    n: int = opts["n"]

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

    func_call_graph = tag_descendants(func_call_graph, oid, n, skip_node=func_offset)

    candidates = tag_target_function(func_name, func_decomp, func_call_graph, func_offset, n)

    if n > 1:
        tag = llm_select_best(func_name, func_decomp, candidates)
    else:
        tag = candidates[0][0]

    api.store(NAME, oid, tag, opts)
    return True

def tag_descendants(G: nx.DiGraph, oid: str, n, skip_node: int) -> None:
    """Populate ``name/tag/confidence`` for every node *except* skip_node."""
    for fn in G.nodes:
        if fn == skip_node:
            continue  # defer tagging root to specialised prompt
        func_name = get_func_name(oid, fn)
        if not func_name:
            continue
        try:
            tag = api.retrieve("tag_function", oid, {"func_name": func_name, "n": n})
        except Exception as exc:  # pragma: no cover – stub error handling
            logger.warning("LLM tag_function failed for %s: %s", func_name, exc)
            tag = ""
        G.nodes[fn].update({"name": func_name, "tag": tag})
    return G


def tag_target_function(func_name:str, decomp: str, G: nx.DiGraph, root: int, n: int = 5) -> List[Tuple[str, str]]:
    """
    Prompt LLM with root decomp and descendant tags; generate N candidate tags (tag, justification) by sampling the model.
    """
    decomp = head_tail(decomp)

    # build descendant tag list
    tag_lines = []
    for node in G.nodes:
        if node == root:
            continue
        tag = G.nodes[node].get("tag", "")
        if not tag:
            continue
        depth = nx.shortest_path_length(G, root, node)
        tag_lines.append("." * depth + f"{G.nodes[node]['name']} ({tag})")
    tag_block = "\n".join(sorted(tag_lines)) or "<no descendants>"

    # prepare prompts
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        logger.error("OPENAI_API_KEY not set; aborting.")
        return ""

    system_prompt = (
        "You are a helpful assistant specialised in reverse engineering."
    )
    user_prompt = f"""
    You are an expert reverse-engineer.

    Function: `{func_name}`

    Decompiled C:
    ```c
    {decomp}
    ```

    Direct-callee tags:
    {tag_block}

    Child tags describe low-level work. Your tag must capture the single high-level purpose of `{func_name}`.
    Use 2-6 words, no punctuation except spaces and hyphens.
    Avoid words used verbatim in the child tags.

    Respond in this format exactly:
    Tag: <2-6 words>
    Why: <≤15 words>
    """
    response = openai.chat.completions.create(
        model="gpt-4o-mini",
        messages=[
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt}
        ],
        temperature=0.8,
        max_tokens=60,
        n=n
    )

    candidates: List[Tuple[str, str]] = []
    for choice in response.choices:
        tag = None
        why = None
        for line in choice.message.content.splitlines():
            lower = line.lower()
            if lower.startswith("tag:"):
                tag = line.split(":", 1)[1].strip()
            elif lower.startswith("why:"):
                why = line.split(":", 1)[1].strip()
        if tag and why:
            candidates.append((tag, why))
    return candidates

def llm_select_best(func_name: str, func_decomp: str, candidates: List[Tuple[str, float, str]]) -> Tuple[str, float]:
    """
    Select the best tag from the list of candidates.
    """
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        logger.error("OPENAI_API_KEY not set; aborting selection.")
        return ""

    system_prompt = "You are a precise assistant skilled at evaluating function tags."
    block = "\n".join(
        f"{i+1}. Tag: {t}  Why: {w}"
        for i, (t, w) in enumerate(candidates)
    )
    user_prompt = f"""
    ### FUNCTION
    Name: `{func_name}`
    ```
    {func_decomp}
    ```
    I have generated these tag candidates:
    {block}
    Which tag is the most accurate and specific? Respond exactly with:
    Tag: <tag>
    """
    response = openai.chat.completions.create(
        model="gpt-4o-mini",
        messages=[
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt}
        ],
        temperature=0.2,
        max_tokens=60
    )

    tag = ""
    for line in response.choices[0].message.content.splitlines():
        if line.lower().startswith("tag:"):
            tag = line.split(":", 1)[1].strip()
    return tag
        
    
def get_func_name(oid, offset):
    result = api.retrieve("function_summary", [oid])
    if result:
        result = result[oid]
        for func_name, details in result.items():
            offset_val = details['offset']
            if offset_val == offset:
                return func_name
            
def get_func_offset(oid, name):
    result = api.retrieve("function_summary", [oid])
    if result:
        summary = result[oid]
        if name in summary:
            return summary[name]['offset']
        
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
        return False


def head_tail(text: str,
              total_budget: int = 10_000,   # max tokens you want to keep
              side_tokens: int = 2_000      # tokens to keep from each end
              ) -> str:
    _enc = tiktoken.encoding_for_model("gpt-4o-mini")
    tokens = _enc.encode(text)
    n = len(tokens)

    # Fast path: under budget → no clipping
    if n <= total_budget:
        return text

    # Defensive: make sure we don’t ask for more than half the budget per side
    side_tokens = min(side_tokens, total_budget // 2)

    head_part = _enc.decode(tokens[:side_tokens])
    tail_part = _enc.decode(tokens[-side_tokens:])

    return f"{head_part}\n/* …clipped… */\n{tail_part}"