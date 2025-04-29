DESC = "Uses an LLM to generate a tag for a given function"
NAME = "tag_function"
CATEGORY = ""  # used for filtering of modules e.g. disassemblers like ida

import logging
from typing import Dict, List, Tuple, Any
import os
import openai
from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"func_name": {"type": str, "mangle": True, "default": "None"},
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
    """
    Extracts a decompiled function, generates multiple tag candidates, then selects the best one.
    """
    logger.debug("process()")

    func_name = opts['func_name']
    n = opts['n']
    func_decomp = decomp_for_func(oid, func_name)
    if not func_decomp:
        logger.error(f"No decompilation found for function {func_name}")
        return False

    # 1) Generate multiple tag candidates
    candidates = llm_generate_candidates(func_name, func_decomp, n)
    if not candidates:
        logger.error("No tag candidates generated")
        return False

    if n > 1:
        tag = llm_select_best(func_name, func_decomp, candidates)
    else:
        tag = candidates[0][0]
    

    result = tag
    api.store(NAME, oid, result, opts)
    return True
    
def llm_generate_candidates(func_name: str, func_decomp: str, n: int = 5) -> List[Tuple[str, str]]:
    """
    Generate N candidate tags (tag, justification) by sampling the model.
    """
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        logger.error("OPENAI_API_KEY not set; aborting candidate generation.")
        return []

    system_prompt = "You are a helpful assistant specialised in reverse engineering."
    user_prompt = f"""
    ### FUNCTION
    Name: `{func_name}`
    ```
    {func_decomp}
    ```
    Task: Propose a concise 2–6 word tag and a ≤15-word justification.
    Respond exactly in two lines:
    Tag: <tag>
    Why: <justification>
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

prompt = ""