DESC = "Uses an LLM to generate a tag for a given function"
NAME = "tag_function"
CATEGORY = ""  # used for filtering of modules e.g. disassemblers like ida

import logging
from typing import Dict, List, Tuple, Any
import regex as re
from oxide.core import api
from llm_service import runner
import textwrap
from typing import Optional

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"func_name": {"type": str, "mangle": True, "default": "None"}}

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
    func_decomp = decomp_for_func(oid, func_name)
    if not func_decomp:
        logger.error(f"No decompilation found for function {func_name}")
        return False

    tag = llm_tag(func_decomp)
    result = tag
    api.store(NAME, oid, result, opts)
    return True

def llm_tag(func_decomp: str, temperature: float = 0.1, max_new_tokens: int = 150) -> Optional[str]:
    """
    Generate a single 2–6 word tag for a decompiled function.

    Args:
      func_name:     Name of the function.
      func_decomp:   Decompiled C code of the function.
      temperature:   Sampling temperature for diversity.
      max_new_tokens:Max number of tokens to generate.

    Returns:
      The extracted tag (without the 'Tag:' prefix), or None if parsing fails.
    """
    # Build the prompt
    prompt = textwrap.dedent(f"""
FUNCTION SOURCE (C)
```c
{func_decomp}

─────────────────────────────────────────────────────────
Your task:
• Read only on the function body above.
• Produce one 2-6-word tag that states what the function *does*  
• Produce one ≤ 15-word justification

─────────────────────────────────────────────────────────
Rules:
1. Tag must describe the *function's runtime behaviour*.
    ✗ Do **not** mention “reverse engineering”, "<tag>", “C code”, or variables/instructions found in the code.
2. Lower-case words, single spaces, no underscores/hyphens.
3. No hedging or speculation language.
4. If the purpose is completely unclear, output exactly "unknown".
5. Output exactly two lines in the following format, nothing else:

Tag: <tag>
Why: <justification>
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
            return None        
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

prompt = ""

def normalize_tag(raw: str) -> str:
    # 1) replace underscores/hyphens with spaces  
    # 2) collapse multiple spaces into one  
    # 3) lowercase everything  
    t = raw.replace("_", " ").replace("-", " ")
    t = " ".join(t.split())
    return t.lower()
