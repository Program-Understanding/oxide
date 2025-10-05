
from typing import Dict, Any, List, Tuple
import networkx as nx
import textwrap
from oxide.core import api
from ollama_service import runner
import re
import time


def run(oid, func_offset):
    func_name = get_func_name(oid, func_offset)
    func_decomp = decomp_for_func(oid, func_name)
    if func_decomp is None:
        return False, False, 0
    return semantic_function_tag(func_decomp)

def semantic_function_tag(decomp: str, temperature: float = 0.15, max_new_tokens: int = 150) -> str:

    # Build the prompt
    prompt = textwrap.dedent(f"""
FUNCTION SOURCE (C)
```c
{decomp}

─────────────────────────────────────────────────────────
Your task:
• Read only on the function body above.
• Produce one 2-6-word tag that states what the function *does*  
• Produce one ≤ 15-word justification (why)

─────────────────────────────────────────────────────────
Rules:
1. Tag must describe the *function's runtime behaviour*.
    ✗ Do **not** mention “reverse engineering”, "<tag>", “C code”, or variables/instructions found in the code.
2. Lower-case words, single spaces, no underscores/hyphens.
3. No hedging or speculation language.
4. If the purpose is completely unclear, output exactly "unknown".
5. Output exactly two lines in the following format, nothing else:

Tag: <tag>
Why: <why>
""").strip()

    t0 = time.time()
    response = runner.generate(
        user_input=prompt,
        temperature=temperature,
        max_new_tokens=max_new_tokens
    )
    t1 = time.time()
    gpu_time_sec = t1 - t0

    raw_text = ("\n".join(response).strip()
                if isinstance(response, list)
                else response.strip())

    for line in raw_text.splitlines():
        if line.lower().startswith("tag:"):
            raw_tag = line.split(":", 1)[1].strip()
        if line.lower().startswith("why:"): 
            why = line.split(":", 1)[1].strip()

    return raw_tag, why, gpu_time_sec
        
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
        return None