
from typing import Dict, Any, List, Tuple
import networkx as nx
import textwrap
from oxide.core import api
from llm_service import runner
import re
import os


def run(oid, func_offset):
    func_name = get_func_name(oid, func_offset)

    full_graph: nx.DiGraph = api.get_field("call_graph", oid, oid)
    if full_graph.has_node(func_offset):
        children = list(full_graph.successors(func_offset))
    else:
        children = []

    sub_nodes = set(children) | {func_offset}
    func_call_graph = full_graph.subgraph(sub_nodes).copy()

    func_decomp = decomp_for_func(oid, func_name)
    if func_decomp is None:
        return False

    excl_tags, shared_tags = descendants_tags(func_call_graph, oid, func_offset)
    tag = semantic_function_tag(func_decomp, excl_tags, shared_tags, oid, func_name)
    return tag

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
            if api.exists("tag_function_context", oid, {"func_name": func_name}):
                tag = api.retrieve("tag_function_context", oid, {"func_name": func_name})
            else:
                print("No tag with context")
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


def semantic_function_tag(
    decomp: str,
    excl_tags: List[str],
    shared_tags: List[str],
    oid: str,
    func_name: str,
    temperature: float = 0.15,
    max_new_tokens: int = 150
) -> str:
    excl_block = "\n".join(sorted(excl_tags)) or "<no exclusive descendants>"
    shared_block = "\n".join(sorted(shared_tags)) or "<no shared descendants>"

    prompt = textwrap.dedent(f"""
FUNCTION SOURCE:
```c
{decomp}

Exclusive Direct-callee function tags:
{excl_block}

Shared Direct-callee function tags:
{shared_block}

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
""")

    response = runner.generate(
        user_input=prompt,
        temperature=temperature,
        max_new_tokens=max_new_tokens
    )

    raw_text = ("\n".join(response).strip()
                if isinstance(response, list)
                else response.strip())

    # Ensure the prompts directory exists
    prompts_dir = "llm_prompts"
    try:
        os.makedirs(prompts_dir, exist_ok=True)
        filename = os.path.join(prompts_dir, f"{oid}_{func_name}.txt")
        with open(filename, "w", encoding="utf-8") as f:
            f.write("Prompt:\n")
            f.write(prompt + "\n\n")
            f.write("Response:\n")
            f.write(raw_text + "\n")
    except Exception as e:
        logger.error(f"Failed to save prompt and response: {e}")

    for line in raw_text.splitlines():
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