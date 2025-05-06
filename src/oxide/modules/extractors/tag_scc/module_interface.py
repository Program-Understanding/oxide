DESC = "Uses an LLM to generate a tag for a given function and its call graph"
NAME = "tag_scc"
CATEGORY = ""  # used for filtering of modules e.g. disassemblers like ida

import logging

from typing import Dict, Any, List, Tuple
import networkx as nx
import textwrap
from oxide.core import api
from llm_service import runner

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

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
    result = {}

    cg: nx.DiGraph = api.get_field("call_graph", oid, oid)

    THRESH = 15                     # prune if < 15 instructions
    small = [n for n,d in cg.nodes(data=True)
            if d.get("instr_count", 0) < THRESH]
    
    orig_pairs = sum(1 for _ in nx.all_pairs_shortest_path_length(cg))

    # Prune
    Gp = prune_small_funcs(cg, small)

    # New reachability should be ≥ original (never less)
    assert sum(1 for _ in nx.all_pairs_shortest_path_length(Gp)) >= orig_pairs

    all_sccs = list(nx.strongly_connected_components(Gp))
    nontrivial_sccs = [s for s in all_sccs if len(s) > 1]

    for scc in nontrivial_sccs:
        members = sorted(scc)
        member_tags = []
        for fn in members:
            func_name = get_func_name(oid, fn)
            tag_ctx = api.retrieve("tag_function_context", oid, {"func_name": func_name})
            member_tags.append(tag_ctx)

        # dedupe & cap
        member_tags = sorted(set(member_tags))[:50]
        tags_str = ", ".join(member_tags)

        # generate candidates
        scc_tag = llm_tag(tags_str)

        # 4) store the super-node tag
        result[tuple(members)] = {"scc tag":scc_tag, "function tags": member_tags}
    api.store(NAME, oid, result, opts)
    return True

def llm_tag(scc_string: List, temperature: float = 0.2, max_new_tokens: int = 150) -> str:
    """
    Generate N candidate tags (tag, justification) by sampling the model.
    """

    prompt = textwrap.dedent(f"""
        ### SCC FUNCTION TAGS
        {scc_string}

        ────────────────────────────────────────────────────────────
        **Your task**

        1. Read *only* the tags above.  
        2. Decide the single, high-level purpose that unifies this strongly-connected component (SCC).  
        • If the tags suggest a finite-state machine, reflect that (e.g. “usb device fsm”).  
        3. Output **exactly two lines**:  

        Tag: <2–6-word, lower-case, verb-plus-noun theme>  
        Why: <≤ 15-word justification>  

        Rules
        • Do *not* mention code, reverse engineering, or these instructions.  
        • Use single spaces, no underscores/hyphens.  
        • No hedging or speculation language.
        • If the theme is genuinely unclear, output **unknown** on the Tag line and give a one-sentence explanation on the Why line.
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

    # Find and return the tag
    for line in text.splitlines():
        if line.lower().startswith("tag:"):
            return line.split(":", 1)[1].strip()
    return None

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

def build_scc_dag(G: nx.DiGraph):
    """
    Return
      * dag        –  a DiGraph whose nodes are frozensets of original functions
      * func2scc   –  dict: original node ➜ owning SCC node
    """
    # nx.strongly_connected_components returns generators of nodes
    scc_nodes  = [frozenset(c) for c in nx.strongly_connected_components(G)]
    func2scc   = {f:scc for scc in scc_nodes for f in scc}
    dag        = nx.DiGraph()

    for scc in scc_nodes:
        dag.add_node(scc)

    # add edges between SCCs (ignoring self-loops)
    for u, v in G.edges():
        su, sv = func2scc[u], func2scc[v]
        if su != sv:
            dag.add_edge(su, sv)

    return dag, func2scc

def prune_small_funcs(G, small):
    G = G.copy()                # keep the original intact
    for n in small:
        if n not in G:          # may already be gone via a previous pass
            continue

        preds = list(G.predecessors(n))
        succs = list(G.successors(n))

        # 1. add shortcut edges caller → callee
        for p in preds:
            for s in succs:
                if p != s:      # skip self-loops
                    if not G.has_edge(p, s):
                        G.add_edge(p, s)

        # 2. finally remove the tiny helper itself
        G.remove_node(n)

    return G