from oxide.core import api
from difflib import unified_diff


def retrieve_function_instructions(file, func):
    """
    Retrieve function instructions for a specific function by its name.
    """
    function_data = api.retrieve('function_representations', file, {'lift_addrs': False})
    if func in function_data:
        return function_data[func].get('fun_instructions')
    
    return None

def diff_features(diff, target_file, target_function,
                  target_func_insts, baseline_file,
                  baseline_func,   baseline_func_insts):
    """
    Compute low-level change features between
    (target_file, target_function) and
    (baseline_file, baseline_func).
    Drops the old func_calls metric in favor of detailed
    new-vs-removed call counts.
    """
    # 1) instruction-level changes
    added_instr, removed_instr = _instruction_changes(target_func_insts, baseline_func_insts)

    # 2) basic-block delta
    bb_nodes, bb_edges = _get_bb_delta(
        target_file, target_function,
        baseline_file, baseline_func
    )

    # 3) new calls split into existing vs brand-new targets
    new_exist, new_new = _get_fc_new(
        diff,
        target_file,   target_function,
        baseline_file, baseline_func
    )

    # 4) removed calls split into existing vs deleted
    removed_exist, removed_deleted = _get_fc_removed(
        diff,
        target_file,   target_function,
        baseline_file, baseline_func
    )

    return {
        'added_instr':               added_instr,
        'removed_instr':             removed_instr,
        'bb_nodes':                  bb_nodes,
        'bb_edges':                  bb_edges,
        'fc_add_existing':           new_exist,
        'fc_add_new':                new_new,
        'fc_removed_existing':       removed_exist,
        'fc_removed_deleted':        removed_deleted
    }

def _get_bb_delta(target_file, target_func, baseline_file, baseline_func):
    """
    Returns a tuple:
      (Δ#basic_blocks, Δ#internal_edges)
    between target_func in target_file and baseline_func in baseline_file.
    """
    # — TARGET —
    target_disasm = api.retrieve('ghidra_disasm', target_file) or {}
    target_blocks = set()
    target_edges = 0

    if target_disasm and target_func in target_disasm['functions']:
        target_blocks = set(target_disasm['functions'][target_func]['blocks'])
        target_bb_count = len(target_blocks)

        # need the global original_blocks map for edge info
        target_orig_blocks = api.get_field("ghidra_disasm", target_file, "original_blocks") or {}

        for b in target_blocks:
            for dst in target_orig_blocks.get(b, {}).get("dests", []):
                if dst in target_blocks:
                    target_edges += 1
    else:
        target_bb_count = None

    # — BASELINE —
    base_disasm = api.retrieve('ghidra_disasm', baseline_file) or {}
    baseline_edges = 0

    if base_disasm and baseline_func in base_disasm['functions']:
        base_blocks = set(base_disasm['functions'][baseline_func]['blocks'])
        baseline_bb_count = len(base_blocks)

        base_orig_blocks = api.get_field("ghidra_disasm", baseline_file, "original_blocks") or {}

        for b in base_blocks:
            for dst in base_orig_blocks.get(b, {}).get("dests", []):
                if dst in base_blocks:
                    baseline_edges += 1
    else:
        baseline_bb_count = None

    # — DELTAS —
    if target_bb_count is not None and baseline_bb_count is not None:
        bb_delta   = target_bb_count   - baseline_bb_count
        edge_delta = target_edges      - baseline_edges
        return bb_delta, edge_delta

    # fallback if one side is missing
    return 0, 0

def _get_fc_new(diff, target_file: str, target_func: str, baseline_file: str, baseline_func: str):
    """
    Count call-edge additions in the target function:
      • fc_add_existing: calls to functions present in the baseline
      • fc_add_new:      calls to brand-new functions
    """
    # Get list of all callees from target function
    target_calls = api.get_field('function_call_targets', target_file, target_func) or []
    # Get list of callees from baseline function
    baseline_calls = api.get_field('function_call_targets', baseline_file, baseline_func) or []

    # function_matches: keys are (t_addr, b_addr)
    matches = diff.get('function_matches', {})

    num_add_existing = 0
    num_add_new = 0

    for callee in target_calls:
        # find a matching baseline function for this callee, if any
        bf = None
        for t_addr, b_addr in matches:
            if t_addr == callee:
                bf = b_addr
                break

        if bf is not None:
            # this callee corresponds to baseline function bf
            if bf in baseline_calls:
                # baseline already called bf, so this edge is not new
                continue
            # bf existed but was not previously called
            num_add_existing += 1
        else:
            # no match → brand-new function
            num_add_new += 1

    return num_add_existing, num_add_new


def _get_fc_removed(diff, target_file, target_func,
                    baseline_file, baseline_func):
    """
    Count, for a given function diff, how many call-edges
    present in the baseline are missing in the target,
    split into:
      • removed_existing: calls to functions that still existed
      • removed_deleted: calls to functions that have been removed
    """
    # Get all callees from baseline and target
    baseline_calls = api.get_field('function_call_targets', baseline_file, baseline_func) or []
    target_calls   = api.get_field('function_call_targets', target_file,     target_func)   or []

    # Keys of diff['function_matches'] are (t_addr, b_addr)
    match_pairs = diff.get('function_matches', {}).keys()

    removed_existing = 0
    removed_deleted  = 0

    for b_addr in baseline_calls:
        # find corresponding t_addr for this b_addr, if any
        tf = None
        for t_addr, bb in match_pairs:
            if bb == b_addr:
                tf = t_addr
                break

        if tf is not None:
            # this baseline function survived, so check if it’s still called
            if tf in target_calls:
                # still called → not removed
                continue
            # survived but call-edge was removed
            removed_existing += 1
        else:
            # no match → function was deleted entirely
            removed_deleted += 1
    return removed_existing, removed_deleted

def parse_instruction(line):
    """
    Given a single line of disassembly (e.g. '+_addiu a0,a0,0x24'),
    return (opcode, operands). We strip off the first character (+ or -)
    and split on whitespace so that the first token is the opcode and
    the remainder is the operand string.
    """
    # Remove leading diff marker (+/-) and any surrounding whitespace
    line = line[1:].strip()
    if not line:
        return "", ""
    # Split once on whitespace: first token is opcode, rest is operands
    parts = line.split(None, 1)
    opcode = parts[0]
    operands = parts[1] if len(parts) > 1 else ""
    return opcode, operands

def _instruction_changes(func_insts, ref_func_insts):
    """
    Returns (lines_added, lines_removed) between ref_func_insts and func_insts.
    """
    total_added = 0
    total_removed = 0

    for line in unified_diff(ref_func_insts, func_insts, n=0):
        # skip diff metadata
        if line.startswith('+++') or line.startswith('---'):
            continue
        # count additions/removals
        if line.startswith('+'):
            total_added += 1
        elif line.startswith('-'):
            total_removed += 1

    return total_added, total_removed