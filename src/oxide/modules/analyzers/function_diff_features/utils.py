from oxide.core import api
from difflib import unified_diff
from typing import Tuple, Dict, Any

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
    added_instr, removed_instr, opcode_mods, operand_mods = \
        _instruction_changes(target_func_insts, baseline_func_insts)

    # 2) basic-block delta
    basic_blocks = _get_bb_delta(
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
        'modified_opcode_instr':     opcode_mods,
        'modified_operand_instr':    operand_mods,
        'basic_blocks':              basic_blocks,
        'fc_add_existing':     new_exist,
        'fc_add_new':          new_new,
        'fc_removed_existing': removed_exist,
        'fc_removed_deleted':     removed_deleted,
    }

def _get_bb_delta(target_file, target_func, baseline_file, baseline_func):
    target_num_bb = None
    baseline_num_bb = None

    # TARGET FILE FUNCS
    file_disasm = api.retrieve('ghidra_disasm', target_file) or {}
    if file_disasm and target_func in file_disasm['functions']:
        call_mappings = api.get_field("function_call_targets", target_file, target_func)
        target_num_bb = len(file_disasm['functions'][target_func]['blocks'])
    
    # BASELINE FILE FUNCS
    file_disasm = api.retrieve('ghidra_disasm', baseline_file) or {}
    if file_disasm and baseline_func in file_disasm['functions']:
        call_mappings = api.get_field("function_call_targets", baseline_file, baseline_func)
        baseline_num_bb = len(file_disasm['functions'][baseline_func]['blocks'])
    
    if target_num_bb and baseline_num_bb:
        return target_num_bb - baseline_num_bb
    return 0 

def _get_fc_new(diff, target_file: str, target_func: str, baseline_file: str, baseline_func: str):
    """
    Count call-edge additions in the target function:
      • fc_add_existing: calls to functions present in the baseline
      • fc_add_new:      calls to brand-new functions
    """
    # Get list of all callees from target function
    target_calls = api.get_field('function_call_targets',
                                 target_file, target_func) or []
    # Get list of callees from baseline function
    baseline_calls = api.get_field('function_call_targets',
                                   baseline_file, baseline_func) or []

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
    u_diff = unified_diff(ref_func_insts, func_insts, n=0)

    # High-level counters
    total_lines_added = 0
    total_lines_removed = 0

    # Detailed counters for the "modified" lines
    total_opcode_modifications = 0
    total_operand_modifications = 0

    # For tracking lines within the current diff hunk
    minus_lines = []  # lines that start with '-'
    plus_lines = []   # lines that start with '+'

    def process_hunk(minus_list, plus_list):
        """
        Pair up the minus_list and plus_list lines (which should be
        the same length if they truly represent modifications),
        then figure out whether the opcode changed or just the operands.
        Returns (opcode_mod_count, operand_mod_count, leftover_minus, leftover_plus)
        """
        opcode_mod_count = 0
        operand_mod_count = 0

        # We will pair up as many lines as we can in one-to-one fashion
        pairs_to_check = min(len(minus_list), len(plus_list))
        for i in range(pairs_to_check):
            opcode_minus, operands_minus = parse_instruction(minus_list[i])
            opcode_plus, operands_plus = parse_instruction(minus_list[i])

            if opcode_minus == opcode_plus:
                # Same opcode => operand modification
                operand_mod_count += 1
            else:
                # Different opcode => opcode modification
                opcode_mod_count += 1

        # Return how many lines remain unpaired (i.e. purely added or removed)
        leftover_minus = len(minus_list) - pairs_to_check
        leftover_plus = len(plus_list) - pairs_to_check

        return opcode_mod_count, operand_mod_count, leftover_minus, leftover_plus

    # We'll process the diff line by line
    for line in u_diff:
        # Skip file header lines in the diff
        if line.startswith("---") or line.startswith("+++"):
            continue

        if line.startswith("@@"):
            # We’ve hit a new diff hunk. First, process the old one:
            if minus_lines or plus_lines:
                # Determine how many lines are purely added/removed vs. modified
                opcode_mod, operand_mod, leftover_minus, leftover_plus = process_hunk(minus_lines, plus_lines)
                total_opcode_modifications += opcode_mod
                total_operand_modifications += operand_mod

                # Lines that didn’t match up one-to-one are added or removed
                total_lines_removed += leftover_minus
                total_lines_added += leftover_plus

            # Reset lists for the new hunk
            minus_lines = []
            plus_lines = []
            continue

        # Collect lines in the current hunk
        if line.startswith("-"):
            minus_lines.append(line)
        elif line.startswith("+"):
            plus_lines.append(line)
        else:
            # Context line (no + or -), just ignore
            pass

    # After the loop, handle the final hunk (if any)
    if minus_lines or plus_lines:
        opcode_mod, operand_mod, leftover_minus, leftover_plus = process_hunk(minus_lines, plus_lines)
        total_opcode_modifications += opcode_mod
        total_operand_modifications += operand_mod
        total_lines_removed += leftover_minus
        total_lines_added += leftover_plus

    return total_lines_added, total_lines_removed, total_opcode_modifications, total_operand_modifications