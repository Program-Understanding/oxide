from oxide.core import api
from difflib import unified_diff

def retrieve_function_instructions(file, func):
    """
    Retrieve function instructions for a specific function by its name.
    """
    function_data = api.retrieve('function_representations', file, {'lfit_addrs': True})
    for func_id, details in function_data.items():
        if details.get('name') == func:
            return details.get('modified_fun_instructions', None)
    return None

def diff_features(target_file, target_func_name, target_func_insts, baseline_file, baseline_func_name, baseline_func_insts):
    added_instr = 0
    removed_instr = 0
    basic_blocks = 0
    func_calls = 0

    # Control Flow
    num_target_func_bb, num_target_func_calls = _get_bb(target_file, target_func_name)
    num_baseline_func_bb, num_baseline_func_calls = _get_bb(baseline_file, baseline_func_name)

    if num_target_func_bb - num_baseline_func_bb != 0:
        basic_blocks = num_target_func_bb - num_baseline_func_bb

    if num_target_func_calls - num_baseline_func_calls != 0:
        func_calls = num_target_func_calls - num_baseline_func_calls

    added_instr, removed_instr, opcode_modifications, operand_modifications = _instruction_changes(target_func_insts, baseline_func_insts)
    return added_instr, removed_instr, opcode_modifications, operand_modifications, basic_blocks, func_calls

def _get_bb(file, func):
    file_disasm = api.retrieve('ghidra_disasm', file)
    for func_addr in file_disasm['functions']:
        if file_disasm['functions'][func_addr]['name'] == func:
            call_mappings = api.get_field("call_mapping", file, func_addr)
            function_calls = len(call_mappings['calls_to'])
            num_bb = len(file_disasm['functions'][func_addr]['blocks'])
            return function_calls, num_bb
    return 0, 0

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
    u_diff = unified_diff(func_insts, ref_func_insts, n=0)

    # High-level counters
    total_lines_added = 0
    total_lines_removed = 0
    total_lines_modified = 0

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