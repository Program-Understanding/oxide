from oxide.core import api
from difflib import unified_diff

def retrieve_function_instructions(file, func):
    """
    Retrieve function instructions for a specific function by its name.
    """
    function_data = api.retrieve('function_tlsh', file, {'replace_addrs': True})
    for func_id, details in function_data.items():
        if details.get('name') == func:
            return details.get('modified_fun_instructions', None)
    return None

def diff_features(file, func_name, func_insts, ref_file, ref_func_name, ref_func_insts):
    added_instr = 0
    removed_instr = 0
    modified_isntr = 0
    basic_blocks = 0
    func_calls = 0

    # Control Flow
    num_func_bb, num_func_calls = _get_bb(file, func_name)
    num_ref_func_bb, num_ref_func_calls = _get_bb(ref_file, ref_func_name)

    if num_func_bb - num_ref_func_bb != 0:
        basic_blocks = num_func_bb - num_ref_func_bb

    if num_func_calls - num_ref_func_calls != 0:
        func_calls = num_func_calls - num_ref_func_calls

    added_instr, removed_instr, modified_isntr, = _instruction_changes(func_insts, ref_func_insts)
    return added_instr, removed_instr, modified_isntr, basic_blocks, func_calls

def _get_bb(file, func):
    file_disasm = api.retrieve('ghidra_disasm', file)
    for func_addr in file_disasm['functions']:
        if file_disasm['functions'][func_addr]['name'] == func:
            call_mappings = api.get_field("call_mapping", file, func_addr)
            function_calls = len(call_mappings['calls_to'])
            num_bb = len(file_disasm['functions'][func_addr]['blocks'])
            return function_calls, num_bb
    return 0, 0

def _instruction_changes(func_insts, ref_func_insts):
    u_diff = unified_diff(func_insts, ref_func_insts, n=0)

    # Initialize counters
    lines_added = 0
    lines_removed = 0
    total_lines_added = 0
    total_lines_removed = 0
    total_lines_modified = 0

    # Process the diff
    for line in u_diff:
        if line.startswith("---") or line.startswith("+++"):
            # Skip file headers
            continue
        
        if line.startswith("-"):
            lines_removed += 1
        elif line.startswith("+"):
            lines_added += 1
        elif line.startswith("@@"):
            if lines_added == lines_removed:
                total_lines_modified += lines_added
            else:
                total_lines_added += lines_added
                total_lines_removed += lines_removed
            lines_added = 0
            lines_removed = 0
            continue
        else:
            continue

        if lines_added == lines_removed:
            total_lines_modified += lines_added

    return total_lines_added, total_lines_removed, total_lines_modified