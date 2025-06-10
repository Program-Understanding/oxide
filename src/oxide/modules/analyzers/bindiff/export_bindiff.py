import os
import subprocess
import tempfile
import json
import shutil
from bindiff import BinDiff

def run_ghidra_binexport(ghidra_path, input_file, output_dir, script_path, use_xvfb=True):
    """
    Run Ghidra headlessly to export a BinExport file.

    If `use_xvfb` is True, wraps the call with xvfb-run to simulate an X server.
    Ensures Java runs in headless mode to avoid AWT errors.
    """
    env = os.environ.copy()
    opts = env.get("JAVA_TOOL_OPTIONS", "")
    env["JAVA_TOOL_OPTIONS"] = f"{opts} -Djava.awt.headless=true".strip()

    base_name = os.path.splitext(os.path.basename(input_file))[0]
    output_binexport = os.path.join(output_dir, f"{base_name}.BinExport")


    script_dir = script_path if os.path.isdir(script_path) else os.path.dirname(script_path)
    ghidra_bin = os.path.join(ghidra_path, "support", "analyzeHeadless")
    base_cmd = [
        ghidra_bin,
        None,
        "temp_proj",
        "-import", input_file,
        "-scriptPath", script_dir,
        "-postScript", "ExportBinDiffScript", output_binexport,
        "-noanalysis",
        "-deleteProject"
    ]

    with tempfile.TemporaryDirectory() as tmp_proj:
        base_cmd[1] = tmp_proj
        if use_xvfb:
            if shutil.which("xvfb-run") is None:
                raise EnvironmentError(
                    "'xvfb-run' not found in PATH. Install Xvfb: 'sudo apt-get install xvfb'"
                )
            cmd = ["xvfb-run", "-a"] + base_cmd
        else:
            cmd = base_cmd
        subprocess.run(cmd, check=True, env=env)

    if not os.path.exists(output_binexport):
        raise FileNotFoundError(f"Expected BinExport not found at: {output_binexport}")
    return output_binexport


def run_bindiff(primary, secondary, output_dir):
    """
    Run BinDiff on two BinExport files, ensuring the output_dir exists.
    """
    output_dir = output_dir or os.getcwd()
    # Create output directory if it doesn't exist
    os.makedirs(output_dir, exist_ok=True)
    if not os.access(output_dir, os.W_OK):
        raise PermissionError(f"Output directory not writable: {output_dir}")

    subprocess.run([
        "bindiff",
        "--primary", primary,
        "--secondary", secondary,
        "--output_dir", output_dir
    ], check=True)

    base1 = os.path.splitext(os.path.basename(primary))[0]
    base2 = os.path.splitext(os.path.basename(secondary))[0]
    expected = os.path.join(output_dir, f"{base1}_vs_{base2}.BinDiff")
    if not os.path.isfile(expected):
        raise FileNotFoundError(f"Expected .BinDiff not found: {expected}")
    return _parse_bindiff_to_dict(primary, secondary, expected)


def _parse_bindiff_to_dict(binexp1, binexp2, bindiff_file):
    """
    Parse a .BinDiff file and return statistics as a Python dict.
    """
    diff = BinDiff.from_binexport_files(binexp1, binexp2, bindiff_file)
    stats = {"matched_functions": [], "unmatched_primary": [], "unmatched_secondary": []}

    for f1, f2, match in diff.iter_function_matches():
        bb_matches = list(diff.iter_basicblock_matches(f1, f2))
        instr_matched = sum(
            len(list(diff.iter_instruction_matches(bb1, bb2))) for bb1, bb2, _ in bb_matches
        )
        instr_unmatched_prim = sum(len(diff.primary_unmatched_instruction(bb1)) for bb1, _, _ in bb_matches)
        instr_unmatched_sec  = sum(len(diff.secondary_unmatched_instruction(bb2)) for _, bb2, _ in bb_matches)

        stats["matched_functions"].append({
            "primary_address": hex(f1.addr),
            "secondary_address": hex(f2.addr),
            "function_name": f1.name,
            "similarity": match.similarity,
            "confidence": match.confidence,
            "basic_block_stats": {
                "matched": len(bb_matches),
                "unmatched_primary": len(diff.primary_unmatched_basic_block(f1)),
                "unmatched_secondary": len(diff.secondary_unmatched_basic_block(f2))
            },
            "instruction_stats": {
                "matched": instr_matched,
                "unmatched_primary": instr_unmatched_prim,
                "unmatched_secondary": instr_unmatched_sec
            }
        })

    for func in diff.primary_unmatched_function():
        stats["unmatched_primary"].append({"address": hex(func.addr), "function_name": func.name})
    for func in diff.secondary_unmatched_function():
        stats["unmatched_secondary"].append({"address": hex(func.addr), "function_name": func.name})

    return stats