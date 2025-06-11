import os
import subprocess
import tempfile
import shutil
from bindiff import BinDiff
from bindiff.types import function_algorithm_str, basicblock_algorithm_str
from pathlib import Path

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
    Parse a .BinDiff database and return exhaustive statistics
    in a JSON-serialisable dict.
    """
    diff = BinDiff.from_binexport_files(binexp1, binexp2, bindiff_file)

    # 1. per-binary roll-ups
    file_stats = {
        "similarity": diff.similarity,              # float 0-1
        "confidence": diff.confidence,              # float 0-1
    }

    # running aggregates for convenience
    agg = {"matched_functions": 0,
           "matched_basic_blocks": 0,
           "matched_instructions": 0}

    # 2. per-function detail
    fun_matches = {}
    for f1, f2, fm in diff.iter_function_matches():
        fun_matches[(hex(f1.addr), hex(f2.addr))] = {
            "similarity":        fm.similarity,
            "confidence":        fm.confidence,
            "algorithm": {
                "id": fm.algorithm, 
                "name": function_algorithm_str(fm.algorithm),
            },
            "functions": {
                "primary": {
                    "address": hex(f1.addr),
                    "name": f1.name
                },
                "secondary": {
                    "address": hex(f2.addr),
                    "name": f2.name,
                }
            },
        }

        # update aggregates
        agg["matched_functions"]     += 1

    # 3. unmatched functions
    unmatched_primary = [
        {"address": hex(f.addr), "name": f.name}
        for f in diff.primary_unmatched_function()
    ]
    unmatched_secondary = [
        {"address": hex(f.addr), "name": f.name}
        for f in diff.secondary_unmatched_function()
    ]

    # 4. wrap-up
    file_stats.update(agg)
    return {
        "file_stats":        file_stats,
        "function_matches":  fun_matches,
        "unmatched_primary": unmatched_primary,
        "unmatched_secondary": unmatched_secondary,
    }