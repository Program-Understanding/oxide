import os
import subprocess
import tempfile
import shutil
from bindiff import BinDiff
from bindiff.types import function_algorithm_str
from pathlib import Path
from oxide.core.libraries.ghidra_utils import get_file_offset
from oxide.core import api

LOAD_ADDR = 0

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
        return None

    return output_binexport


def run_bindiff(primary_oid, primary,  secondary_oid, secondary, output_dir, use_func_names=False):
    """
    Run BinDiff on two BinExport files, ensuring the output_dir exists.
    """
    output_dir = output_dir or os.getcwd()
    # Create output directory if it doesn't exist
    os.makedirs(output_dir, exist_ok=True)
    if not os.access(output_dir, os.W_OK):
        raise PermissionError(f"Output directory not writable: {output_dir}")

    try:
        if use_func_names:
            subprocess.run(
            [
                "bindiff",
                "--primary", primary,
                "--secondary", secondary,
                "--output_dir", output_dir
            ],
            check=True,
            capture_output=True,
            text=True
            )
        else:
            config_path = os.path.join(os.path.dirname(os.path.abspath(__file__)),"bindiff_configs", "exclude_function_names.json")
            subprocess.run(
                [
                    "bindiff",
                    "--config", config_path,
                    "--primary", primary,
                    "--secondary", secondary,
                    "--output_dir", output_dir
                ],
                check=True,
                capture_output=True,
                text=True
            )
    except subprocess.CalledProcessError as e:
        return {}

    base1 = os.path.splitext(os.path.basename(primary))[0]
    base2 = os.path.splitext(os.path.basename(secondary))[0]
    expected = os.path.join(output_dir, f"{base1}_vs_{base2}.BinDiff")
    if not os.path.isfile(expected):
        raise FileNotFoundError(f"Expected .BinDiff not found: {expected}")
    return _parse_bindiff_to_dict(primary_oid, primary, secondary_oid, secondary, expected)

def _parse_bindiff_to_dict(primary_oid, primary_binexp, secondary_oid, secondary_binexp, bindiff_file):
    """
    Parse a .BinDiff database and return exhaustive statistics
    in a JSON-serialisable dict.
    """
    diff = BinDiff.from_binexport_files(primary_binexp, secondary_binexp, bindiff_file)
    primary_header = api.get_field("object_header", primary_oid, primary_oid)
    secondary_header = api.get_field("object_header", secondary_oid, secondary_oid)

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
        primary_f_offset = get_file_offset(int(f1.addr), primary_header, LOAD_ADDR)
        secondary_f_offset = get_file_offset(int(f2.addr), secondary_header, LOAD_ADDR)
        fun_matches[(primary_f_offset, secondary_f_offset)] = {
            "similarity":        fm.similarity,
            "confidence":        fm.confidence,
            "algorithm": {
                "id": fm.algorithm, 
                "name": function_algorithm_str(fm.algorithm),
            },
            "functions": {
                "primary": {
                    "address": primary_f_offset,
                    "name": f1.name
                },
                "secondary": {
                    "address": secondary_f_offset,
                    "name": f2.name,
                }
            },
        }

        # update aggregates
        agg["matched_functions"]     += 1

    # 3. unmatched functions
    unmatched_primary = []
    for f in diff.primary_unmatched_function():
        primary_f_offset = get_file_offset(int(f.addr), primary_header, LOAD_ADDR)
        unmatched_primary.append({"address": primary_f_offset, "name": f.name})

    unmatched_secondary = []
    for f in diff.secondary_unmatched_function():
        secondary_f_offset = get_file_offset(int(f.addr), secondary_header, LOAD_ADDR)
        unmatched_secondary.append({"address": secondary_f_offset, "name": f.name})

    # 4. wrap-up
    file_stats.update(agg)
    return {
        "file_stats":        file_stats,
        "function_matches":  fun_matches,
        "unmatched_primary": unmatched_primary,
        "unmatched_secondary": unmatched_secondary,
    }