#!/usr/bin/env python3
"""
BinDiff analyzer module for pairing target and baseline binary files using BinDiff.
"""

import logging
from typing import Dict, Any, List, Tuple

from oxide.core import api
from export_bindiff import run_bindiff, run_ghidra_binexport
import os

# Module metadata
desc = "Analyzer module to compute BinDiff between two firmware binaries."
name = "bindiff"

logger = logging.getLogger(name)
logger.debug("Initializing BinDiff analyzer module")

# Options documentation
tps_doc: Dict[str, Any] = {}


def documentation() -> Dict[str, Any]:
    """
    Returns module documentation.

    :returns: dict containing description, option docs, and visibility flags.
    """
    return {
        "description": desc,
        "opts_doc": tps_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }

def results(oid_list: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Entry point for the BinDiff analyzer.

    Expects exactly two OIDs: the target and the baseline. Computes differences
    using BinDiff and returns the results.
    """
    # Validate input
    if len(oid_list) != 2:
        logger.error("Expected exactly two OIDs: target and baseline.")
        return {}

    target_oid, baseline_oid = oid_list

    # Prepare temporary files
    try:
        target_tmp, _ = _prepare_temp_file(target_oid)
        baseline_tmp, _ = _prepare_temp_file(baseline_oid)
    except ValueError as e:
        logger.error(str(e))
        return {}

    # Run BinDiff
    try:
        ghidra_path = api.ghidra_path
        script_path = api.scripts_dir
        scratch_dir = api.scratch_dir

        baseline_binexport = run_ghidra_binexport(ghidra_path, baseline_tmp, scratch_dir, script_path)
        target_binexport = run_ghidra_binexport(ghidra_path, target_tmp, scratch_dir, script_path)

        diff_results = run_bindiff(baseline_binexport, target_binexport, scratch_dir)
    except Exception as e:
        logger.exception("BinDiff execution failed")
        return {}

    return diff_results or {}

def _prepare_temp_file(oid: str) -> Tuple[str, Any]:
    """
    Retrieves binary data for the given OID, writes it to a temporary file,
    and returns the temporary file path along with its header.

    :param oid: Object ID in the database.
    :raises ValueError: If data, header, or filename cannot be retrieved.
    :returns: (tmp_file_path, header)
    """
    # Retrieve data field
    src = api.source(oid)
    data = api.get_field(src, oid, "data", {})
    if not data:
        raise ValueError(f"No data available for OID {oid}")

    # Retrieve header for metadata
    header = api.get_field("object_header", oid, oid)
    if not header:
        raise ValueError(f"No header available for OID {oid}")

    # Retrieve filename metadata
    names = api.get_field("file_meta", oid, "names") or []
    if not names:
        raise ValueError(f"No filenames found for OID {oid}")
    original_name = names.pop()

    # Write to temporary file
    tmp_path = api.tmp_file(original_name, data)
    return tmp_path, header
