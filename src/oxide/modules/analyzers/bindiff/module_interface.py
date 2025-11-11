#!/usr/bin/env python3
"""
BinDiff analyzer module for pairing target and baseline binary files using BinDiff.
Refined for clarity, reduced duplication, enhanced error handling, and logging.
"""
import logging
from typing import Dict, Any, List

from oxide.core import api
from export_bindiff import run_bindiff, run_ghidra_binexport
import os
import tempfile

# Module metadata
DESC = "Analyzer module to compute BinDiff between two binaries."
NAME = "bindiff"

logger = logging.getLogger(NAME)

# Options documentation
opts_doc: Dict[str, Any] = {}

def documentation() -> Dict[str, Any]:
    """
    Returns module documentation.
    """
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }

def results(oid_list: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Entry point for the BinDiff analyzer.
    Expects exactly two OIDs: the baseline and the target.
    Computes differences using BinDiff and returns the results.
    """
    results = {}
    if len(oid_list) != 2:
        logger.error("Expected exactly two OIDs: baseline and target, got %d", len(oid_list))
        return {}

    target_oid = oid_list[0]
    baseline_oid = oid_list[1]

    if api.exists(NAME, target_oid):
        data = api.retrieve(NAME, target_oid)
        if baseline_oid in data:
            return data[baseline_oid]

    try:
        baseline_export = get_or_create_binexport(baseline_oid)
        target_export = get_or_create_binexport(target_oid)

        results = run_bindiff(target_oid, target_export, baseline_oid, baseline_export, api.scratch_dir)
    except Exception:
        logger.exception("BinDiff execution failed for OIDs %s and %s", target_oid, baseline_oid)
        return {}
    if api.exists(NAME, target_oid):
        data = api.retrieve(NAME, target_oid)
        data[baseline_oid] = results
        api.store(NAME, target_export, data)
    else:
        api.store(NAME, target_oid, {target_oid: results})
    return results

def get_or_create_binexport(oid: str) -> str:
    """
    Retrieves or generates a BinExport file for the given OID.
    Caches the result in the API store under NAME.
    """
    # Return cached export if exists
    if api.exists(NAME, oid):
        cached = api.get_field(NAME, oid, oid)
        return api.tmp_file(f"{NAME}_{oid}", cached)

    # Generate via Ghidra
    ghidra_path = api.ghidra_path
    scripts_dir = api.scripts_dir

    binary_path = write_temp_file_for_oid(oid)
    binexport_path = run_ghidra_binexport(ghidra_path, binary_path, api.scratch_dir, scripts_dir)
    cache_binexport(oid, binexport_path)
    return binexport_path

def write_temp_file(data: bytes, descriptor: str) -> str:
    """
    Write bytes data to a temporary file. Return the file path.
    """
    suffix = os.path.splitext(descriptor)[1] or ""
    with tempfile.NamedTemporaryFile(prefix=f"{descriptor}_", suffix=suffix, delete=False) as tmp:
        tmp.write(data)
        tmp.flush()
        return tmp.name

def write_temp_file_for_oid(oid: str) -> str:
    """
    Extract binary data for the given OID, write to a temp file, and return its path.
    """
    src = api.source(oid)
    data = api.get_field(src, oid, "data")
    if not data:
        raise ValueError(f"No data found for OID {oid}")

    names = api.get_field("file_meta", oid, "names") or {}
    filename = names.pop() if names else oid
    return write_temp_file(data, descriptor=filename)

def cache_binexport(oid: str, path: str) -> None:
    """
    Cache the BinExport file content in the API store.
    """
    with open(path, "rb") as f:
        content = f.read()
    api.store(NAME, oid, {oid: content})
