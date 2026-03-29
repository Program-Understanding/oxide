"""
Copyright 2023 National Technology & Engineering Solutions
of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS,
the U.S. Government retains certain rights in this software.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
"""

""" Wrapper for scripts for Ghidra, in which decompilation is associated with addresses
"""

import os
import subprocess
import json
import logging
import time
import shutil

from oxide.core.libraries.ghidra_utils import get_file_offset
from oxide.core import sys_utils

from typing import Dict, List, Optional, Tuple


NAME = "ghidra_decmap"
logger = logging.getLogger(NAME)
PYTHON_BACKEND = "python"
JAVA_BACKEND = "java"


def _log_file_contents(path: str, label: str, level: str = "info") -> None:
    if not path or not os.path.exists(path):
        logger.debug("%s not found: %s", label, path)
        return

    try:
        contents = sys_utils.get_contents_of_file(path).decode("utf-8", errors="replace").strip()
    except Exception:
        logger.exception("Failed to read %s: %s", label, path)
        return

    if not contents:
        logger.debug("%s is empty: %s", label, path)
        return

    log_fn = getattr(logger, level, logger.info)
    log_fn("%s (%s):\n%s", label, path, contents)


def _read_file_contents(path: str) -> str:
    if not path or not os.path.exists(path):
        return ""
    try:
        return sys_utils.get_contents_of_file(path).decode("utf-8", errors="replace")
    except Exception:
        logger.exception("Failed to read file contents: %s", path)
        return ""


def _load_backend_cache() -> Dict[str, str]:
    raw = _read_file_contents(GHIDRA_BACKEND_CACHE_FILE).strip()
    if not raw:
        return {}
    try:
        payload = json.loads(raw)
    except json.decoder.JSONDecodeError:
        logger.warning("Ignoring invalid Ghidra backend cache file: %s", GHIDRA_BACKEND_CACHE_FILE)
        return {}
    backends = payload.get("backend_by_ghidra_path")
    return backends if isinstance(backends, dict) else {}


def _store_backend_cache(backends: Dict[str, str]) -> None:
    payload = {"backend_by_ghidra_path": backends}
    try:
        with open(GHIDRA_BACKEND_CACHE_FILE, "w", encoding="utf-8") as cache_fp:
            json.dump(payload, cache_fp, indent=2, sort_keys=True)
    except Exception:
        logger.exception("Failed to write Ghidra backend cache file: %s", GHIDRA_BACKEND_CACHE_FILE)


def _get_cached_backend() -> Optional[str]:
    backend = _load_backend_cache().get(GHIDRA_PATH)
    if backend in (PYTHON_BACKEND, JAVA_BACKEND):
        return backend
    return None


def _set_cached_backend(backend: str) -> None:
    if backend not in (PYTHON_BACKEND, JAVA_BACKEND):
        return
    backends = _load_backend_cache()
    backends[GHIDRA_PATH] = backend
    _store_backend_cache(backends)
    logger.info("Cached Ghidra decmap backend '%s' for %s", backend, GHIDRA_PATH)


def _backend_order() -> List[str]:
    cached = _get_cached_backend()
    if cached == JAVA_BACKEND:
        return [JAVA_BACKEND, PYTHON_BACKEND]
    if cached == PYTHON_BACKEND:
        return [PYTHON_BACKEND, JAVA_BACKEND]
    return [PYTHON_BACKEND, JAVA_BACKEND]


def _script_name_for_backend(backend: str) -> str:
    if backend == JAVA_BACKEND:
        return JAVA_EXPORT_SCRIPT_PATH
    return PYTHON_EXPORT_SCRIPT_PATH


def _log_paths_for_backend(backend: str) -> Tuple[str, str]:
    suffix = ".{}".format(backend)
    return GHIDRA_SCRIPT_LOG_FILE + suffix, GHIDRA_LOG_FILE + suffix


def _script_dir_for_backend(backend: str) -> str:
    return os.path.join(GHIDRA_Project_PATH, "ghidra_decmap_scripts", backend)


def _cleanup_artifacts(paths: List[str]) -> None:
    for path in paths:
        if path and os.path.exists(path):
            sys_utils.delete_file(path)


def _backend_error_text(stdout: str, stderr: str, script_log: str, app_log: str) -> str:
    return "\n".join(part for part in (stdout, stderr, script_log, app_log) if part).lower()


def _python_unavailable(error_text: str) -> bool:
    return "python is not available" in error_text or "ghidra was not started with pyghidra" in error_text


def _prepare_script_dir(backend: str) -> Optional[str]:
    script_name = _script_name_for_backend(backend)
    source_script_path = os.path.join(SCRIPTS_PATH, script_name)
    if not os.path.exists(source_script_path):
        logger.warning("Missing %s backend script: %s", backend, source_script_path)
        return None

    script_dir = _script_dir_for_backend(backend)
    os.makedirs(script_dir, exist_ok=True)
    dest_script_path = os.path.join(script_dir, script_name)

    try:
        shutil.copy2(source_script_path, dest_script_path)
    except Exception:
        logger.exception("Failed to prepare isolated script dir for %s backend", backend)
        return None

    logger.info("Prepared isolated Ghidra script dir for %s backend: %s", backend, script_dir)
    return script_dir


def _run_ghidra_script(file_test: str, backend: str) -> Optional[str]:
    script_name = _script_name_for_backend(backend)
    script_dir = _prepare_script_dir(backend)
    if not script_dir:
        return None
    script_log_file, app_log_file = _log_paths_for_backend(backend)
    _cleanup_artifacts([GHIDRA_TMP_FILE, script_log_file, app_log_file])

    cmd = "{} {} {} ".format(GHIDRA_PATH, GHIDRA_Project_PATH, GHIDRA_Project_NAME) + \
          "-import {} -overwrite -scriptPath {} ".format(file_test, script_dir)   + \
          "-scriptlog {} -log {} ".format(script_log_file, app_log_file) + \
          "-postScript {} {}".format(script_name, GHIDRA_TMP_FILE)
    logger.info("Running Ghidra headless command with %s backend: %s", backend, cmd)

    try:
        completed = subprocess.run(
            cmd,
            shell=True,
            text=True,
            capture_output=True,
            check=False,
        )
    except Exception:
        logger.exception("Failed to launch Ghidra headless command for %s backend", backend)
        return None

    stdout = (completed.stdout or "").strip()
    stderr = (completed.stderr or "").strip()
    script_log = _read_file_contents(script_log_file).strip()
    app_log = _read_file_contents(app_log_file).strip()

    if stdout:
        logger.info("Ghidra stdout (%s backend):\n%s", backend, stdout)
    if stderr:
        logger.warning("Ghidra stderr (%s backend):\n%s", backend, stderr)

    logger.info("Ghidra headless command return code (%s backend): %d", backend, completed.returncode)
    if script_log:
        logger.info("Ghidra script log (%s backend, %s):\n%s", backend, script_log_file, script_log)
    if app_log:
        logger.info("Ghidra application log (%s backend, %s):\n%s", backend, app_log_file, app_log)

    if completed.returncode != 0:
        logger.error("Ghidra headless command exited with return code %d for %s backend", completed.returncode, backend)
        return None

    tmp_exists = os.path.exists(GHIDRA_TMP_FILE)
    logger.info("Ghidra temp output file exists after %s backend run: %s (%s)", backend, tmp_exists, GHIDRA_TMP_FILE)
    if tmp_exists:
        logger.info("Ghidra headless command completed successfully using %s backend", backend)
        return backend

    error_text = _backend_error_text(stdout, stderr, script_log, app_log)
    if backend == PYTHON_BACKEND and _python_unavailable(error_text):
        logger.warning("Python backend is unavailable in this Ghidra environment; falling back to Java backend")
    else:
        logger.error("Ghidra completed with %s backend but did not create output file: %s", backend, GHIDRA_TMP_FILE)
    return None


def extract_ghidra_decmap(file_test: str) -> Optional[str]:
    """ Run ghidra with arguments populated to execute script
    """
    for backend in _backend_order():
        logger.info("Attempting ghidra_decmap extraction using %s backend", backend)
        if not os.path.exists(os.path.join(SCRIPTS_PATH, _script_name_for_backend(backend))):
            logger.warning("Skipping missing %s backend script: %s", backend, _script_name_for_backend(backend))
            continue

        successful_backend = _run_ghidra_script(file_test, backend)
        if successful_backend:
            _set_cached_backend(successful_backend)
            return successful_backend

    logger.error("All Ghidra decmap backends failed to produce output")
    return None


def extract(file_test: str, header: dict, org_by_func: bool) -> dict:
    """ Runs instruction extraction from ghidraHEADLESS using a java language script
        Input -
            file_test - temporary file name to analyze
            header_interface (header) - header object using header utility lib
            org_by_func - organize output mapping by function, then offset? (default: no)
    """
    output_map = {}
    output_map["meta"] = {}

    if not header.known_format:
        logger.info("File Sample is of unknown format, Ghidra returning empty output.")
        return None

    start = time.time()

    # Collect stdout from ghidra script to parse
    backend = extract_ghidra_decmap(file_test)
    if backend is None:
        logger.error("Ghidra decompiler mapping extraction failed before temp file could be parsed")
        return None

    # parse output file
    try:
        raw = sys_utils.get_contents_of_file(GHIDRA_TMP_FILE).decode("utf-8")
    except AttributeError:
        logger.error("Ghidra temp output file was expected but not found: %s", GHIDRA_TMP_FILE)
        return None

    output_map['decompile'] = {}
    try:
        mapping = json.loads(raw)
        LOAD_ADDR = mapping['meta']['load_addr']
        LOAD_ADDR = int(LOAD_ADDR, 16)

        del mapping['meta']

        for func in mapping:
            # If organizing by function, add empty dict at func dimension
            if org_by_func:
                output_map['decompile'][func] = {}
            for addr in mapping[func]:
                # If organizing by function, include all elements for each function, even those associated with "None" address
                if org_by_func:
                    if addr != 'None':
                        output_map['decompile'][func][get_file_offset(int(addr, 16), header, LOAD_ADDR)] = mapping[func][addr]
                    else:
                        output_map['decompile'][func][addr] = mapping[func][addr]
                # Otherwise, filter out lines associated with "None" address and don't include func dimension (default behavior)
                else:
                    if addr != 'None':
                        output_map['decompile'][get_file_offset(int(addr, 16), header, LOAD_ADDR)] = mapping[func][addr]
    except json.decoder.JSONDecodeError:
        logger.info("Json decoding error encountered on Ghidra tmp file.")
        return None

    # Clean up temp file
    logger.debug("Removing tmp file")
    sys_utils.delete_file(GHIDRA_TMP_FILE) 
    script_log_file, app_log_file = _log_paths_for_backend(backend)
    _cleanup_artifacts([script_log_file, app_log_file])

    end = time.time()
    output_map["meta"]["time"] = end - start

    return output_map
