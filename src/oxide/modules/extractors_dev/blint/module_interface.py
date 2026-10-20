"""
Runs blint and returns the findings.

Configuring this module.
# macOS (Homebrew)
brew install llvm@20 zstd
export NYXSTONE_LLVM_PREFIX=$(brew --prefix llvm@20)
export CFLAGS="-std=c++17" CXXFLAGS="-std=c++17" LDFLAGS="-L$(brew --prefix)/lib"

# Linux (Debian/Ubuntu)
sudo apt install llvm-20-dev libzstd-dev libxml2-dev zlib1g-dev
export NYXSTONE_LLVM_PREFIX=/usr/lib/llvm-20

uv sync --extra blint

# For all of the extra features. NOTE: This db is massive.
uv run blint db --download
"""

DESC = "Runs blint and returns the recovered Nosbom."
NAME = "blint"

import json
import logging
import os
from typing import Any

from blint.config import BlintOptions
from blint.db import is_supported_blintdb
from blint.lib.sbom import generate
from oxide.core import api

logging.basicConfig(level=logging.WARNING)
logging.getLogger().setLevel(logging.WARNING)

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> dict[str, Any]:
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }


def process(oid: str, opts: dict) -> bool:
    logger.debug("process()")

    if not is_supported_blintdb():
        logger.warning(
            "blintdb is not installed or not supported. Please look at the blint module documentation for installation instructions."
        )
    result = {}

    header = api.get_field("object_header", oid, oid)
    if not header:
        logger.warning("No header found for %s in %s", oid, NAME)
        return False

    src = api.source(oid)
    if src is None:
        logger.warning("No source found for %s", oid)
        return False

    data = api.get_field(src, oid, "data")
    if data is None:
        logger.warning("No data found for %s", oid)
        return False

    names = api.get_field("file_meta", oid, "names")
    if names is None:
        logger.warning("No file names found for %s", oid)
        return False

    f_name = names.pop()
    file = api.tmp_file(f_name, data)
    if file is None:
        logger.warning("File creation failed for %s", oid)
        return False

    sbom_path = os.path.join(api.scratch_dir, f"{oid}.cdx.json")
    blint_options = BlintOptions(
        sbom_mode=True,
        src_dir_image=[os.path.dirname(file)],
        sbom_output=sbom_path,
        deep_mode=True,
        use_blintdb=True,
        quiet_mode=True,
    )
    sbom_status = generate(blint_options, [file], [])
    if sbom_status:
        with open(sbom_path) as f:
            result["sbom"] = json.load(f)
        os.remove(sbom_path)

    if result is None: return False
    api.store(NAME, oid, result, opts)
    return True
