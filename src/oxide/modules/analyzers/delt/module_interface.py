DESC = "DeLT single-comparison analyzer for paper-facing backdoor triage metrics."

import logging

from typing import Any, Dict, List

from oxide.core import api
from oxide.modules.analyzers.delt.pipeline.analyze import run_comparison
from oxide.modules.analyzers.delt.config import NAME
from oxide.modules.analyzers.delt.pipeline.utils.resolve import resolve_artifact_root, resolve_collection_pair

logger = logging.getLogger(NAME)
logging.getLogger("httpx").setLevel(logging.WARNING)
logger.setLevel(logging.INFO)
logger.debug("init")

opts_doc = {
    "filter": {"type": str, "mangle": True, "default": "Call_OR_Control_Modified"},
    "diff_mode": {"type": str, "mangle": True, "default": "processed"},
    "model": {"type": str, "mangle": True, "default": ""},
    "agent_prompt_file": {"type": str, "mangle": True, "default": "agent.yaml"},
    "agent_callee_prompt_file": {"type": str, "mangle": True, "default": "agent_with_callees.yaml"},
    "agent_request_s": {"type": float, "mangle": True, "default": 150.0},
    "raw": {"type": bool, "mangle": True, "default": False},
    "no_triage": {"type": bool, "mangle": True, "default": False},
    "include_added_callees": {"type": bool, "mangle": True, "default": True},
    "outdir": {"type": str, "mangle": True, "default": ""},
    "ground_truth": {"type": str, "mangle": True, "default": ""},
}


def documentation() -> Dict[str, Any]:
    """ Documentation for this module
        private - Whether module shows up in help
        set - Whether this module accepts collections
        atomic - TBD
    """
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True}


def results(oid_list: List[str], opts: dict) -> Dict[str, Any]:
    """ Run DeLT over every modified function between two collections.
        oid_list must be [target_oid, baseline_oid].
    """
    logger.debug("process()")

    target_oid, baseline_oid = resolve_collection_pair(list(oid_list))
    outdir = resolve_artifact_root(target_oid, baseline_oid, opts)
    try:
        target_name = api.get_colname_from_oid(target_oid)
    except Exception:
        target_name = str(target_oid)
    try:
        baseline_name = api.get_colname_from_oid(baseline_oid)
    except Exception:
        baseline_name = str(baseline_oid)

    result = run_comparison(target_oid, baseline_oid, outdir, dict(opts))
    result["artifact_root"] = outdir
    return result
