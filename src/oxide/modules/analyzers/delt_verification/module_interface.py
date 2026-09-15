DESC = "Three-phase DeLT analyzer: bounded, binary context, and unbounded."

import logging

from typing import Any, Dict, List

from oxide.core import api
from oxide.modules.analyzers.delt_verification.pipeline.orchestrator import run_comparison
from oxide.modules.analyzers.delt_verification.config import NAME
from oxide.modules.analyzers.delt_verification.pipeline.utils.resolve import (
    resolve_artifact_root,
    resolve_collection_pair,
)

logger = logging.getLogger(NAME)
logging.getLogger("httpx").setLevel(logging.WARNING)
logger.setLevel(logging.INFO)
logger.debug("init")

opts_doc = {
    "filter": {"type": str, "mangle": True, "default": "Call_OR_Control_Modified"},
    "diff_mode": {"type": str, "mangle": True, "default": "processed"},
    "model": {"type": str, "mangle": True, "default": ""},
    # Which Ollama server to use. Not mangled: the same candidate analyzed on another
    # endpoint is the same result, so the endpoint must not split the cache.
    "ollama_base_url": {"type": str, "mangle": False, "default": ""},
    "bounded_prompt_file": {"type": str, "mangle": True, "default": "bounded.yaml"},
    "bounded_with_callees_prompt_file": {"type": str, "mangle": True, "default": "bounded_with_callees.yaml"},
    "unbounded_prompt_file": {"type": str, "mangle": True, "default": "unbounded_agent.yaml"},
    "unbounded_no_report_prompt_file": {"type": str, "mangle": True, "default": "unbounded_no_report.yaml"},
    "bounded_request_s": {"type": float, "mangle": True, "default": 1000.0},
    # Measured over 225 bounded model calls: median 2.3s, p99 66.4s, with a thin tail. The
    # longest observed generation needed 153.5s, so 90 clipped roughly 1% of calls mid-
    # response. Matches unbounded's per-call budget.
    "bounded_model_call_s": {"type": float, "mangle": True, "default": 180.0},
    "unbounded_request_s": {"type": float, "mangle": True, "default": 1000.0},
    "unbounded_model_call_s": {"type": float, "mangle": True, "default": 180.0},
    # Greedy decoding. The model ships temperature 1, so this has to be set or runs sample.
    # Every other sampling and runtime option is left to the model and to Ollama.
    "temperature": {"type": float, "mangle": True, "default": 0.0},
    "seed": {"type": int, "mangle": True, "default": 1},
    "raw": {"type": bool, "mangle": True, "default": False},
    "no_bounded": {"type": bool, "mangle": True, "default": False},
    "skip_bounded": {"type": bool, "mangle": True, "default": False},
    "skip_unbounded": {"type": bool, "mangle": True, "default": False},
    "no_bounded_report": {"type": bool, "mangle": True, "default": False},
    "include_added_callees": {"type": bool, "mangle": True, "default": True},
    "outdir": {"type": str, "mangle": True, "default": ""},
    "ground_truth": {"type": str, "mangle": True, "default": ""},
    "gt_only": {"type": bool, "mangle": True, "default": False},
    "_cache_kind": {"type": str, "mangle": True, "default": ""},
    "_cache_fingerprint": {"type": str, "mangle": True, "default": ""},
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
