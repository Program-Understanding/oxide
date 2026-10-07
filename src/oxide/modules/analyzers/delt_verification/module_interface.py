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
    # Budgets sized so the per-turn output cap below, not wall clock, is what bounds a
    # generation. One capped turn costs 468s at the 175 tok/s measured on this workload and
    # 680s at its 120.5 tok/s median, so the per-call cap sits above both and the run budget
    # holds two of them plus a normal investigation. The cap's remaining job is catching a
    # stalled call, since streaming makes the HTTP read timeout useless.
    "bounded_request_s": {"type": float, "mangle": True, "default": 1800.0},
    # Per-model-call cap, sized from the model's documented output length rather than from
    # the observed tail. Qwen3.6-35B-A3B recommends an output length of 32768 tokens, and
    # measured decode over 4849 calls of this workload is 120.5 tok/s median (identical in
    # both stages, so context size is not the driver), which needs 272s. The previous 180s
    # allowed ~21700 tokens -- below one recommended output -- and killed roughly 14% of
    # investigations in each stage. Completed calls ran to 173.1s with 0.25% past 150s and a
    # tail halving every ~30s, so the cap was clipping a live distribution, not stopping
    # non-terminating generations.
    "bounded_model_call_s": {"type": float, "mangle": True, "default": 900.0},
    "unbounded_request_s": {"type": float, "mangle": True, "default": 1800.0},
    "unbounded_model_call_s": {"type": float, "mangle": True, "default": 900.0},
    # Qwen3.6-35B-A3B's published sampling profile for thinking mode on precise coding
    # tasks. The Ollama model file ships the general-tasks profile instead, which differs in
    # temperature (1.0) and presence_penalty (1.5); reasoning over decompiled code is the
    # precise-coding case, and a presence penalty works against tool-call syntax, which has
    # to re-emit the same structural tokens on every call. Negative leaves an option unsent
    # so the model file value stands; >= 0 pins it.
    "temperature": {"type": float, "mangle": True, "default": 0.6},
    "top_p": {"type": float, "mangle": True, "default": 0.95},
    "top_k": {"type": int, "mangle": True, "default": 20},
    "min_p": {"type": float, "mangle": True, "default": 0.0},
    "presence_penalty": {"type": float, "mangle": True, "default": 0.0},
    "repeat_penalty": {"type": float, "mangle": True, "default": 1.0},
    "seed": {"type": int, "mangle": True, "default": -1},
    # Per-turn output cap. Qwen3.6-35B-A3B recommends an output length of 81920 tokens for
    # highly complex problems, and a turn on this workload has been observed attempting past
    # 52000, so bounding output at the published figure stops a runaway turn without
    # truncating one the model is documented to produce. Worst observed per-call prompt is
    # 52402 tokens, so this stays inside the 262144 context.
    "max_output_tokens": {"type": int, "mangle": True, "default": 81920},
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
