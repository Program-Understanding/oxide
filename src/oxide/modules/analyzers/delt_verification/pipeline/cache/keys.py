import hashlib
import json
from typing import Any, Dict, Optional


def bounded_opts_fingerprint(
    opts: Dict[str, Any], prompt_bundle: Optional[Dict[str, Any]] = None
) -> str:
    tracked_opts = {
        key: opts.get(key)
        for key in (
            "model",
            "filter",
            "diff_mode",
            "raw",
            "no_bounded",
            "include_added_callees",
            "bounded_request_s",
            "bounded_model_call_s",
            "temperature",
            "seed",
        )
    }
    prompts = {}
    if prompt_bundle:
        for name in ("bounded", "bounded_with_callees"):
            cfg = prompt_bundle.get(name) or {}
            prompts[name] = {"system": cfg.get("system"), "schema": cfg.get("schema")}
    blob = json.dumps({"opts": tracked_opts, "prompts": prompts}, sort_keys=True, default=str)
    return hashlib.sha1(blob.encode("utf-8")).hexdigest()[:16]


def unbounded_opts_fingerprint(
    opts: Dict[str, Any], prompt_bundle: Optional[Dict[str, Any]] = None
) -> str:
    tracked_opts = {
        key: opts.get(key)
        for key in (
            "model",
            "filter",
            "diff_mode",
            "raw",
            "include_added_callees",
            "unbounded_request_s",
            "unbounded_model_call_s",
            "temperature",
            "seed",
        )
    }
    # no_bounded_report is deliberately not tracked. Its only effect is blanking the claim,
    # and unbounded_inputs_digest below already hashes the claim, so tracking it here
    # would split the cache between arms that send the agent an identical request.
    prompts = {}
    if prompt_bundle:
        for name in (
            "bounded",
            "bounded_with_callees",
            "unbounded",
            "unbounded_no_report",
        ):
            cfg = prompt_bundle.get(name) or {}
            prompts[name] = {"system": cfg.get("system"), "schema": cfg.get("schema")}
    blob = json.dumps({"opts": tracked_opts, "prompts": prompts}, sort_keys=True, default=str)
    return hashlib.sha1(blob.encode("utf-8")).hexdigest()[:16]


def bounded_result_cache_key(
    target_oid: str,
    baseline_oid: str,
    baseline_addr: str,
    target_addr: str,
    fingerprint: str,
) -> str:
    return f"bounded_{target_oid}_{baseline_oid}_{baseline_addr}_{target_addr}_{fingerprint}"


def unbounded_inputs_digest(
    bounded_report_md: str, callee_texts: Optional[Dict[str, str]] = None
) -> str:
    """Digest of the evidence handed to the unbounded agent.

    The opts fingerprint pins how the report was produced, not what it says, and two runs
    at the same fingerprint can still hand the agent different documents: an arm that
    withholds the report, or one with no bounded stage at all, supplies an empty claim where
    another supplies a real one. Folding the report text into the key means a verdict is
    replayed only when the agent would read byte-identical inputs, which is also what lets
    arms that send identical requests share a cached investigation.
    """
    blob = json.dumps(
        {"bounded_report_md": bounded_report_md, "callee_texts": callee_texts or {}},
        sort_keys=True,
        default=str,
    )
    return hashlib.sha1(blob.encode("utf-8")).hexdigest()[:16]


def unbounded_result_cache_key(
    target_oid: str,
    baseline_oid: str,
    baseline_addr: str,
    target_addr: str,
    fingerprint: str,
    inputs_digest: str,
) -> str:
    return (
        f"unbounded_{target_oid}_{baseline_oid}_{baseline_addr}_{target_addr}"
        f"_{fingerprint}_{inputs_digest}"
    )


