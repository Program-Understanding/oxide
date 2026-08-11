import hashlib
import json
from typing import Any, Dict, Optional


def triage_opts_fingerprint(
    opts: Dict[str, Any], prompt_bundle: Optional[Dict[str, Any]] = None
) -> str:
    tracked_opts = {
        key: opts.get(key)
        for key in (
            "model",
            "filter",
            "diff_mode",
            "raw",
            "no_triage",
            "include_added_callees",
        )
    }
    prompts = {}
    if prompt_bundle:
        for name in ("triage", "triage_with_callees"):
            cfg = prompt_bundle.get(name) or {}
            prompts[name] = {"system": cfg.get("system"), "schema": cfg.get("schema")}
    blob = json.dumps({"opts": tracked_opts, "prompts": prompts}, sort_keys=True, default=str)
    return hashlib.sha1(blob.encode("utf-8")).hexdigest()[:16]


def verification_opts_fingerprint(
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
            "verification_request_s",
            "verification_model_call_s",
        )
    }
    prompts = {}
    if prompt_bundle:
        for name in ("triage", "triage_with_callees", "verification"):
            cfg = prompt_bundle.get(name) or {}
            prompts[name] = {"system": cfg.get("system"), "schema": cfg.get("schema")}
    blob = json.dumps({"opts": tracked_opts, "prompts": prompts}, sort_keys=True, default=str)
    return hashlib.sha1(blob.encode("utf-8")).hexdigest()[:16]


def binary_context_opts_fingerprint(
    opts: Dict[str, Any], prompt_bundle: Optional[Dict[str, Any]] = None
) -> str:
    tracked_opts = {
        key: opts.get(key)
        for key in (
            "model",
            "filter",
            "binary_context_request_s",
            "binary_context_model_call_s",
        )
    }
    prompts = {}
    if prompt_bundle:
        cfg = prompt_bundle.get("binary_context") or {}
        prompts["binary_context"] = {"system": cfg.get("system"), "schema": cfg.get("schema")}
    blob = json.dumps({"opts": tracked_opts, "prompts": prompts}, sort_keys=True, default=str)
    return hashlib.sha1(blob.encode("utf-8")).hexdigest()[:16]


def triage_result_cache_key(
    target_oid: str,
    baseline_oid: str,
    baseline_addr: str,
    target_addr: str,
    fingerprint: str,
) -> str:
    return f"triage_{target_oid}_{baseline_oid}_{baseline_addr}_{target_addr}_{fingerprint}"


def verification_inputs_digest(triage_report_md: str, binary_context_md: str) -> str:
    """Digest of the two reports handed to the verification agent.

    The opts fingerprint pins how the reports were produced, not what they say. Two runs
    at the same fingerprint can still hand the agent different documents: a binary-context
    run that timed out yields an empty report, and the retry that follows yields a real
    one. Folding the report text into the key means a verdict is only replayed when the
    agent would read byte-identical inputs, so a verdict reached without binary context is
    never reused once that context exists.
    """
    blob = json.dumps(
        {"triage_report_md": triage_report_md, "binary_context_md": binary_context_md},
        sort_keys=True,
        default=str,
    )
    return hashlib.sha1(blob.encode("utf-8")).hexdigest()[:16]


def verification_result_cache_key(
    target_oid: str,
    baseline_oid: str,
    baseline_addr: str,
    target_addr: str,
    fingerprint: str,
    inputs_digest: str,
) -> str:
    return (
        f"verification_{target_oid}_{baseline_oid}_{baseline_addr}_{target_addr}"
        f"_{fingerprint}_{inputs_digest}"
    )


def binary_context_cache_key(baseline_oid: str, fingerprint: str) -> str:
    """Keyed by the baseline alone: the report describes only that binary.

    The agent is handed the baseline OID and nothing about the target, so every pair
    sharing a baseline (a backdoored and a safe target against the same previous release)
    can reuse one report.
    """
    return f"binary_context_{baseline_oid}_{fingerprint}"
