import hashlib
import json
from typing import Any, Dict, Optional

_SHARED_OPT_KEYS = ("model", "diff_mode", "raw", "include_added_callees",
                    "temperature", "seed", "top_p", "top_k", "min_p",
                    "presence_penalty", "repeat_penalty")


def _sha1_16(payload: Any) -> str:
    return hashlib.sha1(
        json.dumps(payload, sort_keys=True, default=str).encode("utf-8")
    ).hexdigest()[:16]


def _opts_fingerprint(
    opts: Dict[str, Any],
    prompt_bundle: Optional[Dict[str, Any]],
    *,
    opt_keys: tuple,
    prompt_names: tuple,
) -> str:
    """Hash the opts and prompts a stage's verdict depends on.

    Shared so an opt that affects both stages cannot be remembered in one list and
    forgotten in the other -- that failure mode replays a stale verdict rather than
    raising.
    """
    tracked_opts = {key: opts.get(key) for key in opt_keys}
    prompts = {}
    if prompt_bundle:
        for name in prompt_names:
            cfg = prompt_bundle.get(name) or {}
            prompts[name] = {"system": cfg.get("system"), "schema": cfg.get("schema")}
    return _sha1_16({"opts": tracked_opts, "prompts": prompts})


def bounded_opts_fingerprint(
    opts: Dict[str, Any], prompt_bundle: Optional[Dict[str, Any]] = None
) -> str:
    return _opts_fingerprint(
        opts,
        prompt_bundle,
        opt_keys=_SHARED_OPT_KEYS + ("no_bounded", "bounded_request_s", "bounded_model_call_s"),
        prompt_names=("bounded", "bounded_with_callees"),
    )


def unbounded_opts_fingerprint(
    opts: Dict[str, Any], prompt_bundle: Optional[Dict[str, Any]] = None
) -> str:
    # no_bounded_report is deliberately not tracked. Its only effect is blanking the claim,
    # and unbounded_inputs_digest below already hashes the claim, so tracking it here
    # would split the cache between arms that send the agent an identical request.
    return _opts_fingerprint(
        opts,
        prompt_bundle,
        opt_keys=_SHARED_OPT_KEYS + ("unbounded_request_s", "unbounded_model_call_s"),
        prompt_names=("bounded", "bounded_with_callees", "unbounded", "unbounded_no_report"),
    )


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
    return _sha1_16({"bounded_report_md": bounded_report_md, "callee_texts": callee_texts or {}})


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


