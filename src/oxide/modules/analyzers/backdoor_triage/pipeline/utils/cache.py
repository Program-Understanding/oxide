import hashlib
import json
from typing import Any, Callable, Dict, Optional

from oxide.core import api


def get_or_compute(name: str, cache_key: str, compute: Callable[[], Any]) -> Any:
    """ Return the cached value for cache_key under the given local-datastore
        namespace, computing and storing it via compute() on a miss.
    """
    if api.local_exists(name, cache_key):
        cached = api.local_retrieve(name, cache_key)
        if isinstance(cached, dict):
            return cached

    value = compute()
    api.local_store(name, cache_key, value)
    return value


def opts_fingerprint(opts: Dict[str, Any], prompt_bundle: Optional[Dict[str, Any]] = None) -> str:
    """ Stable short hash over exactly the opts (and, if given, the prompt bundle's
        system/schema text) that affect triage output. Editing a prompt YAML changes
        model behavior exactly like changing an opt would, so folding prompt content
        in here means a prompt edit invalidates stale cached/filesystem results
        automatically instead of silently serving them.
    """
    tracked_opts = {
        key: opts.get(key)
        for key in (
            "model", "stage3_model", "filter", "raw",
            "stage1_only", "stage2_only", "no_triage", "include_added_callees",
        )
    }
    payload: Dict[str, Any] = {"opts": tracked_opts}
    if prompt_bundle:
        payload["prompts"] = {
            name: {"system": cfg.get("system"), "schema": cfg.get("schema")}
            for name, cfg in prompt_bundle.items()
        }
    blob = json.dumps(payload, sort_keys=True, default=str)
    return hashlib.sha1(blob.encode("utf-8")).hexdigest()[:16]


def comparison_cache_key(target_oid: str, baseline_oid: str, fingerprint: str) -> str:
    return f"compare_{target_oid}_{baseline_oid}_{fingerprint}"


def function_triage_cache_key(
    target_oid: str, baseline_oid: str, baseline_addr: str, target_addr: str, fingerprint: str
) -> str:
    return f"triage_{target_oid}_{baseline_oid}_{baseline_addr}_{target_addr}_{fingerprint}"
