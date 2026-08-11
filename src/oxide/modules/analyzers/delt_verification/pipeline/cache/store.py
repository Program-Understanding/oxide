import hashlib
from typing import Any, Dict, Optional

from oxide.core import api


def stage_cache_opts(kind: str, fingerprint: str) -> Dict[str, Any]:
    return {"_cache_kind": kind, "_cache_fingerprint": fingerprint}


def _local_cache_namespace(kind: str, fingerprint: str) -> str:
    digest = hashlib.sha1(f"{kind}:{fingerprint}".encode("utf-8")).hexdigest()[:16]
    return f"delt_verification_cache_{kind}_{digest}"


def _local_cache_key(target_oid: str, cache_key: str) -> str:
    return f"{target_oid}:{cache_key}"


def load_cached_stage_result(
    target_oid: str, cache_opts: Dict[str, Any], cache_key: str
) -> Optional[Dict[str, Any]]:
    kind = str(cache_opts.get("_cache_kind") or "")
    fingerprint = str(cache_opts.get("_cache_fingerprint") or "")
    namespace = _local_cache_namespace(kind, fingerprint)
    key = _local_cache_key(target_oid, cache_key)
    if not api.local_exists(namespace, key):
        return None
    cached = api.local_retrieve(namespace, key)
    return dict(cached) if isinstance(cached, dict) else None


def store_cached_stage_result(
    target_oid: str, cache_opts: Dict[str, Any], cache_key: str, value: Dict[str, Any]
) -> None:
    kind = str(cache_opts.get("_cache_kind") or "")
    fingerprint = str(cache_opts.get("_cache_fingerprint") or "")
    namespace = _local_cache_namespace(kind, fingerprint)
    key = _local_cache_key(target_oid, cache_key)
    api.local_store(namespace, key, dict(value))
