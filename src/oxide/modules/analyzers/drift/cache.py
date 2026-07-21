from typing import Any, Callable

from oxide.core import api


def comparison_cache_key(target_oid: str, baseline_oid: str) -> str:
    return f"compare_{target_oid}_{baseline_oid}"


def function_diff_cache_key(target_oid: str, baseline_oid: str) -> str:
    return f"file_diff_{target_oid}_{baseline_oid}"


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
