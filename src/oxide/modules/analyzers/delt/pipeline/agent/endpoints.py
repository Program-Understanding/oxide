"""Per-function Ollama endpoint provisioning for the delt analyzer.

When function_workers > 1, delt fans functions across one Ollama server per GPU. The
servers are launched lazily and cached for the process (keyed by workers + base_port), so
they are reused across every comparison and model rather than relaunched per pair. Launch
and warmup are delegated to delt_three_stage.resolve_endpoints (the shared OllamaManager),
so the strategy stays identical to the three-stage pipeline.
"""
import atexit
import logging
import os
import threading
from typing import Any, Dict, List, Optional, Tuple

from oxide.modules.analyzers.delt.config import NAME

logger = logging.getLogger(NAME)

_DEFAULT_BASE_PORT = 11435

_POOL_LOCK = threading.Lock()
# (workers, base_port) -> (endpoints, manager)
_POOLS: Dict[Tuple[int, int], Tuple[List[str], Any]] = {}


def _explicit_endpoints(opts: Dict[str, Any]) -> List[str]:
    raw = opts.get("ollama_base_urls") or opts.get("endpoints") or os.getenv("DELT_ENDPOINTS")
    if isinstance(raw, (list, tuple)):
        return [str(u).strip() for u in raw if str(u).strip()]
    text = str(raw or "").strip()
    return [u.strip() for u in text.split(",") if u.strip()]


def resolve_function_endpoints(opts: Dict[str, Any]) -> List[str]:
    """Return the Ollama base URLs for per-function workers.

    An explicit endpoint list (opts 'ollama_base_urls'/'endpoints' or DELT_ENDPOINTS) wins.
    Otherwise, when function_workers > 1, lazily launch one server per GPU via
    delt_three_stage.resolve_endpoints and cache it for the process. Returns [] when
    function_workers <= 1 or when there are fewer GPUs than workers (shared-endpoint mode)."""
    explicit = _explicit_endpoints(opts)
    if explicit:
        return explicit

    workers = int(opts.get("function_workers") or 1)
    if workers <= 1:
        return []

    base_port = int(opts.get("ollama_base_port") or os.getenv("DELT_OLLAMA_BASE_PORT") or _DEFAULT_BASE_PORT)
    key = (workers, base_port)
    with _POOL_LOCK:
        cached = _POOLS.get(key)
        if cached is not None:
            return cached[0]
        # Lazy import: only pull the launcher in when multi-GPU fan-out is actually used.
        from oxide.plugins import delt_three_stage
        endpoints, manager = delt_three_stage.resolve_endpoints(opts, workers, base_port)
        _POOLS[key] = (endpoints, manager)
        if manager is not None:
            atexit.register(manager.shutdown)
        return endpoints
