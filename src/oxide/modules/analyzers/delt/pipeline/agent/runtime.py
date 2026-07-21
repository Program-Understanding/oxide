import logging
import threading
from dataclasses import dataclass
from typing import Any, Dict, Optional

from langchain_ollama import ChatOllama

from oxide.modules.analyzers.delt.config import NAME
from oxide.modules.analyzers.delt.pipeline.agent import agent_runtime
from oxide.modules.analyzers.delt.pipeline.utils.llm import load_prompt_bundle

logger = logging.getLogger(NAME)


@dataclass
class TriageRuntime:
    """Bundles the agent runtime so triage always runs against initialized clients."""

    agent_llm: ChatOllama
    agent_sys: str
    agent_sys_callee: str
    agent_request_timeout_s: float


RUNTIMES: Dict[str, TriageRuntime] = {}
RUNTIMES_LOCK = threading.Lock()


def _runtime_cache_key(opts: Dict[str, Any]) -> str:
    return "|".join(
        [
            str(opts["model"]),
            str(opts.get("ollama_base_url") or ""),
            str(opts.get("agent_prompt_file") or ""),
            str(opts.get("agent_callee_prompt_file") or ""),
            str(opts.get("agent_request_s") or ""),
        ]
    )


def _build_runtime(opts: Dict[str, Any]) -> TriageRuntime:
    model = str(opts["model"])
    # Optional per-run Ollama endpoint. Lets one experiment fan out across several
    # Ollama servers (e.g. one per GPU); None falls back to ChatOllama's default host.
    base_url = str(opts.get("ollama_base_url") or "").strip() or None
    prompts = load_prompt_bundle(opts)
    request_timeout_s = float(opts["agent_request_s"])

    return TriageRuntime(
        agent_llm=agent_runtime.make_agent_model(
            model, request_timeout_s=request_timeout_s, base_url=base_url
        ),
        agent_sys=prompts["agent"]["system"],
        agent_sys_callee=prompts["agent_callee"]["system"],
        agent_request_timeout_s=request_timeout_s,
    )


def _resolve_runtime_opts(opts: Optional[Dict[str, Any]]) -> Dict[str, Any]:
    resolved_opts = dict(opts or {})
    model = str(resolved_opts.get("model") or "").strip()
    if not model:
        raise ValueError(
            "delt requires an explicit 'model' opt (an Ollama model tag); "
            "no default model is configured."
        )
    resolved_opts["model"] = model
    resolved_opts["agent_request_s"] = float(resolved_opts.get("agent_request_s") or 150.0)
    return resolved_opts


def get_or_build_runtime(opts: Optional[Dict[str, Any]]) -> TriageRuntime:
    """Memoized by model + endpoint + prompt/timeout config for the triage pipeline."""
    resolved_opts = _resolve_runtime_opts(opts)
    cache_key = _runtime_cache_key(resolved_opts)
    with RUNTIMES_LOCK:
        runtime = RUNTIMES.get(cache_key)
        if runtime is None:
            runtime = _build_runtime(resolved_opts)
            RUNTIMES[cache_key] = runtime
        return runtime


def build_worker_runtime(opts: Optional[Dict[str, Any]], base_url: Optional[str] = None) -> TriageRuntime:
    """Build a fresh (non-memoized) runtime pinned to base_url, for per-function parallel
    workers. Each worker owns its own ChatOllama client, so concurrent function triage
    never shares a model client across threads."""
    resolved_opts = _resolve_runtime_opts(opts)
    resolved_opts["ollama_base_url"] = base_url
    return _build_runtime(resolved_opts)
