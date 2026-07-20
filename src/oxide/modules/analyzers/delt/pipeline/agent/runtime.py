import logging
import threading
from dataclasses import dataclass
from typing import Any, Dict, Optional

from langchain_ollama import ChatOllama

from oxide.modules.analyzers.delt.config import NAME
from oxide.modules.analyzers.delt.pipeline.agent.graph import build_triage_graph
from oxide.modules.analyzers.delt.pipeline.agent import agent_runtime
from oxide.modules.analyzers.delt.pipeline.utils.llm import load_prompt_bundle

logger = logging.getLogger(NAME)


@dataclass
class TriageRuntime:
    """Bundles the stage-1/stage-2 runtime so triage always runs against initialized clients."""

    stage1_llm: ChatOllama
    stage1_sys: str
    stage1_schema: Dict[str, Any]
    stage2_llm: ChatOllama
    stage2_sys: str
    stage2_sys_callee: str
    stage2_request_timeout_s: float
    graph: Any


RUNTIMES: Dict[str, TriageRuntime] = {}
RUNTIMES_LOCK = threading.Lock()


def _runtime_cache_key(opts: Dict[str, Any]) -> str:
    return "|".join(
        [
            str(opts["model"]),
            str(opts.get("ollama_base_url") or ""),
            str(opts.get("stage1_prompt_file") or ""),
            str(opts.get("stage2_prompt_file") or ""),
            str(opts.get("stage2_callee_prompt_file") or ""),
            str(opts.get("stage2_request_s") or ""),
            str(opts.get("stage1_client_request_s") or ""),
        ]
    )


def _build_runtime(opts: Dict[str, Any]) -> TriageRuntime:
    model = str(opts["model"])
    # Optional per-run Ollama endpoint. Lets one experiment fan out across several
    # Ollama servers (e.g. one per GPU); None falls back to ChatOllama's default host.
    base_url = str(opts.get("ollama_base_url") or "").strip() or None
    prompts = load_prompt_bundle(opts)
    stage1_sys = prompts["stage1"]["system"]
    stage1_schema = prompts["stage1"].get("schema") or {}
    stage2_sys = prompts["stage2"]["system"]
    stage2_sys_callee = prompts["stage2_callee"]["system"]

    stage1_llm = ChatOllama(
        model=model,
        base_url=base_url,
        temperature=0.0,
        keep_alive="10m",
        request_timeout=float(opts["stage1_client_request_s"]),
        format=stage1_schema,
        model_kwargs={"num_predict": 512},
    )
    stage2_llm = agent_runtime.make_agent_model(
        model, request_timeout_s=float(opts["stage2_request_s"]), base_url=base_url
    )

    runtime = TriageRuntime(
        stage1_llm=stage1_llm,
        stage1_sys=stage1_sys,
        stage1_schema=stage1_schema,
        stage2_llm=stage2_llm,
        stage2_sys=stage2_sys,
        stage2_sys_callee=stage2_sys_callee,
        stage2_request_timeout_s=float(opts["stage2_request_s"]),
        graph=None,
    )
    setattr(runtime.stage1_llm, "_oxide_stage1_token_timeout_s", float(opts["stage1_token_s"]))
    setattr(runtime.stage1_llm, "_oxide_stage1_total_timeout_s", float(opts["stage1_total_s"]))
    runtime.graph = build_triage_graph(runtime)
    return runtime


def _resolve_runtime_opts(opts: Optional[Dict[str, Any]]) -> Dict[str, Any]:
    resolved_opts = dict(opts or {})
    model = str(resolved_opts.get("model") or "").strip()
    if not model:
        raise ValueError(
            "delt requires an explicit 'model' opt (an Ollama model tag); "
            "no default model is configured."
        )
    resolved_opts["model"] = model
    resolved_opts["stage2_request_s"] = float(resolved_opts.get("stage2_request_s") or 150.0)
    resolved_opts["stage1_token_s"] = float(resolved_opts.get("stage1_token_s") or 30.0)
    resolved_opts["stage1_total_s"] = float(resolved_opts.get("stage1_total_s") or 300.0)
    resolved_opts["stage1_client_request_s"] = float(resolved_opts.get("stage1_client_request_s") or 180.0)
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
    workers. Each worker owns its own ChatOllama clients and compiled graph, so concurrent
    function triage never shares a graph or checkpointer across threads."""
    resolved_opts = _resolve_runtime_opts(opts)
    resolved_opts["ollama_base_url"] = base_url
    return _build_runtime(resolved_opts)
