import logging
import threading
from dataclasses import dataclass
from typing import Any, Dict, Optional

from langchain_ollama import ChatOllama

from oxide.modules.analyzers.delt_verification.config import NAME
from oxide.modules.analyzers.delt_verification.pipeline.agents import deepagent_runtime
from oxide.modules.analyzers.delt_verification.pipeline.utils.llm import load_prompt_bundle

logger = logging.getLogger(NAME)


@dataclass
class AnalyzerRuntime:
    """Bundles the agent runtime so triage always runs against initialized clients."""

    triage_llm: ChatOllama
    # Verification gets its own client. It drives MCP tools over a whole binary, so its
    # context grows across many calls and a single call can outlast triage's per-request
    # timeout; sharing the triage client would cap verification mid-investigation.
    verification_llm: ChatOllama
    binary_context_llm: ChatOllama
    triage_sys: str
    triage_with_callees_sys: str
    binary_context_sys: str
    verification_sys: str
    triage_request_timeout_s: float
    binary_context_request_timeout_s: float
    binary_context_model_call_timeout_s: float
    verification_request_timeout_s: float
    # Per-model-call timeout inside that budget. Must stay well below it, or one stalled
    # call consumes the entire investigation and the run is lost with no verdict.
    verification_model_call_timeout_s: float


RUNTIMES: Dict[str, AnalyzerRuntime] = {}
RUNTIMES_LOCK = threading.Lock()


def _runtime_cache_key(opts: Dict[str, Any]) -> str:
    return "|".join(
        [
            str(opts["model"]),
            str(opts.get("ollama_base_url") or ""),
            str(opts.get("triage_prompt_file") or ""),
            str(opts.get("triage_with_callees_prompt_file") or ""),
            str(opts.get("binary_context_prompt_file") or ""),
            str(opts.get("verification_prompt_file") or ""),
            str(opts.get("triage_request_s") or ""),
            str(opts.get("binary_context_request_s") or ""),
            str(opts.get("binary_context_model_call_s") or ""),
            str(opts.get("verification_request_s") or ""),
            str(opts.get("verification_model_call_s") or ""),
        ]
    )


def _build_runtime(opts: Dict[str, Any]) -> AnalyzerRuntime:
    model = str(opts["model"])
    # Optional per-run Ollama endpoint. Lets one experiment fan out across several
    # Ollama servers (e.g. one per GPU); None falls back to ChatOllama's default host.
    base_url = str(opts.get("ollama_base_url") or "").strip() or None
    prompts = load_prompt_bundle(opts)
    request_timeout_s = float(opts["triage_request_s"])
    binary_context_request_timeout_s = float(opts["binary_context_request_s"])
    binary_context_model_call_timeout_s = float(opts["binary_context_model_call_s"])
    verification_request_timeout_s = float(opts["verification_request_s"])
    verification_model_call_timeout_s = float(opts["verification_model_call_s"])

    return AnalyzerRuntime(
        triage_llm=deepagent_runtime.make_agent_model(
            model, request_timeout_s=request_timeout_s, base_url=base_url
        ),
        verification_llm=deepagent_runtime.make_agent_model(
            model, request_timeout_s=verification_model_call_timeout_s, base_url=base_url
        ),
        binary_context_llm=deepagent_runtime.make_agent_model(
            model, request_timeout_s=binary_context_model_call_timeout_s, base_url=base_url
        ),
        triage_sys=prompts["triage"]["system"],
        triage_with_callees_sys=prompts["triage_with_callees"]["system"],
        binary_context_sys=prompts["binary_context"]["system"],
        verification_sys=prompts["verification"]["system"],
        triage_request_timeout_s=request_timeout_s,
        binary_context_request_timeout_s=binary_context_request_timeout_s,
        binary_context_model_call_timeout_s=binary_context_model_call_timeout_s,
        verification_request_timeout_s=verification_request_timeout_s,
        verification_model_call_timeout_s=verification_model_call_timeout_s,
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
    resolved_opts["triage_request_s"] = float(resolved_opts.get("triage_request_s") or 150.0)
    resolved_opts["binary_context_request_s"] = float(
        resolved_opts.get("binary_context_request_s") or 450.0
    )
    resolved_opts["binary_context_model_call_s"] = float(
        resolved_opts.get("binary_context_model_call_s") or 120.0
    )
    resolved_opts["verification_request_s"] = float(
        resolved_opts.get("verification_request_s") or 600.0
    )
    resolved_opts["verification_model_call_s"] = float(
        resolved_opts.get("verification_model_call_s") or 180.0
    )
    return resolved_opts


def get_or_build_runtime(opts: Optional[Dict[str, Any]]) -> AnalyzerRuntime:
    """Memoized by model + endpoint + prompt/timeout config for the triage pipeline.

    The cache key includes ollama_base_url, so concurrent comparisons pinned to different
    endpoints each get their own runtime and their own ChatOllama client rather than
    sharing one across threads.
    """
    resolved_opts = _resolve_runtime_opts(opts)
    cache_key = _runtime_cache_key(resolved_opts)
    with RUNTIMES_LOCK:
        runtime = RUNTIMES.get(cache_key)
        if runtime is None:
            runtime = _build_runtime(resolved_opts)
            RUNTIMES[cache_key] = runtime
        return runtime
