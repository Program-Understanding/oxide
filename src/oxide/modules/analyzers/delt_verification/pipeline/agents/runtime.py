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
    """Bundles the agent runtime so bounded always runs against initialized clients."""

    bounded_llm: ChatOllama
    # Unbounded gets its own client. It drives MCP tools over a whole binary, so its
    # context grows across many calls and a single call can outlast bounded's per-request
    # timeout; sharing the bounded client would cap unbounded mid-investigation.
    unbounded_llm: ChatOllama
    bounded_sys: str
    bounded_with_callees_sys: str
    unbounded_sys: str
    # Used when bounded produced no report, so the agent is not pointed at a claim
    # that does not exist.
    unbounded_no_report_sys: str
    bounded_request_timeout_s: float
    bounded_model_call_timeout_s: float
    unbounded_request_timeout_s: float
    # Per-model-call timeout inside that budget. Must stay well below it, or one stalled
    # call consumes the entire investigation and the run is lost with no verdict.
    unbounded_model_call_timeout_s: float
    # Greedy decoding. Everything else is left to the model and to Ollama; carried here so
    # a run can record what it asked for.
    sampling: Dict[str, Any]


RUNTIMES: Dict[str, AnalyzerRuntime] = {}
RUNTIMES_LOCK = threading.Lock()


def _runtime_cache_key(opts: Dict[str, Any]) -> str:
    return "|".join(
        [
            str(opts["model"]),
            str(opts.get("ollama_base_url") or ""),
            str(opts.get("bounded_prompt_file") or ""),
            str(opts.get("bounded_with_callees_prompt_file") or ""),
            str(opts.get("unbounded_prompt_file") or ""),
            str(opts.get("unbounded_no_report_prompt_file") or ""),
            str(opts.get("bounded_request_s") or ""),
            str(opts.get("bounded_model_call_s") or ""),
            str(opts.get("unbounded_request_s") or ""),
            str(opts.get("unbounded_model_call_s") or ""),
            str(opts.get("temperature")),
            str(opts.get("seed")),
        ]
    )


def _build_runtime(opts: Dict[str, Any]) -> AnalyzerRuntime:
    model = str(opts["model"])
    # Optional per-run Ollama endpoint. Lets one experiment fan out across several
    # Ollama servers (e.g. one per GPU); None falls back to ChatOllama's default host.
    base_url = str(opts.get("ollama_base_url") or "").strip() or None
    prompts = load_prompt_bundle(opts)
    request_timeout_s = float(opts["bounded_request_s"])
    bounded_model_call_timeout_s = float(opts["bounded_model_call_s"])
    unbounded_request_timeout_s = float(opts["unbounded_request_s"])
    unbounded_model_call_timeout_s = float(opts["unbounded_model_call_s"])
    sampling = {"temperature": float(opts["temperature"]), "seed": int(opts["seed"])}

    return AnalyzerRuntime(
        bounded_llm=deepagent_runtime.make_agent_model(
            model, request_timeout_s=bounded_model_call_timeout_s, base_url=base_url, **sampling
        ),
        unbounded_llm=deepagent_runtime.make_agent_model(
            model, request_timeout_s=unbounded_model_call_timeout_s, base_url=base_url,
            **sampling
        ),
        bounded_sys=prompts["bounded"]["system"],
        bounded_with_callees_sys=prompts["bounded_with_callees"]["system"],
        unbounded_sys=prompts["unbounded"]["system"],
        unbounded_no_report_sys=prompts["unbounded_no_report"]["system"],
        bounded_request_timeout_s=request_timeout_s,
        bounded_model_call_timeout_s=bounded_model_call_timeout_s,
        unbounded_request_timeout_s=unbounded_request_timeout_s,
        unbounded_model_call_timeout_s=unbounded_model_call_timeout_s,
        sampling=sampling,
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
    resolved_opts["bounded_request_s"] = float(resolved_opts.get("bounded_request_s") or 1000.0)
    resolved_opts["bounded_model_call_s"] = float(
        resolved_opts.get("bounded_model_call_s") or 180.0
    )
    resolved_opts["unbounded_request_s"] = float(
        resolved_opts.get("unbounded_request_s") or 1000.0
    )
    resolved_opts["unbounded_model_call_s"] = float(
        resolved_opts.get("unbounded_model_call_s") or 180.0
    )
    # `or` would turn a deliberate 0 back into the default, and 0 is the value that matters
    # most here, so each falls back only when the opt is absent or empty.
    for key, default in (("temperature", 0.0), ("seed", 1)):
        value = resolved_opts.get(key)
        resolved_opts[key] = type(default)(default if value in (None, "") else value)
    return resolved_opts


def get_or_build_runtime(opts: Optional[Dict[str, Any]]) -> AnalyzerRuntime:
    """Memoized by model + endpoint + prompt/timeout config for the bounded pipeline.

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
