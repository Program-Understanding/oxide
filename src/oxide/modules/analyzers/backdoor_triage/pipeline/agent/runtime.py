import logging
import threading
from dataclasses import dataclass
from typing import Any, Dict, Optional

from langchain_ollama import ChatOllama

from oxide.modules.analyzers.backdoor_triage.config import NAME
from oxide.modules.analyzers.backdoor_triage.pipeline.agent.graph import build_triage_graph
from oxide.modules.analyzers.backdoor_triage.pipeline.agent import agent_runtime
from oxide.modules.analyzers.backdoor_triage.pipeline.utils.llm import load_prompt_bundle

logger = logging.getLogger(NAME)


@dataclass
class TriageRuntime:
    """ Bundles everything all three stages need so no code path can run against
        uninitialized/None LLM clients -- constructing one *is* the initialization.
    """

    stage1_llm: ChatOllama
    stage1_sys: str
    stage1_schema: Dict[str, Any]
    stage2_llm: ChatOllama
    stage2_sys: str
    stage2_sys_callee: str
    stage2_request_timeout_s: float
    stage3_llm: ChatOllama
    stage3_sys: str
    stage3_request_timeout_s: float
    stage3_max_repeated_tool_calls: int
    graph: Any


RUNTIMES: Dict[str, TriageRuntime] = {}
RUNTIMES_LOCK = threading.Lock()


def _runtime_cache_key(opts: Dict[str, Any]) -> str:
    return "|".join(
        [
            str(opts["model"]),
            str(opts["stage3_model"]),
            str(opts.get("stage1_prompt_file") or ""),
            str(opts.get("stage2_prompt_file") or ""),
            str(opts.get("stage2_callee_prompt_file") or ""),
            str(opts.get("stage3_prompt_file") or ""),
            str(opts.get("stage2_request_s") or ""),
            str(opts.get("stage3_request_s") or ""),
            str(opts.get("stage1_client_request_s") or ""),
            str(opts.get("stage3_max_repeated_tool_calls") or ""),
        ]
    )


def _build_runtime(opts: Dict[str, Any]) -> TriageRuntime:
    model = str(opts["model"])
    stage3_model = str(opts["stage3_model"])
    prompts = load_prompt_bundle(opts)
    stage1_sys = prompts["stage1"]["system"]
    stage1_schema = prompts["stage1"].get("schema") or {}
    stage2_sys = prompts["stage2"]["system"]
    stage2_sys_callee = prompts["stage2_callee"]["system"]
    stage3_sys = prompts["stage3"]["system"]

    stage1_llm = ChatOllama(
        model=model,
        temperature=0.0,
        keep_alive="10m",
        request_timeout=float(opts["stage1_client_request_s"]),
        format=stage1_schema,
        model_kwargs={"num_predict": 512},
    )
    stage2_llm = agent_runtime.make_agent_model(model, request_timeout_s=float(opts["stage2_request_s"]))
    stage3_llm = agent_runtime.make_agent_model(stage3_model, request_timeout_s=float(opts["stage3_request_s"]))

    runtime = TriageRuntime(
        stage1_llm=stage1_llm,
        stage1_sys=stage1_sys,
        stage1_schema=stage1_schema,
        stage2_llm=stage2_llm,
        stage2_sys=stage2_sys,
        stage2_sys_callee=stage2_sys_callee,
        stage2_request_timeout_s=float(opts["stage2_request_s"]),
        stage3_llm=stage3_llm,
        stage3_sys=stage3_sys,
        stage3_request_timeout_s=float(opts["stage3_request_s"]),
        stage3_max_repeated_tool_calls=int(opts["stage3_max_repeated_tool_calls"]),
        graph=None,
    )
    setattr(runtime.stage1_llm, "_oxide_stage1_token_timeout_s", float(opts["stage1_token_s"]))
    setattr(runtime.stage1_llm, "_oxide_stage1_total_timeout_s", float(opts["stage1_total_s"]))
    runtime.graph = build_triage_graph(runtime)
    return runtime


def get_or_build_runtime(opts: Optional[Dict[str, Any]]) -> TriageRuntime:
    """ Memoized by model + prompt/timeout config. Calling this unconditionally
        before any triage work guarantees a fully-initialized runtime (live LLM
        clients for all three stages and a compiled graph) always exists before
        triage runs -- there is no uninitialized/partial state a caller could hit.
    """
    resolved_opts = dict(opts or {})
    model = str(resolved_opts.get("model") or "").strip()
    if not model:
        raise ValueError(
            "backdoor_triage requires an explicit 'model' opt (an Ollama model tag); "
            "no default model is configured."
        )
    resolved_opts["model"] = model
    # Stage 3 defaults to the same model as Stage 1/2 unless overridden -- it's
    # the one stage worth pointing at a different (e.g. larger/slower) model.
    resolved_opts["stage3_model"] = str(resolved_opts.get("stage3_model") or model).strip() or model
    resolved_opts["stage2_request_s"] = float(resolved_opts.get("stage2_request_s") or 150.0)
    resolved_opts["stage3_request_s"] = float(resolved_opts.get("stage3_request_s") or 3600.0)
    resolved_opts["stage1_token_s"] = float(resolved_opts.get("stage1_token_s") or 30.0)
    resolved_opts["stage1_total_s"] = float(resolved_opts.get("stage1_total_s") or 300.0)
    resolved_opts["stage1_client_request_s"] = float(resolved_opts.get("stage1_client_request_s") or 180.0)
    resolved_opts["stage3_max_repeated_tool_calls"] = int(
        resolved_opts.get("stage3_max_repeated_tool_calls") or agent_runtime.DEFAULT_MAX_CONSECUTIVE_REPEATED_TOOL_CALLS
    )
    cache_key = _runtime_cache_key(resolved_opts)
    with RUNTIMES_LOCK:
        runtime = RUNTIMES.get(cache_key)
        if runtime is None:
            runtime = _build_runtime(resolved_opts)
            RUNTIMES[cache_key] = runtime
        return runtime
