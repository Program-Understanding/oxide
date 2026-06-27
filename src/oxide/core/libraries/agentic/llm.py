"""LLM layer for the native Oxide agentic RE feature.

One code path (litellm) talks to an OpenAI-compatible server at `endpoint` — vLLM, OpenAI, a local
server, or Ollama's /v1 endpoint. The model id + endpoint + (optional) OPENAI_API_KEY are all
that's needed.

Resolution order for every setting: opts -> environment (AGENTIC_<KEY>) -> the [agentic] section of
~/.config/oxide/.config.txt. There are NO built-in default values — a missing required setting
raises a clear error telling you what to add, rather than silently running with a guessed value.
"""
from __future__ import annotations

import json
import os
import time

try:
    import litellm
    litellm.num_retries = 6
    litellm.drop_params = True       # tolerate provider-specific unsupported params
except Exception:  # noqa: BLE001
    litellm = None

_SEED = 1234

USAGE = {"prompt": 0, "completion": 0, "calls": 0}


def _from_oxide_config(key: str):
    """Read an `[agentic]` key from Oxide's config file (~/.config/oxide/.config.txt), if present.
    Uses the raw config parser directly — the typed `get_value` only knows sections REGISTERED in
    Oxide's defaults, and `[agentic]` is a user-added one — so a missing section/key returns None
    and the caller falls through to env/defaults."""
    try:
        from oxide.core import config as _cfg  # type: ignore
        return _cfg.rcp.get("agentic", key)
    except Exception:  # noqa: BLE001  # NoSection/NoOption/etc. -> simply not configured
        return None


def _opt(opts, key):
    v = opts.get(key)
    if v is None:
        v = os.environ.get(f"AGENTIC_{key.upper()}")
    if v is None:
        v = _from_oxide_config(key)
    return v if v not in (None, "") else None


def cfg_get(key: str, default=None):
    """Resolve a module-level agentic tunable: env AGENTIC_<KEY> -> [agentic] config <key> ->
    default. Same precedence as _opt but with no opts dict — so the tuning knobs (max_tokens,
    nothink, timeouts, caps) can all live in ~/.config/oxide/.config.txt, not just env."""
    v = os.environ.get(f"AGENTIC_{key.upper()}")
    if v in (None, ""):
        v = _from_oxide_config(key)
    return v if v not in (None, "") else default


def cfg_int(key: str, default: int) -> int:
    """An OPTIONAL integer knob whose default is supplied by the caller (e.g. a per-run cap)."""
    try:
        return int(cfg_get(key) or default)
    except (ValueError, TypeError):
        return default


def cfg_bool(key: str) -> bool:
    return str(cfg_get(key, "")).strip().lower() in ("1", "true", "yes", "on")


def _missing(key: str):
    raise RuntimeError(
        f"agentic: required setting '{key}' is not configured. Add it under [agentic] in "
        f"~/.config/oxide/.config.txt (or set env AGENTIC_{key.split(' ')[0].upper()}).")


def cfg_required(key: str) -> str:
    """A REQUIRED setting (env AGENTIC_<KEY> or [agentic] config <key>) — raises a clear error if
    absent. Used for the LLM connection + sizing knobs, which have no safe built-in default."""
    v = cfg_get(key)
    if v is None:
        _missing(key)
    return v


def resolve_config(opts: dict | None = None) -> dict:
    """Build the effective LLM config from opts -> env -> [agentic] config. No built-in defaults:
    a required setting absent from all three raises a clear error.

    The LLM is always reached as an OpenAI-compatible server at `endpoint`. Convenience: `model`
    sets ALL roles (planner/worker/verifier) at once; otherwise each *_model must be configured."""
    opts = opts or {}
    endpoint = _opt(opts, "endpoint") or _missing("endpoint")
    cfg = {"endpoint": endpoint}
    one = _opt(opts, "model")                 # one model for every role (convenience)
    for role in ("planner_model", "worker_model", "verifier_model"):
        v = one or _opt(opts, role)
        if v is None:
            _missing(f"{role} (or 'model')")
        cfg[role] = v
    return cfg


class LLM:
    """A thin handle holding the resolved model id + endpoint for litellm. Every backend is reached
    as an OpenAI-compatible server at `endpoint` (vLLM, OpenAI, a local server, or Ollama's /v1)."""

    def __init__(self, model: str, endpoint: str = "", temperature: float = 0.0,
                 think: bool = True):
        self.model = model
        self.endpoint = endpoint
        self.temperature = temperature
        self.think = think          # False -> ask the server to skip chain-of-thought (qwen3/gemma)

    @property
    def litellm_model(self) -> str:
        return f"openai/{self.model}"          # OpenAI-compatible server via custom api_base

    def _kwargs(self) -> dict:
        kw = {"model": self.litellm_model, "temperature": self.temperature,
              "max_tokens": max_tokens(), "seed": _SEED, "timeout": req_timeout(),
              "api_base": self.endpoint,                                  # required (resolve_config)
              "api_key": os.environ.get("OPENAI_API_KEY") or "EMPTY"}     # local servers ignore the key
        if not self.think:
            kw["extra_body"] = {"chat_template_kwargs": {"enable_thinking": False}}
        return kw

    def complete(self, system: str, user: str) -> str:
        """Single tool-free completion -> text."""
        if litellm is None:
            raise RuntimeError("litellm is not installed (add it to oxide deps)")
        _t0 = time.time()
        msgs = [{"role": "system", "content": system}, {"role": "user", "content": user}]
        resp = litellm.completion(messages=msgs, **self._kwargs())
        _track(resp)
        content = resp.choices[0].message.content or ""
        _trace_llm(f"complete[{self.model}]", msgs, content, _t0)
        return content

    def chat(self, messages: list, tools: list | None = None):
        if litellm is None:
            raise RuntimeError("litellm is not installed (add it to oxide deps)")
        kw = self._kwargs()
        if tools:
            kw["tools"] = tools
            kw["tool_choice"] = "auto"
        _t0 = time.time()
        resp = litellm.completion(messages=messages, **kw)
        _track(resp)
        _trace_llm(f"chat[{self.model}]", {"messages": messages,
                   "tools": [ (t.get("function") or {}).get("name") for t in (tools or []) ]},
                   _msg_out(resp), _t0)
        return resp


def make_llm(role: str, cfg: dict, temperature: float = 0.0) -> LLM:
    """role in {planner, worker, verifier} -> an LLM handle per the resolved config.

    Worker + verifier run with thinking OFF by default: they do tool-use + emit findings/verdict
    JSON, where a verbose reasoning model's hidden CoT (thousands of tokens/call) dominates latency
    on a local server. Planner/synthesis keep thinking ON (decomposition/synthesis benefit from it).
    Overrides (env or [agentic] config): think_workers=1 forces thinking ON everywhere;
    nothink=1 forces it OFF everywhere."""
    model = cfg[f"{role}_model"]              # guaranteed present by resolve_config
    think = role not in ("worker", "verifier")
    if cfg_bool("think_workers"):
        think = True
    if cfg_bool("nothink"):
        think = False
    return LLM(model=model, endpoint=cfg["endpoint"],
               temperature=temperature, think=think)


def _msg_out(resp):
    """Extract the assistant message (content + any tool_calls) from a litellm response, JSON-able."""
    try:
        m = resp.choices[0].message
        tcs = []
        for tc in (getattr(m, "tool_calls", None) or []):
            fn = getattr(tc, "function", None)
            tcs.append({"name": getattr(fn, "name", None),
                        "arguments": getattr(fn, "arguments", None)})
        return {"content": getattr(m, "content", None) or "", "tool_calls": tcs}
    except Exception:  # noqa: BLE001
        return {"content": str(resp)[:20000], "tool_calls": []}


def _trace_llm(name, request, response, t0):
    """Forward one LLM call to the file trace (no-op unless trace.set_trace_file is active)."""
    try:
        from oxide.core.libraries.agentic import trace as _tr
        if _tr.file_tracing():
            _tr.record_llm(name, request, response, t0)
    except Exception:  # noqa: BLE001
        pass


def _track(resp) -> None:
    try:
        u = getattr(resp, "usage", None)
        if u is None:
            return
        g = (lambda k: u.get(k, 0)) if isinstance(u, dict) else (lambda k: getattr(u, k, 0) or 0)
        USAGE["prompt"] += g("prompt_tokens") or 0
        USAGE["completion"] += g("completion_tokens") or 0
        USAGE["calls"] += 1
    except Exception:  # noqa: BLE001
        pass


def ctx_chars() -> int:
    """Total input-context budget in CHARS (~4 chars/token). Keeps the ReAct prompt under the
    model's window. REQUIRED via AGENTIC_CTX_CHARS / [agentic] ctx_chars (e.g. 320000 for a 200k
    model). Raise it for large-context local models, lower it for a small window."""
    return int(cfg_required("ctx_chars"))


def req_timeout() -> float:
    """Per-request timeout in seconds. REQUIRED via AGENTIC_REQ_TIMEOUT / [agentic] req_timeout.
    Generous for long reasoning turns, finite so a dropped response aborts + retries vs hanging."""
    return float(cfg_required("req_timeout"))


def max_tokens() -> int:
    """Max OUTPUT tokens per completion. REQUIRED via AGENTIC_MAX_TOKENS / [agentic] max_tokens.
    Large enough that long answers (e.g. a 30-target list + reasoning) aren't cut off."""
    return int(cfg_required("max_tokens"))


def _cap(s: str) -> str:
    """Cap a single tool result placed into the ReAct context (out_cap; 0 = unlimited). Even when
    'unlimited', a single output is hard-clamped to half the context budget so it can never overflow
    the window by itself."""
    from oxide.core.libraries.agentic.tools.registry import out_cap
    c = out_cap()
    if c <= 0:
        c = ctx_chars() // 2
    return s if len(s) <= c else s[:c] + "\n…[truncated]"


def _msg_chars(m: dict) -> int:
    n = len(str(m.get("content") or ""))
    if m.get("tool_calls"):
        try:
            n += len(json.dumps(m["tool_calls"]))
        except Exception:  # noqa: BLE001
            n += 200
    return n


def _fit(messages: list, budget: int) -> None:
    """Shrink the ReAct history in place to ~budget chars by ELIDING the oldest tool-result
    contents first (keeps message/tool_call structure valid), then oldest assistant prose."""
    total = sum(_msg_chars(m) for m in messages)
    if total <= budget:
        return
    for role in ("tool", "assistant"):
        for m in messages[2:]:                      # never touch system + first user
            if total <= budget:
                return
            if m.get("role") == role and m.get("content") and m["content"] != "[elided]":
                total -= len(m["content"])
                m["content"] = "[elided]"
                total += len(m["content"])


def run_react(llm: LLM, system: str, user: str, tools_schema: list, call_tool, max_steps: int,
              label: str = "agent", logfn=None) -> str:
    """Tool-calling loop: the model calls tools until it stops, then returns final content.

    tools_schema : OpenAI function-tool schemas (from tools.tool_schemas()).
    call_tool    : a callable(name, args_dict) -> str result (the Oxide-backed dispatcher).
    Mirrors run_orchestrator.react_loop, but synchronous and litellm-routed.
    """
    log = logfn or (lambda m: None)
    budget = ctx_chars()
    messages = [{"role": "system", "content": system}, {"role": "user", "content": user}]
    for _ in range(1, max_steps + 1):
        _fit(messages, budget)                       # keep the prompt under the model window
        try:
            resp = llm.chat(messages, tools=tools_schema)
        except Exception as e:  # noqa: BLE001
            if "contextwindow" in type(e).__name__.lower() or "context length" in str(e).lower():
                _fit(messages, budget // 2)          # overflowed -> trim harder and retry once
                try:
                    resp = llm.chat(messages, tools=tools_schema)
                except Exception as e2:  # noqa: BLE001
                    log(f"    [{label}] chat error after trim: {str(e2)[:120]}")
                    break
            else:
                log(f"    [{label}] chat error: {str(e)[:120]}")
                break
        msg = resp.choices[0].message
        tool_calls = getattr(msg, "tool_calls", None)
        if not tool_calls:
            content = msg.content or ""
            if content.strip():
                return content
            log(f"    [{label}] empty completion — nudging for the answer")
            messages.append({"role": "assistant", "content": ""})
            messages.append({"role": "user", "content":
                             "Your previous response was empty. Based ONLY on the tool outputs "
                             "above, output your final answer / required JSON now — do not call "
                             "more tools and do not return an empty message."})
            continue
        messages.append({"role": "assistant", "content": msg.content or "",
                         "tool_calls": [{"id": tc.id, "type": "function",
                                         "function": {"name": tc.function.name,
                                                      "arguments": tc.function.arguments}}
                                        for tc in tool_calls]})
        for tc in tool_calls:
            try:
                args = json.loads(tc.function.arguments or "{}")
            except json.JSONDecodeError:
                args = {}
            log(f"    [{label}] -> {tc.function.name}({json.dumps(args)[:80]})")
            out = call_tool(tc.function.name, args)
            messages.append({"role": "tool", "tool_call_id": tc.id, "content": _cap(str(out))})
    # ran out of steps -> force a tool-free turn that emits the required output
    messages.append({"role": "user", "content":
                     "Stop calling tools. Based ONLY on the tool outputs above, output your "
                     "final answer / required JSON now."})
    try:
        resp = llm.chat(messages, tools=None)
        return resp.choices[0].message.content or ""
    except Exception:  # noqa: BLE001
        return "(max steps reached)"
