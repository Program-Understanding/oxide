"""Tool registry for the agentic feature.
"""
from __future__ import annotations

import json

REGISTRY: dict = {}      # name -> ToolSpec


def out_cap() -> int:
    """Per-tool-output char cap. REQUIRED via AGENTIC_OUT_CAP / [agentic] out_cap; 0 = unlimited
    (use on local models where context is cheap), a positive value bounds remote/API runs."""
    from oxide.core.libraries.agentic.llm import cfg_required
    return int(cfg_required("out_cap"))


class ToolSpec:
    def __init__(self, name, group, fn, params, required, desc):
        self.name = name
        self.group = group
        self.fn = fn
        self.schema = {"type": "function", "function": {
            "name": name, "description": desc,
            "parameters": {"type": "object", "properties": params or {},
                           "required": list(required or [])}}}


def tool(name=None, group="core", params=None, required=(), desc=None):
    """Register a tool. `params`/`required` are the OpenAI function-schema fields; `desc`
    defaults to the function's first docstring line."""
    def deco(fn):
        nm = name or fn.__name__
        d = desc or (fn.__doc__ or "").strip().split("\n")[0] or nm
        REGISTRY[nm] = ToolSpec(nm, group, fn, params, required, d)
        return fn
    return deco


def all_schemas() -> list:
    return [s.schema for s in REGISTRY.values()]


def resolve_tool_name(name: str):
    """Map a (possibly model-mangled) tool name to a registered one, or None.

    Some local models rewrite tool names in their chat template (e.g. qwen/gemma variants emit
    `Gemma_Decompile__function` for `decompile`). Match exactly first, then strip such affixes and
    fuzzy-match case-insensitively so tool dispatch is robust across models."""
    if not name:
        return None
    if name in REGISTRY:
        return name
    lower = {nm.lower(): nm for nm in REGISTRY}
    c = name.lower()
    if c in lower:
        return lower[c]
    for pre in ("gemma_", "functions_", "function_", "tools_", "tool_", "default_"):
        if c.startswith(pre):
            c = c[len(pre):]
    for suf in ("__function", "_function", "__tool", "_tool", "_func"):
        if c.endswith(suf):
            c = c[:-len(suf)]
    c = c.replace("__", "_").strip("_ ")
    if c in lower:
        return lower[c]
    for low, orig in lower.items():           # last resort: substring containment either way
        if low == c or low in c or c in low:
            return orig
    return None


def _stringify(res) -> str:
    s = res if isinstance(res, str) else json.dumps(res, default=str)
    cap = out_cap()
    return s if cap <= 0 else s[:cap]


def build_tools(api, oid: str, groups=None):
    """Return (schemas, call_tool) bound to one oid.
    - schemas: tool schemas filtered to `groups` (None = all) — what the LLM sees.
    - call_tool(name, args) -> str: dispatch to ANY registered tool (not group-limited), so
      grounding/recall can re-run any tool. Emits a Phoenix TOOL span when tracing is on."""
    from .context import OxideContext
    try:
        from oxide.core.libraries.agentic import trace as _trace
    except Exception:  # noqa: BLE001
        _trace = None
    ctx = OxideContext(api, oid)
    gset = set(groups) if groups is not None else None
    schemas = [s.schema for s in REGISTRY.values() if gset is None or s.group in gset]
    _cache: dict = {}      # (name,args) -> result; tools are read-only & deterministic, so an
                           # identical call always yields the same output. Memoizing it breaks the
                           # repeat-the-same-tool loops small local models fall into (see _REPEAT).

    def _key(name, args):
        try:
            return name + "\x00" + json.dumps(args or {}, sort_keys=True, default=str)
        except Exception:  # noqa: BLE001
            return name + "\x00" + str(args)

    def _invoke(name, args):
        spec = REGISTRY.get(name)
        if spec is None:                       # tolerate model-mangled tool names (see resolve_tool_name)
            canon = resolve_tool_name(name)
            spec = REGISTRY.get(canon) if canon else None
        if spec is None:
            return f"(no such tool: {name})"
        a = dict(args or {})
        a.pop("binary_path", None)
        try:
            return _stringify(spec.fn(ctx, **a))
        except TypeError as e:
            return f"(tool arg error: {str(e)[:160]})"
        except Exception as e:  # noqa: BLE001
            return f"(tool error: {str(e)[:160]})"

    def _traced() -> bool:
        return _trace is not None and (_trace.enabled() or _trace.file_tracing())

    def call_tool(name, args=None):
        k = _key(name, args)
        if k in _cache:                       # identical earlier call -> reuse, tell the model to stop
            return _REPEAT + _cache[k]
        if _traced():
            with _trace.tool_span(name, dict(args or {})) as out:
                res = _invoke(name, args)
                out(res)
                _cache[k] = res
                return res
        res = _invoke(name, args)
        _cache[k] = res
        return res

    return schemas, call_tool


_REPEAT = ("[REPEAT CALL — you already called this tool with these exact arguments earlier; the "
           "result below is the same. Do NOT call it again with the same args; use what you have, "
           "try DIFFERENT args/a different tool, or output your final answer.]\n")
