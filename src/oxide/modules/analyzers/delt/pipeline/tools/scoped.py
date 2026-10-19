"""Scope the oxide MCP tools to the binaries one agent is allowed to look at.

The agents must not choose which binary they read. The binary-context agent works on one
binary; the unbounded agent works on one target/baseline pair and should address them
only as ``target``/``baseline``, never by raw OID. Both are the same operation: take the
tool surface the MCP server publishes and remove the OID parameters, either by binding
them to a fixed value or by replacing them with a choice among named binaries.

Everything else about a tool -- its parameter names, types, defaults, and description --
comes from the server's own schema, so a signature change in ``oxide_mcp_server.py``
flows through without an edit here.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass
from typing import Any, Dict, Iterable, Mapping, Sequence, Union

from langchain_core.tools import BaseTool, StructuredTool


@dataclass(frozen=True)
class Bind:
    """Drop a server parameter and always send this value for it."""

    value: str


@dataclass(frozen=True)
class Choose:
    """Replace a server parameter with a choice among named binaries.

    The agent picks a name (``target``, ``baseline``); the wrapper substitutes the OID.
    """

    param: str
    options: Mapping[str, str]
    description: str


Rule = Union[Bind, Choose]

# Parameters that name a binary. Leaving one exposed would let the agent read whatever it
# likes, so scoping a tool that has one without a rule for it is a programming error.
_OID_PARAMS = frozenset(
    {
        "oid_or_name",
        "target_oid_or_name",
        "baseline_oid_or_name",
        "source_oid_or_name",
        "destination_oid_or_name",
    }
)


def _schema_of(tool_obj: Any) -> Dict[str, Any]:
    schema = getattr(tool_obj, "args_schema", None)
    if not isinstance(schema, dict):
        raise TypeError(
            f"tool '{getattr(tool_obj, 'name', '?')}' does not publish a JSON schema; "
            "expected the dict schema produced by langchain_mcp_adapters"
        )
    return copy.deepcopy(schema)


def _derive_schema(schema: Dict[str, Any], rules: Mapping[str, Rule]) -> Dict[str, Any]:
    props: Dict[str, Any] = schema.get("properties") or {}
    required = list(schema.get("required") or [])

    for param, rule in rules.items():
        if param not in props:
            continue
        del props[param]
        was_required = param in required
        required = [r for r in required if r != param]
        if isinstance(rule, Choose):
            props[rule.param] = {
                "type": "string",
                "enum": list(rule.options),
                "description": rule.description,
            }
            if was_required and rule.param not in required:
                required.append(rule.param)

    schema["properties"] = props
    if required:
        schema["required"] = required
    else:
        schema.pop("required", None)
    return schema


def _unwrap_kwargs(kwargs: Dict[str, Any]) -> Dict[str, Any]:
    """Flatten the ``{"kwargs": {...}}`` shape some models emit."""
    wrapped = kwargs.get("kwargs")
    if not isinstance(wrapped, dict):
        return kwargs
    merged = dict(wrapped)
    for key, value in kwargs.items():
        if key != "kwargs":
            merged[key] = value
    return merged


def _coerce_strings(args: Dict[str, Any], props: Mapping[str, Any]) -> Dict[str, Any]:
    """Stringify numbers passed to string parameters, e.g. a function offset as int."""
    for key, value in list(args.items()):
        if isinstance(value, (int, float)) and not isinstance(value, bool):
            if (props.get(key) or {}).get("type") == "string":
                args[key] = str(value)
    return args


def _scope_one(underlying: Any, rules: Mapping[str, Rule]) -> BaseTool:
    schema = _schema_of(underlying)
    applicable = {p: r for p, r in rules.items() if p in (schema.get("properties") or {})}
    derived = _derive_schema(schema, applicable)

    leaked = _OID_PARAMS & set(derived.get("properties") or {})
    if leaked:
        raise ValueError(
            f"tool '{underlying.name}' would expose binary selector(s) {sorted(leaked)}; "
            "add a Bind or Choose rule for them"
        )

    props = derived.get("properties") or {}

    async def _call(**kwargs: Any) -> Any:
        args = _coerce_strings(_unwrap_kwargs(kwargs), props)
        # Models still emit the scoped-away parameters sometimes, having read an OID from
        # their input files. Drop those and apply the rules last, so a value the agent
        # supplies can never redirect a tool at a binary it was not given.
        payload = {k: v for k, v in args.items() if k not in _OID_PARAMS}
        for param, rule in applicable.items():
            if isinstance(rule, Bind):
                payload[param] = rule.value
                continue
            choice = str(payload.pop(rule.param, "") or "").strip().lower()
            if choice not in rule.options:
                return (
                    f"{underlying.name}: {rule.param} must be one of "
                    f"{sorted(rule.options)}, got {choice!r}"
                )
            payload[param] = rule.options[choice]
        return await underlying.ainvoke(payload)

    return StructuredTool(
        name=underlying.name,
        description=underlying.description,
        args_schema=derived,
        coroutine=_call,
        metadata=getattr(underlying, "metadata", None),
        handle_tool_error=getattr(underlying, "handle_tool_error", True),
    )


def scope_tools(
    *,
    mcp_tools: Iterable[Any],
    allow: Sequence[str],
    rules: Mapping[str, Rule],
) -> list[BaseTool]:
    """Return the allowed MCP tools, rescoped by the given parameter rules.

    ``allow`` is the tool surface the agent gets, in the order given; names the server
    does not publish are skipped. ``rules`` maps a server parameter name to how it should
    be hidden, and applies to every tool that declares that parameter.
    """
    by_name = {t.name: t for t in mcp_tools if getattr(t, "name", "")}
    return [_scope_one(by_name[name], rules) for name in allow if name in by_name]
