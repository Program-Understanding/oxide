"""Registry-facing tool wrappers: each oracle is published as its own tool so the reviewer can pick
the one whose evidence fits, plus the combined `static_type_oracles` runner."""
from __future__ import annotations

import json
import re

from agentic.tools.registry import tool as _tool
from .common import DEFAULT_ORACLES, _ORACLE_PARAMS


@_tool(group="oracle", params={"addr": {"type": "string"}, "variables": {"type": "string"},
                               "which": {"type": "string"}},
       required=["addr", "variables"],
       desc="Deterministic ABI/decompiler oracles: CERTIFIED per-variable types for the function at "
            "addr. `variables` is the variable list, one `V<n>  <register 0x..|stack -0x..>  <size>` "
            "per line.")
def static_type_oracles(ctx, addr: str, variables: str, which: str = "") -> list:
    """Registry-side entry point for the oracles, so this tool is dispatched exactly like every other
    one (`registry._invoke` -> memoized `_call`) instead of through bespoke code in the MCP server.

    It previously existed ONLY as an `@mcp.tool()` function: absent from REGISTRY, unreachable from
    `build_tools`' dispatcher, and taking `vaddr` where all six other tools take `addr`. That made it
    the odd one out in every respect the model can observe, on a menu where it was already competing
    with seven framework tools nobody had asked for."""
    from agentic import grounding as _G
    q = f"function at vaddr {addr if str(addr).startswith('0x') else '0x' + str(addr)}.\n{variables}\n"
    ct = lambda name, args: _stringify_call(ctx, name, args)          # noqa: E731
    out, seen = [], set()
    for name, fn in _G.resolve_domain_oracles(which or DEFAULT_ORACLES, q):
        try:
            for f in fn(ct, q):
                if f["vid"] in seen:
                    continue                                          # earlier oracles win
                seen.add(f["vid"])
                out.append({**f, "oracle": name})
        except Exception:                                             # noqa: BLE001
            continue
    return out


@_tool(group="oracle", params=_ORACLE_PARAMS, required=["addr", "variables"],
       desc="CERTIFIED types for register-passed PARAMETERS that are handed to a C-library function "
            "whose ABI fixes that argument's type (argument 1 of `fclose` is `FILE *`). Use when the "
            "function calls libc. `variables`: one `V<n>  <register 0x..|stack -0x..>  <size>` per line.")
def callee_signature(ctx, addr: str, variables: str) -> list:
    """Oracle: a parameter's type, fixed by the ABI of the library function it flows into."""
    return static_type_oracles(ctx, addr=addr, variables=variables, which="callee_signature")


@_tool(group="oracle", params=_ORACLE_PARAMS, required=["addr", "variables"],
       desc="CERTIFIED POINTER types taken from the decompiler's own recovered declarations. Use when "
            "you suspect a value is a pointer but the assembly does not settle it. `variables`: one "
            "`V<n>  <register 0x..|stack -0x..>  <size>` per line.")
def decompiler_pointer(ctx, addr: str, variables: str) -> list:
    """Oracle: the decompiler's declared pointer type for an entity."""
    return static_type_oracles(ctx, addr=addr, variables=variables, which="decompiler_pointer")


@_tool(group="oracle", params=_ORACLE_PARAMS, required=["addr", "variables"],
       desc="CERTIFIED types for STACK SLOTS that the prologue spills an argument register into — such "
            "a slot is a copy of that parameter and shares its type. Use for stack locals that mirror "
            "parameters. `variables`: one `V<n>  <register 0x..|stack -0x..>  <size>` per line.")
def spilled_param(ctx, addr: str, variables: str) -> list:
    """Oracle: a stack slot that holds a spilled argument register inherits that parameter's type."""
    return static_type_oracles(ctx, addr=addr, variables=variables, which="spilled_param")


@_tool(group="oracle", params=_ORACLE_PARAMS, required=["addr", "variables"],
       desc="CERTIFIED signedness for integer variables, from opcodes the compiler had no choice "
            "about (shr/sar, movzx/movsx, div/idiv, rotates). Use when deciding signed vs unsigned. "
            "`variables`: one `V<n>  <register 0x..|stack -0x..>  <size>` per line.")
def signedness(ctx, addr: str, variables: str) -> list:
    """Oracle: an integer's sign bit, recovered from sign-revealing instruction choices."""
    return static_type_oracles(ctx, addr, variables, which="signedness")


@_tool(group="oracle", params=_ORACLE_PARAMS, required=["addr", "variables"],
       desc="CERTIFIED types for parameters FORWARDED through user functions until they reach a "
            "fixed-type library position. Use when a parameter is passed straight to another local "
            "function. `variables`: one `V<n>  <register 0x..|stack -0x..>  <size>` per line.")
def interprocedural_param_usage(ctx, addr: str, variables: str) -> list:
    """Oracle: a forwarded parameter's type, resolved one hop into its callee."""
    return static_type_oracles(ctx, addr=addr, variables=variables,
                               which="interprocedural_param_usage")


def _stringify_call(ctx, name, args):
    """Dispatch one registered tool against `ctx` — the same path `registry._invoke` takes."""
    from agentic.tools.registry import REGISTRY, _stringify
    spec = REGISTRY.get(name)
    if spec is None:
        return f"(no such tool: {name})"
    try:
        return _stringify(spec.fn(ctx, **dict(args or {})))
    except Exception as e:                                            # noqa: BLE001
        return f"(tool error: {str(e)[:160]})"
