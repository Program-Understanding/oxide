"""Pure utility tools (group: util) — stateless primitives the agent directs; not Oxide-backed."""
from __future__ import annotations

import ast as _ast

from .registry import tool
from .context import safe_eval


@tool(group="util", params={"expr": {"type": "string"}}, required=["expr"],
      desc="Evaluate an EXACT arithmetic/bitwise expression (+ - * / // % ** & | ^ << >> , hex/dec).")
def compute(ctx, expr: str = "", expression: str = "") -> dict:
    expr = (expr or expression or "").strip()
    if not expr:
        return {"error": "empty expression; pass the formula as expr"}
    try:
        val = safe_eval(_ast.parse(expr, mode="eval"))
    except Exception as e:  # noqa: BLE001
        return {"error": f"could not evaluate: {str(e)[:160]}"}
    out = {"expr": expr, "result": val}
    if isinstance(val, int):
        out["hex"] = hex(val)
    return out
