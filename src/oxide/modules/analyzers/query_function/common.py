"""Helpers shared by the query_function backends."""

from typing import Any, List

from oxide.core import api


def iter_functions(funcs: Any):
    if isinstance(funcs, dict):
        for addr, finfo in funcs.items():
            if addr == "meta":
                continue
            yield addr, finfo
    elif isinstance(funcs, (list, tuple)):
        for addr in funcs:
            yield addr, None


def extract_func_name(finfo: Any, addr: Any) -> str:
    if isinstance(finfo, dict):
        for key in ("name", "function_name", "symbol", "label"):
            value = finfo.get(key)
            if isinstance(value, str) and value.strip():
                return value.strip()
    if isinstance(finfo, str) and finfo.strip():
        return finfo.strip()
    return f"sub_{addr}"


def first_preview_line(text: str) -> str:
    for line in text.splitlines():
        line = line.strip()
        if line:
            return line[:200]
    return ""


def load_text_option(opts: dict, value_key: str, path_key: str) -> str:
    text = (opts.get(value_key) or "").strip()
    path = (opts.get(path_key) or "").strip()
    if (not text) and path:
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as f:
                text = f.read().strip()
        except OSError:
            return ""
    return text


def result_limit(opts: dict) -> int:
    limit = as_int(opts.get("limit", 0), 0)
    top_k = as_int(opts.get("top_k", 10), 10)
    if limit > 0:
        return limit
    if limit <= 0 and top_k <= 0:
        return 0
    return top_k


def expand_oids_best_effort(oid_list: List[str]) -> List[str]:
    try:
        return api.expand_oids(oid_list)
    except Exception:
        return oid_list


def as_int(v: Any, default: int) -> int:
    try:
        return int(v)
    except Exception:
        return default


def as_float(v: Any, default: float) -> float:
    try:
        return float(v)
    except Exception:
        return default


def as_bool(v: Any) -> bool:
    if isinstance(v, str):
        return v.strip().lower() not in ("", "0", "false", "no", "off")
    return bool(v)
