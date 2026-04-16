# -*- coding: utf-8 -*-
"""Post-diff annotation: tag added call sites with llm_function_analysis labels."""

import re
from typing import Any, Dict, List, Optional

from oxide.core import api

from align import parse_addr_any


def _normalize_known_calls_shape(obj: Any) -> Optional[Dict[str, int]]:
    """Normalize various shapes of call-list data into {name: addr}."""
    if obj is None:
        return None

    out: Dict[str, int] = {}

    if isinstance(obj, dict):
        numeric_like_keys = all(
            isinstance(k, int) or (isinstance(k, str) and (k.isdigit() or k.lower().startswith("0x")))
            for k in obj.keys()
        )

        if numeric_like_keys:
            for a, n in obj.items():
                addr = parse_addr_any(a)
                if addr is not None and isinstance(n, str) and n:
                    out[n] = addr
            return out or None

        for n, a in obj.items():
            if not isinstance(n, str) or not n:
                continue
            addr = parse_addr_any(a)
            if addr is None:
                addr = parse_addr_any(n)
            if addr is not None:
                out[n] = addr
        return out or None

    if isinstance(obj, list):
        for item in obj:
            if isinstance(item, dict):
                n = item.get("name")
                a = parse_addr_any(item.get("addr"))
                if isinstance(n, str) and n and a is not None:
                    out[n] = a
            elif isinstance(item, str):
                a = parse_addr_any(item)
                if a is not None:
                    out[item] = a
        return out or None

    return None


def get_function_calls(call_diff: Dict) -> Optional[Dict[str, int]]:
    """Extract {name: addr} for all target-side functions from a call_diff result."""
    target_func_calls: Dict[Any, Any] = {}
    for item in (
        *(call_diff.get("fc_paired") or []),
        *(call_diff.get("fc_add_existing") or []),
        *(call_diff.get("fc_add_new") or []),
    ):
        t = item.get("target") or {}
        if "addr" in t and "name" in t:
            target_func_calls[t["addr"]] = t["name"]

    return _normalize_known_calls_shape(target_func_calls)


def _get_tag_for_addr(oid: str, addr: int) -> Optional[str]:
    try:
        return api.get_field("llm_function_analysis", oid, "tag", {"func_offset": addr})
    except Exception:
        return None


def annotate_with_tags(
    unified: str,
    name_to_addr: Dict[str, int],
    target_oid: str,
) -> str:
    """
    Append '// name: tag' annotations to added diff lines that call known functions.
    Tags are fetched lazily — only for names that actually appear in diff lines.
    """
    if not unified or not name_to_addr:
        return unified

    names_sorted = sorted(name_to_addr.keys(), key=len, reverse=True)

    call_pat = re.compile(
        r"\b(" + "|".join(re.escape(n) for n in names_sorted) + r")\b\s*\("
    )

    name_to_tag: Dict[str, Optional[str]] = {}
    out_lines: List[str] = []

    for line in unified.splitlines():
        if line.startswith(("---", "+++", "@@")):
            out_lines.append(line)
            continue

        if not line or line[0] != "+":
            out_lines.append(line)
            continue

        prefix, body = line[0], line[1:]
        code_part, sep, trailing = body.partition("//")

        matches = [m.group(1) for m in call_pat.finditer(code_part)]
        if not matches:
            out_lines.append(line)
            continue

        seen = list(dict.fromkeys(matches))

        fragments: List[str] = []
        for n in seen:
            if n not in name_to_tag:
                name_to_tag[n] = _get_tag_for_addr(target_oid, name_to_addr[n])
            tag = name_to_tag[n]
            fragments.append(f"{n}: {tag}" if tag else n)

        if sep and all(fragment in trailing for fragment in fragments):
            out_lines.append(line)
            continue

        annotated = prefix + code_part
        if sep:
            annotated += sep + trailing
        annotated += " // " + "; ".join(fragments)
        out_lines.append(annotated)

    return "\n".join(out_lines) + ("\n" if out_lines else "")
