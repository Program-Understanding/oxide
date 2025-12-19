from __future__ import annotations

import re
from typing import Any, Dict, List, Optional, Tuple

from oxide.core import api

from text_tools import DECL_LINE_RE


_COMPACTION_CTX_CANDIDATES = (100, 50, 25, 10, 7, 5, 3, 1, 0)


def _normalize_known_calls_shape(obj: Any) -> Optional[Dict[str, int]]:
    if obj is None:
        return None

    out: Dict[str, int] = {}

    if isinstance(obj, dict):
        numeric_like_keys = True
        for k in obj.keys():
            if not isinstance(k, int) and not (
                isinstance(k, str) and (k.isdigit() or k.lower().startswith("0x"))
            ):
                numeric_like_keys = False
                break

        if numeric_like_keys:
            for a, n in obj.items():
                addr = _parse_addr_any(a)
                if addr is None:
                    continue
                if isinstance(n, str) and n:
                    out[n] = addr
            return out if out else None

        for n, a in obj.items():
            if not isinstance(n, str) or not n:
                continue
            addr = _parse_addr_any(a)
            if addr is None:
                addr = _parse_addr_any(n)
            if addr is not None:
                out[n] = addr
        return out if out else None

    if isinstance(obj, list):
        for it in obj:
            if isinstance(it, dict):
                n = it.get("name")
                a = _parse_addr_any(it.get("addr"))
                if isinstance(n, str) and n and a is not None:
                    out[n] = a
            elif isinstance(it, str):
                n = it
                a = _parse_addr_any(n)
                if a is not None:
                    out[n] = a
        return out if out else None

    return None


_FUN_TOKEN_RE = re.compile(r"\bFUN_([0-9a-fA-F]+)\b")


def _parse_addr_any(v: Any) -> Optional[int]:
    try:
        if isinstance(v, int):
            return v
        if isinstance(v, str):
            s = v.strip()
            m = _FUN_TOKEN_RE.fullmatch(s) or _FUN_TOKEN_RE.search(s)
            if m:
                return int(m.group(1), 16)
            if s.lower().startswith("0x"):
                return int(s, 16)
            if s.isdigit():
                return int(s, 10)
        if isinstance(v, dict):
            for k in ("addr", "address", "start", "start_addr", "ea"):
                if k in v:
                    a = _parse_addr_any(v[k])
                    if a is not None:
                        return a
            for k in ("name", "label"):
                if k in v and isinstance(v[k], str):
                    m = _FUN_TOKEN_RE.search(v[k])
                    if m:
                        return int(m.group(1), 16)
        return None
    except Exception:
        return None


def get_function_calls(
    target_oid: str,
    baseline_oid: str,
    target_func: Any,
    baseline_func: Any,
) -> Optional[Dict[str, int]]:
    diff = (
        api.retrieve(
            "function_call_diff",
            [target_oid, baseline_oid],
            {"target": str(target_func), "baseline": str(baseline_func)},
        )
        or {}
    )

    paired = diff.get("fc_paired") or []
    existing = diff.get("fc_add_existing") or []
    new = diff.get("fc_add_new") or []

    target_func_calls: Dict[Any, Any] = {}

    for item in paired:
        t = item.get("target") or {}
        if "addr" in t and "name" in t:
            target_func_calls[t["addr"]] = t["name"]
    for item in existing:
        t = item.get("target") or {}
        if "addr" in t and "name" in t:
            target_func_calls[t["addr"]] = t["name"]
    for item in new:
        t = item.get("target") or {}
        if "addr" in t and "name" in t:
            target_func_calls[t["addr"]] = t["name"]

    return _normalize_known_calls_shape(target_func_calls)


def _get_tag_for_addr(oid: str, addr: int) -> Optional[str]:
    try:
        return api.get_field("llm_function_analysis", oid, "tag", {"func_offset": addr})
    except Exception:
        return None


def annotate_unified_with_tags(
    unified: str,
    name_to_addr: Dict[str, int],
    target_oid: str,
    annotate_kinds: Tuple[str, ...] = ("+",),
) -> str:
    if not unified or not name_to_addr:
        return unified

    name_to_tag: Dict[str, Optional[str]] = {
        name: _get_tag_for_addr(target_oid, addr) for name, addr in name_to_addr.items()
    }

    names_sorted = sorted(name_to_addr.keys(), key=len, reverse=True)
    if not names_sorted:
        return unified

    call_pat = re.compile(r"\b(" + "|".join(re.escape(n) for n in names_sorted) + r")\b\s*\(")

    out_lines: List[str] = []
    for line in unified.splitlines():
        if line.startswith(("---", "+++", "@@")):
            out_lines.append(line)
            continue

        if not line or line[0] not in annotate_kinds:
            out_lines.append(line)
            continue

        prefix, body = line[0], line[1:]
        code_part, sep, trailing = body.partition("//")

        matches = [m.group(1) for m in call_pat.finditer(code_part)]
        if not matches:
            out_lines.append(line)
            continue

        seen: List[str] = []
        for n in matches:
            if n not in seen:
                seen.append(n)

        fragments: List[str] = []
        for n in seen:
            tag = name_to_tag.get(n)
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


def _extract_changed_regions(unified: str, context_lines: int) -> str:
    lines = unified.splitlines()
    n = len(lines)
    if n == 0:
        return unified

    keep: set[int] = set()

    # Always keep headers
    for i, line in enumerate(lines):
        if line.startswith(("---", "+++", "@@")):
            keep.add(i)

    # Keep +/- lines (except decl-only), plus context
    for i, line in enumerate(lines):
        if not line or line[0] not in ("+", "-"):
            continue

        body = line[1:]
        if DECL_LINE_RE.match(body):
            continue

        lo = max(0, i - context_lines)
        hi = min(n, i + context_lines + 1)
        keep.update(range(lo, hi))

    if not keep:
        return unified

    new_lines: List[str] = []
    last = -1
    for idx in sorted(keep):
        if last != -1 and idx > last + 1:
            new_lines.append("...")
        new_lines.append(lines[idx])
        last = idx

    return "\n".join(new_lines) + ("\n" if new_lines else "")


def maybe_compact_unified(
    unified: str,
    budget: int,
    ctx_candidates: Tuple[int, ...] = _COMPACTION_CTX_CANDIDATES,
) -> str:
    if not unified or len(unified) <= budget:
        return unified

    for ctx in ctx_candidates:
        compact = _extract_changed_regions(unified, context_lines=ctx)
        if len(compact) <= budget:
            return compact

    compact = _extract_changed_regions(unified, context_lines=0)
    lines = compact.splitlines()

    note = "... [diff truncated to fit LLM context]"
    note_len = len(note) + 1

    if budget <= 2 * note_len:
        return note + "\n"

    remaining = budget - 2 * note_len
    target_each = remaining // 2

    prefix_lines: List[str] = []
    prefix_chars = 0
    for line in lines:
        ll = len(line) + 1
        if prefix_chars + ll > target_each:
            break
        prefix_lines.append(line)
        prefix_chars += ll

    suffix_rev: List[str] = []
    suffix_chars = 0
    for line in reversed(lines):
        ll = len(line) + 1
        if suffix_chars + ll > target_each:
            break
        suffix_rev.append(line)
        suffix_chars += ll
    suffix_lines = list(reversed(suffix_rev))

    result = [note]
    result.extend(prefix_lines)
    result.append("...")
    result.extend(suffix_lines)
    result.append(note)

    return "\n".join(result) + "\n"
