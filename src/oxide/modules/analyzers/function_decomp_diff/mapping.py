from __future__ import annotations

from typing import Any, Dict, List, Tuple

from oxide.core import api

from text_tools import (
    RE_FUN,
    RE_LAB,
    VAR_TOKEN_RE,
    RE_LOCAL,
    RE_TMP,
    RE_DAT,
    RE_PTR,
    RE_PARAM,
    RE_IN,
    RE_EXTRAOUT,
    RE_UNAFF,
    tok_from_any,
)

_VAR_MAP_MIN_SUPPORT = 2


def build_fun_projection_map(
    baseline_oid: str,
    target_oid: str,
    baseline_func_addr: Any,
    target_func_addr: Any,
) -> Dict[str, str]:
    projmap_base: Dict[str, str] = {}

    base_tok = tok_from_any(baseline_func_addr)
    tgt_tok = tok_from_any(target_func_addr)
    if base_tok and tgt_tok:
        projmap_base.setdefault(base_tok, tgt_tok)

    try:
        diff = (
            api.retrieve(
                "function_call_diff",
                [target_oid, baseline_oid],
                {"target": str(target_func_addr), "baseline": str(baseline_func_addr)},
            )
            or {}
        )
    except Exception:
        diff = {}

    paired = diff.get("fc_paired") or diff.get("paired") or []
    for item in paired:
        b_side = item.get("baseline", {}) or {}
        t_side = item.get("target", {}) or {}

        b_tok = tok_from_any(b_side.get("addr"))
        t_tok = tok_from_any(t_side.get("addr"))
        if b_tok and t_tok:
            projmap_base[b_tok] = t_tok

    return projmap_base


def project_fun_tokens(lines: List[str], projmap: Dict[str, str]) -> List[str]:
    num_map: Dict[int, int] = {}
    for k, v in projmap.items():
        try:
            num_map[int(k[4:], 16)] = int(v[4:], 16)
        except Exception:
            pass

    candidates = (0, 0x100000, 0x200000, -0x100000, 0x1000, -0x1000)

    seen: List[int] = []
    for s in lines[:120]:
        for m in RE_FUN.finditer(s):
            try:
                seen.append(int(m.group(1), 16))
            except Exception:
                pass
        if len(seen) >= 64:
            break

    bias = 0
    if seen:
        best_hits = -1
        for b in candidates:
            hits = sum(1 for a in seen if (a - b) in num_map)
            if hits > best_hits:
                best_hits = hits
                bias = b

    def _sub(m):
        a = int(m.group(1), 16)
        if a in num_map:
            return f"FUN_{num_map[a]:08x}"
        ab = a - bias
        if ab in num_map:
            return f"FUN_{(num_map[ab] + bias):08x}"
        return f"FUN_{a:08x}"

    return [RE_FUN.sub(_sub, s) for s in lines]


def build_lab_map_from_opcodes(
    base_orig: List[str],
    tgt_orig: List[str],
    opcodes: List[Tuple[str, int, int, int, int]],
) -> Dict[str, str]:
    lab_map: Dict[str, str] = {}

    for tag, i1, i2, j1, j2 in opcodes:
        if tag != "equal":
            continue

        span = min(i2 - i1, j2 - j1)
        for off in range(span):
            b_line = base_orig[i1 + off]
            t_line = tgt_orig[j1 + off]

            b_labs = RE_LAB.findall(b_line)
            t_labs = RE_LAB.findall(t_line)
            if not b_labs or not t_labs:
                continue
            if len(b_labs) != len(t_labs):
                continue

            for bl, tl in zip(b_labs, t_labs):
                existing = lab_map.get(bl)
                if existing is None:
                    lab_map[bl] = tl
                elif existing != tl:
                    lab_map.pop(bl, None)

    return lab_map


def project_lab_tokens(lines: List[str], lab_map: Dict[str, str]) -> List[str]:
    if not lab_map:
        return lines

    def _sub(m):
        tok = m.group(0)
        return lab_map.get(tok, tok)

    return [RE_LAB.sub(_sub, s) for s in lines]


def _extract_var_tokens(line: str) -> List[str]:
    return [m.group(0) for m in VAR_TOKEN_RE.finditer(line)]


def _same_var_kind(a: str, b: str) -> bool:
    if RE_LOCAL.fullmatch(a):
        return bool(RE_LOCAL.fullmatch(b))
    if RE_TMP.fullmatch(a):
        return bool(RE_TMP.fullmatch(b))
    if RE_DAT.fullmatch(a):
        return bool(RE_DAT.fullmatch(b))
    if RE_PTR.fullmatch(a):
        return bool(RE_PTR.fullmatch(b))
    if RE_PARAM.fullmatch(a):
        return bool(RE_PARAM.fullmatch(b))
    if RE_IN.fullmatch(a):
        return bool(RE_IN.fullmatch(b))
    if RE_EXTRAOUT.fullmatch(a):
        return bool(RE_EXTRAOUT.fullmatch(b))
    if RE_UNAFF.fullmatch(a):
        return bool(RE_UNAFF.fullmatch(b))
    return False


def _min_support_for(vb: str) -> int:
    # Temps are unstable. Current policy is effectively "disable temp mapping".
    return 999999 if RE_TMP.fullmatch(vb) else _VAR_MAP_MIN_SUPPORT


def build_var_map(
    base_orig: List[str],
    tgt_orig: List[str],
    base_norm: List[str],
    tgt_norm: List[str],
    opcodes: List[Tuple[str, int, int, int, int]],
) -> Dict[str, str]:
    pair_counts: Dict[Tuple[str, str], int] = {}

    for tag, i1, i2, j1, j2 in opcodes:
        if tag != "equal":
            continue

        length = i2 - i1
        for k in range(length):
            b_idx = i1 + k
            t_idx = j1 + k

            if base_norm[b_idx] != tgt_norm[t_idx]:
                continue

            b_vars = _extract_var_tokens(base_orig[b_idx])
            t_vars = _extract_var_tokens(tgt_orig[t_idx])

            if not b_vars or not t_vars:
                continue
            if len(b_vars) != len(t_vars):
                continue

            for vb, vt in zip(b_vars, t_vars):
                if not _same_var_kind(vb, vt):
                    continue
                pair_counts[(vb, vt)] = pair_counts.get((vb, vt), 0) + 1

    by_baseline: Dict[str, Dict[str, int]] = {}
    for (vb, vt), cnt in pair_counts.items():
        by_baseline.setdefault(vb, {})
        by_baseline[vb][vt] = by_baseline[vb].get(vt, 0) + cnt

    var_map: Dict[str, str] = {}
    for vb, tgt_counts in by_baseline.items():
        vt_best, c_best = max(tgt_counts.items(), key=lambda kv: kv[1])
        if c_best < _min_support_for(vb):
            continue
        var_map[vb] = vt_best

    return var_map


def project_var_tokens(lines: List[str], var_map: Dict[str, str]) -> List[str]:
    if not var_map:
        return lines

    keys = sorted(var_map.keys(), key=len, reverse=True)
    import re as _re
    pat = r"\b(" + "|".join(_re.escape(k) for k in keys) + r")\b"
    re_keys = _re.compile(pat)

    def _sub(m):
        vb = m.group(1)
        return var_map.get(vb, vb)

    return [re_keys.sub(_sub, s) for s in lines]
