from __future__ import annotations

import re
from typing import Any, List, Optional

# Whitespace
RE_WS = re.compile(r"\s+")

# Tokens
RE_FUN = re.compile(r"\bFUN_([0-9a-fA-F]+)\b")
FUN_TOKEN_RE = re.compile(r"\bFUN_([0-9a-fA-F]+)\b")

RE_LAB = re.compile(r"\bLAB_[0-9a-fA-F]+\b")
RE_DAT = re.compile(r"\bDAT_[0-9a-fA-F]+\b")
RE_PTR = re.compile(r"\bPTR_[0-9a-fA-F]+\b")

RE_TMP = re.compile(r"\b(?:p{0,3}[a-z]{1,3}Var\d+)\b")
RE_LOCAL = re.compile(r"\blocal_[A-Za-z0-9_]+\b")

RE_PARAM = re.compile(r"\bparam_[0-9A-Fa-f]+\b")
RE_IN = re.compile(r"\bin_[A-Za-z0-9_]+\b")
RE_EXTRAOUT = re.compile(r"\bextraout_[A-Za-z0-9_]+\b")
RE_UNAFF = re.compile(r"\bunaff_[A-Za-z0-9_]+\b")

VAR_TOKEN_RE = re.compile(
    r"(local_[A-Za-z0-9_]+|"
    r"(?:p{0,3}[a-z]{1,3}Var\d+)|"
    r"DAT_[0-9A-Fa-f]+|"
    r"PTR_[0-9A-Fa-f]+|"
    r"param_[0-9A-Fa-f]+|"
    r"in_[A-Za-z0-9_]+|"
    r"extraout_[A-Za-z0-9_]+|"
    r"unaff_[A-Za-z0-9_]+)"
)

# Canon helpers
RE_TYPE = re.compile(
    r"\b(?:"
    r"undefined\d+|"
    r"__uid_t|__gid_t|"
    r"u?int(?:8|16|32|64)?_t|"
    r"int|uint|long|ulong|short|ushort|char|uchar|bool|size_t|"
    r"FILE|"
    r"void"
    r")\b"
)
RE_PARENRUN = re.compile(r"[()]{2,}")

# Decl line normalization
RE_DECL_LINE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_\s\*]*)\s+([A-Za-z_][A-Za-z0-9_]*)\s*;\s*$"
)

# For compaction filtering
DECL_LINE_RE = re.compile(
    r"^\s*(?:"
    r"undefined\d+|int|uint|long|short|char|bool|size_t|FILE|"
    r"__uid_t|__gid_t|void\s*\*"
    r")\b.*;\s*$"
)

# Decmap prefix
RE_DECMAP_PREFIX = re.compile(r"^\s*\d+:(.*)$")


def lines_equal_ignoring_ws(a: List[str], b: List[str]) -> bool:
    if len(a) != len(b):
        return False
    for x, y in zip(a, b):
        if RE_WS.sub(" ", x).strip() != RE_WS.sub(" ", y).strip():
            return False
    return True


def normalize_decl_line(s: str) -> str:
    st = s.strip()
    if "(" in st or ")" in st:
        return s
    m = RE_DECL_LINE.match(st)
    if not m:
        return s
    name = m.group(2)
    return f"<TYPE> {name};"


def normalize_lines(lines: List[str]) -> List[str]:
    out: List[str] = []
    for s in lines:
        s = normalize_decl_line(s)
        s = RE_LAB.sub("LAB_<ADDR>", s)
        s = RE_DAT.sub("DAT_<ADDR>", s)
        s = RE_PTR.sub("PTR_<ADDR>", s)
        s = RE_TMP.sub("<TMP>", s)
        s = RE_LOCAL.sub("<LOCAL>", s)
        s = RE_PARAM.sub("<PARAM>", s)
        s = RE_IN.sub("<IN>", s)
        s = RE_EXTRAOUT.sub("<EXTRAOUT>", s)
        s = RE_UNAFF.sub("<UNAFF>", s)
        s = RE_WS.sub(" ", s).strip()
        out.append(s)
    return out


def canon_decomp_noise(s: str) -> str:
    s = RE_LAB.sub("LAB_<ADDR>", s)
    s = RE_DAT.sub("DAT_<ADDR>", s)
    s = RE_PTR.sub("PTR_<ADDR>", s)
    s = RE_TMP.sub("<TMP>", s)
    s = RE_LOCAL.sub("<LOCAL>", s)
    s = RE_PARAM.sub("<PARAM>", s)
    s = RE_IN.sub("<IN>", s)
    s = RE_EXTRAOUT.sub("<EXTRAOUT>", s)
    s = RE_UNAFF.sub("<UNAFF>", s)
    s = RE_TYPE.sub("<TYPE>", s)
    s = RE_PARENRUN.sub("()", s)
    s = RE_WS.sub(" ", s).strip()
    return s


def canon_block(lines: List[str]) -> str:
    return " ".join(canon_decomp_noise(x) for x in lines)


def parse_addr_any(v: Any) -> Optional[int]:
    try:
        if isinstance(v, int):
            return v
        if isinstance(v, str):
            s = v.strip()
            m = FUN_TOKEN_RE.fullmatch(s) or FUN_TOKEN_RE.search(s)
            if m:
                return int(m.group(1), 16)
            if s.lower().startswith("0x"):
                return int(s, 16)
            if s.isdigit():
                return int(s, 10)
        if isinstance(v, dict):
            for k in ("addr", "address", "start", "start_addr", "ea"):
                if k in v:
                    a = parse_addr_any(v[k])
                    if a is not None:
                        return a
            for k in ("name", "label"):
                if k in v and isinstance(v[k], str):
                    m = FUN_TOKEN_RE.search(v[k])
                    if m:
                        return int(m.group(1), 16)
        return None
    except Exception:
        return None


def tok_from_any(v: Any) -> Optional[str]:
    a = parse_addr_any(v)
    return f"FUN_{a:08x}" if a is not None else None


def sanitize_name(name: str) -> str:
    name = name.strip()
    name = re.sub(r"\s+", "_", name)
    name = re.sub(r"[^A-Za-z0-9_.$@+-]", "", name)
    return name or "unknown"
