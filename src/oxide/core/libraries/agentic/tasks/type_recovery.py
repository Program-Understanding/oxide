"""Type-recovery task module (Ω for variable type recovery).

Defines the two deterministic TYPE oracles and registers them with the core dispatcher on import:
  - callee_signature   : a register-passed parameter's C type, fixed by the ABI signature of a known
                         C-library function it is passed to (e.g. arg 1 of `fclose` is `FILE *`).
  - decompiler_pointer : the decompiler's own recovered POINTER type for a variable (char*/FILE*/T**),
                         which a small model routinely discards for a scalar guess.

These are TYPE claims — meaningless for other tasks — so they live here, not in the core library. A
harness that runs type recovery imports this module (which registers the oracles) and then names them
in its Ω (AGENTIC_DOMAIN_ORACLES=callee_signature,decompiler_pointer).
"""
from __future__ import annotations

import re

from oxide.core.libraries.agentic.grounding import register_domain_oracle

# C-library ABI facts: callee -> per-argument fixed type ("" = unconstrained/vararg). These hold for
# ANY binary linking libc (a decompiler ships the same prototypes), so this is generic type-recovery
# knowledge, not benchmark-specific. When a variable reaches one of these at a fixed-type position, its
# type is pinned deterministically — no model inference.
_LIBC_SIG = {
    "fclose": ["FILE *"], "fflush": ["FILE *"], "fileno": ["FILE *"], "feof": ["FILE *"],
    "ferror": ["FILE *"], "clearerr": ["FILE *"], "rewind": ["FILE *"], "ftello": ["FILE *"],
    "ftell": ["FILE *"], "__fpending": ["FILE *"], "__freading": ["FILE *"], "__fwriting": ["FILE *"],
    "__freadable": ["FILE *"], "__fwritable": ["FILE *"], "fputc": ["int", "FILE *"],
    "putc": ["int", "FILE *"], "getc": ["FILE *"], "fgetc": ["FILE *"],
    "fwrite": ["void *", "size_t", "size_t", "FILE *"], "fread": ["void *", "size_t", "size_t", "FILE *"],
    "fseeko": ["FILE *", "off_t", "int"], "fseek": ["FILE *", "long", "int"],
    "fgets": ["char *", "int", "FILE *"], "fputs": ["char *", "FILE *"],
    "setvbuf": ["FILE *", "char *", "int", "size_t"], "fdopen": ["int", "char *"],
    "fopen": ["char *", "char *"], "perror": ["char *"], "puts": ["char *"],
    "strlen": ["char *"], "strnlen": ["char *", "size_t"], "strcmp": ["char *", "char *"],
    "strncmp": ["char *", "char *", "size_t"], "strcpy": ["char *", "char *"],
    "strncpy": ["char *", "char *", "size_t"], "strcat": ["char *", "char *"],
    "strchr": ["char *", "int"], "strrchr": ["char *", "int"], "strstr": ["char *", "char *"],
    "strdup": ["char *"], "strtol": ["char *", "char **", "int"], "strtoul": ["char *", "char **", "int"],
    "memcpy": ["void *", "void *", "size_t"], "memmove": ["void *", "void *", "size_t"],
    "memset": ["void *", "int", "size_t"], "memcmp": ["void *", "void *", "size_t"],
    "free": ["void *"], "realloc": ["void *", "size_t"], "malloc": ["size_t"],
    "calloc": ["size_t", "size_t"], "close": ["int"], "read": ["int", "void *", "size_t"],
    "write": ["int", "void *", "size_t"],
}
# Ghidra x86-64 register-space offsets -> SysV integer argument position (1-based): rdi,rsi,rdx,rcx,r8,r9.
_REGOFF_TO_ARG = {0x38: 1, 0x30: 2, 0x10: 3, 0x08: 4, 0x80: 5, 0x88: 6}
# ... and -> the decompiler's SysV parameter identifier.
_REGOFF_TO_PARAM = {0x38: "param_1", 0x30: "param_2", 0x10: "param_3", 0x08: "param_4",
                    0x80: "param_5", 0x88: "param_6"}


def callee_type_recall_facts(call_tool, question) -> list:
    """For each register-passed PARAMETER named in the question, if the decompilation passes it
    (directly, or through a one-level local alias) to a known library function at a position whose ABI
    type is fixed, emit that type. Returns a list of (vid, ctype, callee, argpos) tuples."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    addr = m.group(1)
    vid_param = {}
    for vm in re.finditer(r"\bV(\d+)\b[^)]*?\bregister\s+(0x[0-9a-fA-F]+)", question or ""):
        k = _REGOFF_TO_ARG.get(int(vm.group(2), 16))
        if k:
            vid_param[f"V{vm.group(1)}"] = k
    if not vid_param:
        return []
    try:
        dec = call_tool("decompile", {"addr": addr})
    except Exception:  # noqa: BLE001
        return []
    if not isinstance(dec, str) or dec.startswith("(no"):
        return []
    call_re = re.compile(r"\b([A-Za-z_]\w*)\s*\(([^()]*)\)")
    facts, taken = [], set()
    for vid, k in vid_param.items():
        if vid in taken:
            continue
        pname = f"param_{k}"
        aliases = {pname}
        for am in re.finditer(rf"\b([A-Za-z_]\w*)\s*=\s*{pname}\b(?![\w.\[])", dec):
            aliases.add(am.group(1))
        alt = "|".join(re.escape(a) for a in aliases)
        for line in dec.splitlines():
            for cm in call_re.finditer(line):
                sig = _LIBC_SIG.get(cm.group(1))
                if not sig:
                    continue
                args = [a.strip() for a in cm.group(2).split(",")]
                for j, a in enumerate(args):
                    if j < len(sig) and sig[j] and re.search(rf"(?<![\w])(?:{alt})(?![\w])", a):
                        facts.append((vid, sig[j], cm.group(1), j + 1))
                        taken.add(vid)
                        break
                if vid in taken:
                    break
            if vid in taken:
                break
    return facts


def decompiler_pointer_facts(call_tool, question) -> list:
    """Parse the decompiler's OWN declared type for each queried variable and, when it declared a
    POINTER (char*/FILE*/T**), emit it. Storage resolves deterministically — a register by the calling
    convention, a stack slot -0xNN to Ghidra's `local_NN`. Returns a list of (vid, ctype) tuples."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    addr = m.group(1)
    vid_name = {}
    for vm in re.finditer(r"\bV(\d+)\b[^)]*?\bregister\s+(0x[0-9a-fA-F]+)", question or ""):
        nm = _REGOFF_TO_PARAM.get(int(vm.group(2), 16))
        if nm:
            vid_name[f"V{vm.group(1)}"] = nm
    for vm in re.finditer(r"\bV(\d+)\b[^)]*?\bstack\s+(-?0x[0-9a-fA-F]+)", question or ""):
        off = abs(int(vm.group(2), 16))
        vid_name[f"V{vm.group(1)}"] = f"local_{off:x}"
    if not vid_name:
        return []
    try:
        dec = call_tool("decompile", {"addr": addr})
    except Exception:  # noqa: BLE001
        return []
    if not isinstance(dec, str) or dec.startswith("(no"):
        return []
    decl = {}
    for dm in re.finditer(r"\b([A-Za-z_][\w ]*?[A-Za-z_])\s+(\*+)\s*(param_\d+|local_[0-9a-f]+)\b", dec):
        base = re.sub(r"\s+", " ", dm.group(1)).strip()
        if base in ("return", "else", "goto", "case"):
            continue
        decl.setdefault(dm.group(3), f"{base} {dm.group(2)}")
    return [(vid, decl[nm]) for vid, nm in vid_name.items() if nm in decl]


# Argument list allowing ONE level of nested parens, so a forwarded call with casts
# (`FUN_x(param_1, (int)param_2, param_3)`) is captured whole instead of truncating at the first `(`.
_CALL_ARGS = r"\(((?:[^()]|\([^()]*\))*)\)"
_USERFN_CALL = re.compile(r"\b(FUN_[0-9a-fA-F]+)\s*" + _CALL_ARGS)
_LIBC_CALL = re.compile(r"\b([A-Za-z_]\w*)\s*" + _CALL_ARGS)


def _callee_addr(name: str):
    """`FUN_0010b353` -> `0x0010b353` (Ghidra encodes the entry address in the auto-name)."""
    m = re.match(r"FUN_0*([0-9a-fA-F]+)$", name or "")
    return f"0x{m.group(1)}" if m else None


def _libc_type_of_param(dec: str, pname: str):
    """If `pname` (or a one-level local alias) is passed to a known libc function at a fixed-type
    position anywhere in `dec`, return (ctype, callee, argpos-1based); else None."""
    aliases = {pname}
    for am in re.finditer(rf"\b([A-Za-z_]\w*)\s*=\s*{re.escape(pname)}\b(?![\w.\[])", dec):
        aliases.add(am.group(1))
    alt = "|".join(re.escape(a) for a in aliases)
    for line in dec.splitlines():
        for cm in _LIBC_CALL.finditer(line):
            sig = _LIBC_SIG.get(cm.group(1))
            if not sig:
                continue
            args = [a.strip() for a in cm.group(2).split(",")]
            for j, a in enumerate(args):
                if j < len(sig) and sig[j] and re.search(rf"(?<![\w])(?:{alt})(?![\w])", a):
                    return (sig[j], cm.group(1), j + 1)
    return None


def interprocedural_param_usage_facts(call_tool, question) -> list:
    """Recover a forwarded parameter's type ONE HOP away. When a queried register parameter has no
    local usage but is passed straight into a user function `FUN_xxxx`, decompile that callee and, if
    it hands the forwarded argument to a known libc function at a fixed-type position, pin that type.
    This is the deterministic inter-procedural signal thin wrapper/forwarder functions need (they carry
    no intra-procedural evidence). Returns (vid, ctype, callee, callee_param, libc_fn, argpos) tuples."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    vid_param = {}
    for vm in re.finditer(r"\bV(\d+)\b[^)]*?\bregister\s+(0x[0-9a-fA-F]+)", question or ""):
        k = _REGOFF_TO_ARG.get(int(vm.group(2), 16))
        if k:
            vid_param[f"V{vm.group(1)}"] = k
    if not vid_param:
        return []
    try:
        dec = call_tool("decompile", {"addr": m.group(1)})
    except Exception:  # noqa: BLE001
        return []
    if not isinstance(dec, str) or dec.startswith("(no"):
        return []
    facts, taken, callee_cache = [], set(), {}
    for vid, k in vid_param.items():
        if vid in taken:
            continue
        pname = f"param_{k}"
        aliases = {pname}
        for am in re.finditer(rf"\b([A-Za-z_]\w*)\s*=\s*{re.escape(pname)}\b(?![\w.\[])", dec):
            aliases.add(am.group(1))
        alt = "|".join(re.escape(a) for a in aliases)
        for line in dec.splitlines():
            for cm in _USERFN_CALL.finditer(line):
                args = [a.strip() for a in cm.group(2).split(",")]
                pos = next((j for j, a in enumerate(args)
                            if re.search(rf"(?<![\w])(?:{alt})(?![\w])", a)), None)
                if pos is None:
                    continue
                caddr = _callee_addr(cm.group(1))
                if not caddr:
                    continue
                if caddr not in callee_cache:
                    try:
                        cd = call_tool("decompile", {"addr": caddr})
                    except Exception:  # noqa: BLE001
                        cd = ""
                    callee_cache[caddr] = cd if isinstance(cd, str) and not cd.startswith("(no") else ""
                cdec = callee_cache[caddr]
                if not cdec:
                    continue
                res = _libc_type_of_param(cdec, f"param_{pos + 1}")
                if res:
                    ctype, lc, apos = res
                    facts.append((vid, ctype, cm.group(1), f"param_{pos + 1}", lc, apos))
                    taken.add(vid)
                    break
            if vid in taken:
                break
    return facts


# --- normalized Ω oracles (return {"vid","ctype","source","claim","reason"}) + registration --------
def _oracle_callee_signature(call_tool, question) -> list:
    out = []
    for vid, ctype, callee, argpos in callee_type_recall_facts(call_tool, question):
        out.append({
            "vid": vid, "ctype": ctype, "source": "deterministic_callee_signature",
            "claim": (f"{vid} has C type `{ctype}` — it is passed as argument {argpos} to "
                      f"`{callee}`, whose library ABI signature fixes that parameter's type. "
                      f"Treat as established; this overrides any weaker guess for {vid}."),
            "reason": f"ABI signature of {callee} fixes argument {argpos}"})
    return out


def _oracle_decompiler_pointer(call_tool, question) -> list:
    out = []
    for vid, ctype in decompiler_pointer_facts(call_tool, question):
        out.append({
            "vid": vid, "ctype": ctype, "source": "deterministic_decompiler_pointer",
            "claim": (f"{vid} has C type `{ctype}` — this is the decompiler's own recovered POINTER "
                      f"type for the variable. Treat as established; the decompiler's pointer "
                      f"inference overrides a scalar guess for {vid}."),
            "reason": "decompiler declared this a pointer type"})
    return out


def _oracle_interprocedural_param_usage(call_tool, question) -> list:
    out = []
    for vid, ctype, callee, cparam, lc, apos in interprocedural_param_usage_facts(call_tool, question):
        out.append({
            "vid": vid, "ctype": ctype, "source": "deterministic_interprocedural_param_usage",
            "claim": (f"{vid} has C type `{ctype}` — it is forwarded to user function `{callee}` "
                      f"(as its `{cparam}`), which passes it as argument {apos} to `{lc}`, whose "
                      f"library ABI signature fixes that parameter's type. Treat as established; this "
                      f"inter-procedural evidence overrides any weaker guess for {vid}."),
            "reason": f"forwarded to {callee}; {lc} ABI fixes argument {apos} one hop away"})
    return out


register_domain_oracle("callee_signature", _oracle_callee_signature)
register_domain_oracle("decompiler_pointer", _oracle_decompiler_pointer)
register_domain_oracle("interprocedural_param_usage", _oracle_interprocedural_param_usage)
