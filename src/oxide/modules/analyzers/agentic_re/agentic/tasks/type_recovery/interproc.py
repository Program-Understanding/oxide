"""interprocedural oracle: follow a forwarded parameter out of the function -- to a library
terminus, or failing that to the first callee that commits to a concrete type."""
from __future__ import annotations

import json
import re
from .common import _CALL_ARGS, _REGNAME_TO_ARG, _SPILL_STORE, _W2T, _arg_is_value, _decl_pointer_map, _is_vague_pointer, _libc_type_of_param, _split_args, _vid_sizes, _vid_stack_offsets, _vid_to_arg


def _spilled_home_args(call_tool, addr, question) -> dict:
    """{'V12': 3, ...} — a STACK variable the prologue spills an argument register into is that
    parameter's HOME SLOT, so it holds the parameter's value and any parameter-directed oracle should
    be able to address it.

    Ground truth lists a register parameter and its home slot as two SEPARATE variables of the same
    type, so an oracle that only understands registers resolves one of the pair and is silent on the
    other — the miss costs exactly what the hit gains. Measured on `stat/out_mount_point`: `prefix_len`
    (rdx) and `prefix_len-local` (its slot) are both `size_t`, both were typed `char *`, and both
    scored 1/6."""
    out = {}
    for vid, off in _vid_stack_offsets(question).items():
        try:
            sv = call_tool("stack_var", {"addr": addr, "offset": off})
        except Exception:  # noqa: BLE001
            continue
        if not isinstance(sv, str):
            continue
        sm = _SPILL_STORE.search(sv)                     # first store into the slot = prologue spill
        k = _REGNAME_TO_ARG.get(sm.group(1)) if sm else None
        if k:
            out[vid] = k
    return out


_USERFN_CALL = re.compile(r"\b(FUN_[0-9a-fA-F]+)\s*" + _CALL_ARGS)


def _callee_addr(name: str):
    """`FUN_0010b353` -> `0x0010b353` (Ghidra encodes the entry address in the auto-name)."""
    m = re.match(r"FUN_0*([0-9a-fA-F]+)$", name or "")
    return f"0x{m.group(1)}" if m else None


_MAX_HOPS = 3   # follow forwarder chains up to this depth (version_etc forwards 2-3 levels deep)


# Ghidra type names that carry NO commitment: the decompiler emits these when it could not infer a
# type at all, so they must not be read as evidence of anything.
_NOCOMMIT_DECL = re.compile(r"^(?:undefined\d*|void|code)$")


# ... versus the ones that are a positive commitment to "not a pointer".
_INT_DECL = {"char", "byte", "bool", "short", "ushort", "int", "uint", "long", "ulong",
             "longlong", "ulonglong", "int1", "int2", "int4", "int8", "uint1", "uint2",
             "uint4", "uint8", "size_t", "ssize_t", "wchar_t", "float", "double"}


_INT_WIDTH = {"char": 1, "unsigned char": 1, "short": 2, "unsigned short": 2, "int": 4,
              "unsigned int": 4, "long": 8, "unsigned long": 8, "long long": 8,
              "unsigned long long": 8, "float": 4, "double": 8, "size_t": 8, "ssize_t": 8,
              "wchar_t": 4, "int1": 1, "int2": 2, "int4": 4, "int8": 8,
              "uint1": 1, "uint2": 2, "uint4": 4, "uint8": 8}


def _width_matched_int(ctype: str, size) -> str:
    """Keep the callee's declared integer when it already fits the slot, else the same-signedness
    integer that does. `ulong` -> `unsigned long`, so the emitted type is valid C."""
    norm = {"ulong": "unsigned long", "uint": "unsigned int", "ushort": "unsigned short",
            "byte": "unsigned char", "ulonglong": "unsigned long long",
            "longlong": "long long", "bool": "char"}.get(ctype.strip(), ctype.strip())
    if not size or _INT_WIDTH.get(norm) == size:
        return norm
    base = _W2T.get(size)
    if not base:
        return norm
    return f"unsigned {base}" if norm.startswith("unsigned") else base


def _sig_param_decls(dec: str) -> dict:
    """{'param_1': 'char *', 'param_2': 'long'} -- the decompiler's declared type for every parameter,
    read off the function's SIGNATURE line. Unlike `_decl_pointer_map` this reports NON-pointer
    declarations too, which is the whole point: `long` is a positive claim that a value is not a
    pointer, and that claim is what distinguishes a length from a string."""
    for ln in (dec or "").splitlines():
        ln = ln.strip()
        if not ln.endswith(")") or "param_" not in ln:
            continue
        m = re.match(r"^[A-Za-z_][\w \*]*\s+\**\w+\s*\((.*)\)$", ln)
        if not m:
            continue
        out = {}
        for a in m.group(1).split(","):
            am = re.match(r"^\s*([A-Za-z_][\w ]*?)\s*(\**)\s*(param_\d+)\s*$", a)
            if am:
                base = re.sub(r"\s+", " ", am.group(1)).strip()
                out[am.group(3)] = f"{base} {am.group(2)}" if am.group(2) else base
        if out:
            return out
    return {}


def _derefs_param(dec: str, pname: str) -> bool:
    """Is `pname` (or a one-level alias) ever dereferenced in `dec`? Used only to VETO a "not a
    pointer" verdict, so it is deliberately over-eager -- a false positive costs coverage, never
    precision. Note `(char *)(param_2 + param_1)` is correctly not a dereference: the cast applies to
    the sum, which is the signature of `base + length`, not of a load."""
    # Erase cast tokens first. Ghidra's dominant load idiom is `*(char *)(p + i)`, where the cast's
    # closing paren sits between the `*` and the expression; without this the pattern below cannot
    # reach `p` and the single most common dereference in the corpus goes unseen. Stripping casts
    # turns it into `*(p + i)`. Note this deliberately does NOT create a false positive for
    # `(char *)(p + n)` -> `(p + n)`: with no leading `*` that is still an address computation, not a
    # load, which is exactly the `base + length` case this oracle exists to recognise.
    dec = re.sub(r"\(\s*[A-Za-z_][\w ]*\*+\s*\)", "", dec or "")
    aliases = {pname}
    for am in re.finditer(rf"\b([A-Za-z_]\w*)\s*=\s*{re.escape(pname)}\b(?![\w.\[])", dec):
        aliases.add(am.group(1))
    # OFFSET-alias: `local_20 = (param_1 + 1)` (a cast sum, once the cast is stripped). If such a
    # local is later dereferenced then `pname` is an address, because only an address can be offset
    # and loaded through. This is what proves WHICH operand of `base + length` is the base -- the
    # motivating case, `stat/out_mount_point`, turns on exactly this and nothing else distinguishes
    # `param_1` from `param_2` in the callee that consumes them.
    for am in re.finditer(rf"\b([A-Za-z_]\w*)\s*=\s*\(?\s*{re.escape(pname)}\s*\+", dec):
        aliases.add(am.group(1))
    alt = "|".join(re.escape(a) for a in aliases)
    pats = (rf"(?<![\w])(?:{alt})\s*(?:\[|->)",                                   # p[i] / p->f
            rf"\*\s*\(?\s*(?:{alt})(?![\w])",                                     # *p, *(p)
            rf"\*\s*\([^()]*(?<![\w])(?:{alt})(?![\w])[^()]*\)")                  # *(p + N)
    return any(re.search(p, dec) for p in pats)


def _ptr_evidence(dec: str, name: str) -> bool:
    """Is `name` established as an ADDRESS in `dec` — declared a pointer, dereferenced (directly or
    through an offset-alias), or passed to a library function at a pointer position?"""
    if "*" in (_decl_pointer_map(dec).get(name) or ""):
        return True
    if _derefs_param(dec, name):
        return True
    hit = _libc_type_of_param(dec, name)
    return bool(hit and "*" in hit[0])


def _sum_sibling_is_pointer(dec: str, pname: str) -> bool:
    """In `(T *)(x + y)` the decompiler declares BOTH operands `long`, because it cannot tell a base
    from a length either. But if the SIBLING is independently established as an address, this operand
    must be the offset — pointer arithmetic has exactly one pointer operand. That is a deterministic
    tie-break for the one shape the integer-only-operator gate cannot reach, since `+` is precisely
    what a pointer does support."""
    stripped = re.sub(r"\(\s*[A-Za-z_][\w ]*\*+\s*\)", "", dec or "")
    p = re.escape(pname)
    for m in re.finditer(rf"\(\s*(?:{p}\s*\+\s*([A-Za-z_]\w*)|([A-Za-z_]\w*)\s*\+\s*{p})\s*\)",
                         stripped):
        sib = m.group(1) or m.group(2)
        if sib and sib != pname and _ptr_evidence(dec, sib):
            return True
    return False


# Operations C does not define on a pointer. `+`/`-`/comparison are deliberately ABSENT: they are
# exactly what a pointer supports, and `(char *)(a + b)` -- a base plus a length -- is the shape where
# the decompiler declares BOTH operands `long` and neither the decompiler nor this oracle can say which
# is which. Requiring one of these instead of trusting the declaration is what makes the claim sound.
_ARITH = r"(?:\*|/|%|<<|>>|&(?!&)|\|(?!\|)|\^)"


_SCALAR_OPS = (
    (rf"(?<![\w]){{p}}\s*{_ARITH}\s*", "is multiplied/divided/shifted/masked"),
    # A leading operand is REQUIRED here, else a dereference `*p` reads as a multiplication.
    (rf"[\w\)\]]\s*{_ARITH}\s*\(?\s*(?:\([\w ]*\)\s*)?(?<![\w]){{p}}(?![\w])", "is a right operand of "
     "an integer-only operator"),
    (r"\w+\s*\[\s*(?:\([\w ]*\)\s*)?(?<![\w]){p}(?![\w])\s*\]", "is used as an array subscript"),
)


def _scalar_evidence(dec: str, pname: str) -> str:
    """Why this value cannot be an address, or "" if there is no such evidence.

    A `long` declaration is NOT evidence: Ghidra emits it as freely as `undefined8`, and measured over
    stat/du/ln it agreed with ground truth on only 8 of 14 forwarded parameters -- it typed genuine
    `void *` and `char *` values `long` whenever they were consumed by arithmetic. Demanding an
    operation that no pointer supports raises that to a claim worth certifying."""
    dec = re.sub(r"\(\s*[A-Za-z_][\w ]*\*+\s*\)", "", dec or "")     # drop casts, as in _derefs_param
    aliases = {pname}
    for am in re.finditer(rf"\b([A-Za-z_]\w*)\s*=\s*{re.escape(pname)}\b(?![\w.\[])", dec):
        aliases.add(am.group(1))
    alt = "|".join(re.escape(a) for a in aliases)
    for pat, why in _SCALAR_OPS:
        if re.search(pat.replace("{p}", f"(?:{alt})"), dec):
            return why
    if _sum_sibling_is_pointer(dec, pname):
        return "is added to a value that is itself provably an address, so it is the offset"
    return ""


def _resolve_forward_usage(call_tool, dec, fname, pname, depth, seen):
    """Fallback for `_resolve_forward_chain` when a forwarding chain never reaches libc: report the
    FIRST function along the chain that COMMITTED to a concrete type for the forwarded position, plus
    whether the value is dereferenced anywhere up to that point.

    Shallowest-concrete-wins, and `undefined8` is not concrete. Deepest-wins was considered and is
    wrong on the motivating example: in `stat/out_mount_point`, `pformat` (a real `char *`) and
    `prefix_len` (a `size_t`) are forwarded side by side and BOTH are declared `long` two hops out,
    where they only ever appear in `p < (char *)(param_2 + param_1)`. One hop out they separate --
    `char *` and `undefined8`. The first callee that commits is the one that had the local evidence to
    do so; a deeper one has merged the two roles into an addition.

    Returns (ctype, fn, param, deref_seen) or None."""
    decl = _sig_param_decls(dec).get(pname, "")
    base = decl.replace("*", "").strip()
    deref = _derefs_param(dec, pname)
    if "*" in decl:
        return (("void *" if _NOCOMMIT_DECL.match(base) else decl), fname, pname, deref, "")
    why = _scalar_evidence(dec, pname) if base in _INT_DECL else ""
    if why:
        return (decl, fname, pname, deref, why)
    # A bare `long`/`int` declaration with no integer-only operation behind it is treated exactly like
    # `undefined8`: no commitment. Keep walking -- the evidence may be one hop further on.
    if depth <= 0:
        return None
    aliases = {pname}
    for am in re.finditer(rf"\b([A-Za-z_]\w*)\s*=\s*{re.escape(pname)}\b(?![\w.\[])", dec):
        aliases.add(am.group(1))
    alt = "|".join(re.escape(a) for a in aliases)
    for cm in _USERFN_CALL.finditer(dec):
        args = _split_args(cm.group(2))
        pos = next((j for j, a in enumerate(args) if _arg_is_value(a, aliases)), None)
        if pos is None:
            continue
        caddr = _callee_addr(cm.group(1))
        if not caddr or caddr in seen:
            continue
        seen.add(caddr)
        try:
            cd = call_tool("decompile", {"addr": caddr})
        except Exception:  # noqa: BLE001
            continue
        if not isinstance(cd, str) or cd.startswith("(no"):
            continue
        r = _resolve_forward_usage(call_tool, cd, cm.group(1), f"param_{pos + 1}", depth - 1, seen)
        if r:
            return (r[0], r[1], r[2], deref or r[3], r[4])
    return None


def _resolve_forward_chain(call_tool, dec, pname, depth, seen):
    """Follow `pname` through forwarder calls until it reaches a fixed-ABI libc position. Returns
    (ctype, libc_fn, argpos) or None. Recurses into a user-function callee when `pname` is forwarded
    to it (aliases followed one level), bounded by `depth` and a `seen` set of callee addresses."""
    hit = _libc_type_of_param(dec, pname)          # does it reach a libc fn HERE?
    if hit:
        return hit
    if depth <= 0:
        return None
    aliases = {pname}
    for am in re.finditer(rf"\b([A-Za-z_]\w*)\s*=\s*{re.escape(pname)}\b(?![\w.\[])", dec):
        aliases.add(am.group(1))
    alt = "|".join(re.escape(a) for a in aliases)
    for cm in _USERFN_CALL.finditer(dec):
        args = _split_args(cm.group(2))
        pos = next((j for j, a in enumerate(args) if _arg_is_value(a, aliases)), None)
        if pos is None:
            continue
        caddr = _callee_addr(cm.group(1))
        if not caddr or caddr in seen:
            continue
        seen.add(caddr)
        try:
            cd = call_tool("decompile", {"addr": caddr})
        except Exception:  # noqa: BLE001
            continue
        if not isinstance(cd, str) or cd.startswith("(no"):
            continue
        r = _resolve_forward_chain(call_tool, cd, f"param_{pos + 1}", depth - 1, seen)
        if r:
            return r
    return None


def interprocedural_param_usage_facts(call_tool, question) -> list:
    """Recover a forwarded parameter's type across a chain of user-function forwarders (up to
    `_MAX_HOPS` deep). When a queried register parameter has no local usage but is passed into a user
    function `FUN_xxxx`, follow it through that callee (and its callees) until it reaches a known libc
    function at a fixed-type position, then pin that type. This is the deterministic inter-procedural
    signal thin wrapper/forwarder functions need (they carry no intra-procedural evidence).

    When the chain reaches no libc position -- the common case, since most forwarding is between user
    functions -- fall back to how the CALLEE uses the value: the first callee that committed to a
    concrete declared type for the forwarded position, and whether the value is ever dereferenced.
    That yields a pointer floor or, uniquely among the oracles, a NEGATIVE claim ("not a pointer"),
    which is what separates a forwarded length from a forwarded string.

    Returns (vid, ctype, callee, callee_param, libc_fn, argpos, kind) tuples, where kind is
    `libc` | `declared_ptr` | `declared_scalar` (libc_fn/argpos are empty for the latter two)."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    vid_param = dict(_vid_to_arg(question))
    # Also address each parameter's spilled HOME SLOT, which holds the same value and so has the same
    # type. A register and its home slot are two distinct entities in the answer, so both are mapped
    # and both get certified independently — resolving only the register leaves the other half of the
    # pair to be guessed, at identical cost.
    vid_param.update(_spilled_home_args(call_tool, m.group(1), question))
    if not vid_param:
        return []
    try:
        dec = call_tool("decompile", {"addr": m.group(1)})
    except Exception:  # noqa: BLE001
        return []
    if not isinstance(dec, str) or dec.startswith("(no"):
        return []
    facts, taken, callee_cache = [], set(), {}
    sizes = _vid_sizes(question)
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
                args = _split_args(cm.group(2))
                pos = next((j for j, a in enumerate(args) if _arg_is_value(a, aliases)), None)
                if pos is None:
                    continue
                caddr = _callee_addr(cm.group(1))
                # `_USERFN_CALL` also matches the DEFINITION line, whose "arguments" are the parameter
                # declarations -- so without this guard the oracle resolves a parameter against its own
                # function's signature and reports it as "forwarded to FUN_<self>". That is not
                # inter-procedural evidence (it is `decompiler_pointer`'s and `callee_signature`'s job,
                # and both run before this oracle), and taking it short-circuits the real walk.
                if not caddr or int(caddr, 16) == int(m.group(1), 16):
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
                # follow the forwarded arg through this callee AND its own callees (multi-hop)
                res = _resolve_forward_chain(call_tool, cdec, f"param_{pos + 1}",
                                             _MAX_HOPS - 1, {caddr})
                if res:
                    ctype, lc, apos = res
                    if "*" in ctype and (sizes.get(vid) or 8) < 8:
                        continue                    # same realizability check as the fallback below
                    facts.append((vid, ctype, cm.group(1), f"param_{pos + 1}", lc, apos, "libc"))
                    taken.add(vid)
                    break
                # No libc position anywhere in the chain -- the overwhelmingly common case, and where
                # this oracle used to give up. The chain still carries evidence: read the first
                # callee that COMMITTED to a concrete type for the forwarded position.
                use = _resolve_forward_usage(call_tool, cdec, cm.group(1), f"param_{pos + 1}",
                                             _MAX_HOPS - 1, {caddr})
                if use:
                    uty, ufn, uparam, uderef, uwhy = use
                    # Physical realizability, enforced HERE rather than only in the trailer's
                    # size guard: the verifier now calls the oracles as tools directly, which bypasses
                    # that guard entirely, so an impossible fact would reach the model unchallenged.
                    # It fires: all 4 pointer errors measured over stat/du/ln were `byte *` certified
                    # onto 4-byte slots in `du/__strftime_internal` (GT `int`).
                    if "*" in uty and (sizes.get(vid) or 8) < 8:
                        continue
                    if "*" in uty:
                        kind = "declared_ptr"
                    elif uderef:
                        kind = ""       # declared an integer yet dereferenced -- contradictory, abstain
                    else:
                        kind = "declared_scalar"
                    if kind == "declared_scalar":
                        uty = _width_matched_int(uty, sizes.get(vid))
                    if kind:
                        facts.append((vid, uty, ufn, uparam, uwhy, 0, kind))
                        taken.add(vid)
                        break
            if vid in taken:
                break
    return facts


def _oracle_interprocedural_param_usage(call_tool, question) -> list:
    out = []
    for vid, ctype, callee, cparam, lc, apos, kind in \
            interprocedural_param_usage_facts(call_tool, question):
        if kind == "libc":
            out.append({
                "vid": vid, "ctype": ctype, "source": "deterministic_interprocedural_param_usage",
                "floor": _is_vague_pointer(ctype),
                "claim": (f"{vid} has C type `{ctype}` — it is forwarded to user function `{callee}` "
                          f"(as its `{cparam}`), which passes it as argument {apos} to `{lc}`, whose "
                          f"library ABI signature fixes that parameter's type. Treat as established; "
                          f"this inter-procedural evidence overrides any weaker guess for {vid}."),
                "reason": f"forwarded to {callee}; {lc} ABI fixes argument {apos} one hop away"})
        elif kind == "declared_ptr":
            # A declared type one hop out is weaker than a library ABI, so it is always a FLOOR: it
            # can raise a scalar answer to a pointer but never overwrite a pointee the agents named.
            out.append({
                "vid": vid, "ctype": ctype, "source": "deterministic_interprocedural_param_usage",
                "floor": True, "mode": "floor",
                "claim": (f"{vid} IS A POINTER — it is forwarded into `{callee}`, where the "
                          f"decompiler independently declared that position `{ctype}`. Treat "
                          f"\"{vid} is a pointer\" as established; if your type for {vid} is not a "
                          f"pointer, replace it. If you already have a more specific pointer type, "
                          f"keep yours."),
                "reason": f"{callee} declares the forwarded {cparam} as {ctype}"})
        elif kind == "declared_scalar":
            # The mirror of the pointer floor, and the only oracle claim that is NEGATIVE: it asserts
            # "not a pointer" and leaves the choice of integer to whoever answers. Justified because
            # the callee committed to an integer AND the value is dereferenced nowhere along the
            # chain -- had it been an address, the callee that consumes it would have loaded from it.
            out.append({
                "vid": vid, "ctype": ctype, "source": "deterministic_interprocedural_param_usage",
                "floor": False, "mode": "scalar",
                "claim": (f"{vid} IS NOT A POINTER — it is forwarded into `{callee}`, where it "
                          f"{lc or 'is used only as an integer'} (an operation C does not define on a "
                          f"pointer) and is dereferenced nowhere along the chain. It is a count, "
                          f"length, index or flag. If your type for {vid} is a pointer, replace it "
                          f"with an integer of the slot's width; if you already have an integer, keep "
                          f"yours."),
                "reason": f"in {callee} the forwarded {cparam} {lc}; never dereferenced"})
    return out
