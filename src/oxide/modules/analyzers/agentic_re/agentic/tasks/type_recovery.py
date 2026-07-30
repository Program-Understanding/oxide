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

import json
import re

from agentic.grounding import register_domain_oracle, register_domain_evidence
from agentic.tools.registry import tool as _tool

# C-library ABI facts: callee -> per-argument fixed type ("" = unconstrained/vararg). These hold for
# ANY binary linking libc (a decompiler ships the same prototypes), so this is generic type-recovery
# knowledge, not benchmark-specific. When a variable reaches one of these at a fixed-type position, its
# type is pinned deterministically — no model inference.
DEFAULT_ORACLES = "callee_signature,decompiler_pointer,interprocedural_param_usage,spilled_param"

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
    # printf / error family: the FILE* stream and the char* format sit at fixed positions (the rest are
    # varargs). Very common in wrapper/forwarder functions (version_etc, error reporters, quotearg).
    "fprintf": ["FILE *", "char *"], "vfprintf": ["FILE *", "char *"], "printf": ["char *"],
    "vprintf": ["char *"], "sprintf": ["char *", "char *"], "snprintf": ["char *", "size_t", "char *"],
    "vsnprintf": ["char *", "size_t", "char *"], "error": ["int", "int", "char *"],
    "dprintf": ["int", "char *"], "asprintf": ["char **", "char *"],
    # The *_unlocked stdio family + ungetc. coreutils uses these almost EXCLUSIVELY (they are the
    # single-threaded fast paths), so their absence blanked the callee-signature signal across the
    # whole benchmark: `cut_fields` calls getc_unlocked/putchar_unlocked/fwrite_unlocked/feof_unlocked/
    # ferror_unlocked/ungetc and matched NONE of them. Same fixed ABI as the locking variants.
    "getc_unlocked": ["FILE *"], "fgetc_unlocked": ["FILE *"], "getchar_unlocked": [],
    "putc_unlocked": ["int", "FILE *"], "fputc_unlocked": ["int", "FILE *"],
    "putchar_unlocked": ["int"],
    "fwrite_unlocked": ["void *", "size_t", "size_t", "FILE *"],
    "fread_unlocked": ["void *", "size_t", "size_t", "FILE *"],
    "fputs_unlocked": ["char *", "FILE *"], "fgets_unlocked": ["char *", "int", "FILE *"],
    "feof_unlocked": ["FILE *"], "ferror_unlocked": ["FILE *"], "fflush_unlocked": ["FILE *"],
    "clearerr_unlocked": ["FILE *"], "fileno_unlocked": ["FILE *"],
    "ungetc": ["int", "FILE *"],
}
# Ghidra x86-64 register-space offsets -> SysV integer argument position (1-based): rdi,rsi,rdx,rcx,r8,r9.
_REGOFF_TO_ARG = {0x38: 1, 0x30: 2, 0x10: 3, 0x08: 4, 0x80: 5, 0x88: 6}
# ... and -> the decompiler's SysV parameter identifier.
_REGOFF_TO_PARAM = {0x38: "param_1", 0x30: "param_2", 0x10: "param_3", 0x08: "param_4",
                    0x80: "param_5", 0x88: "param_6"}


# The question's variable lines are parsed in FOUR places; keep ONE pattern per storage kind so the
# oracles cannot drift apart. (They already had: `spilled_param` used `[ \t(]*stack` while the others
# used `[ \t(]*\bstack` — the same anchoring family that caused the 775ca3f mis-mapping bug.)
_V_REGISTER = re.compile(r"\bV(\d+)\b[ \t(]*\bregister\s+(0x[0-9a-fA-F]+)")
_V_STACK = re.compile(r"\bV(\d+)\b[ \t(]*\bstack\s+(-?0x[0-9a-fA-F]+)")


def _vid_to_arg(question: str) -> dict:
    """{'V1': 1, ...} — a REGISTER variable's 1-based System V integer-argument position."""
    out = {}
    for vm in _V_REGISTER.finditer(question or ""):
        k = _REGOFF_TO_ARG.get(int(vm.group(2), 16))
        if k:
            out[f"V{vm.group(1)}"] = k
    return out


def _vid_stack_offsets(question: str) -> dict:
    """{'V4': '-0x28', ...} — a STACK variable's frame offset, verbatim from the question."""
    return {f"V{vm.group(1)}": vm.group(2) for vm in _V_STACK.finditer(question or "")}


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


# A pointer whose POINTEE is unknown (`undefined *`, `void **`, `undefined8 *`). Such a fact asserts
# the CLASS only — "this is a pointer" — not what it points to, so it must be certified as a FLOOR
# (a lower bound) rather than as an exact type. Certifying it exactly lets a decompiler `undefined *`
# overwrite a correct `char *`: measured on printf/c_strcasecmp, 4 such overrides cost 12.12 points.
_VAGUE_PTR = re.compile(r"^\s*(?:undefined\d*|void)\s*\*+\s*$", re.I)


def _is_vague_pointer(ctype: str) -> bool:
    return bool(_VAGUE_PTR.match(str(ctype or "")))


# A pointer carrying NO pointee information: `void *`, `undefined8 *`, or a bare/anonymous
# `struct *`. Distinct from `_is_vague_pointer` only by also admitting the tagless `struct *` the
# model emits when it has recognised an aggregate but cannot describe it. A `shape` certification
# replaces exactly these; anything with a named pointee (`char *`, `FILE *`, `Hash_table *`) wins.
_SHAPELESS_PTR = re.compile(r"^\s*(?:undefined\d*|void|struct|union)\s*\*+\s*$", re.I)


def is_shapeless_pointer(ctype: str) -> bool:
    return bool(_SHAPELESS_PTR.match(str(ctype or "")))


def callee_type_recall_facts(call_tool, question) -> list:
    """For each register-passed PARAMETER named in the question, if the decompilation passes it
    (directly, or through a one-level local alias) to a known library function at a position whose ABI
    type is fixed, emit that type. Returns a list of (vid, ctype, callee, argpos) tuples."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    addr = m.group(1)
    vid_param = _vid_to_arg(question)
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
                    if j < len(sig) and sig[j] and _arg_is_value(a, aliases):
                        facts.append((vid, sig[j], cm.group(1), j + 1))
                        taken.add(vid)
                        break
                if vid in taken:
                    break
            if vid in taken:
                break
    return facts


def _decl_pointer_map(dec: str) -> dict:
    """{'param_4': 'void **', 'local_30': 'char *', ...} — the decompiler's OWN declared pointer type
    for each parameter / local identifier in the decompilation."""
    decl = {}
    for dm in re.finditer(r"\b([A-Za-z_][\w ]*?[A-Za-z_])\s+(\*+)\s*(param_\d+|local_[0-9a-f]+)\b", dec):
        base = re.sub(r"\s+", " ", dm.group(1)).strip()
        if base in ("return", "else", "goto", "case"):
            continue
        decl.setdefault(dm.group(3), f"{base} {dm.group(2)}")
    return decl


def decompiler_pointer_facts(call_tool, question) -> list:
    """Parse the decompiler's OWN declared type for each queried variable and, when it declared a
    POINTER (char*/FILE*/T**), emit it. Storage resolves deterministically — a register by the calling
    convention, a stack slot -0xNN to Ghidra's `local_NN`. Returns a list of (vid, ctype) tuples."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    addr = m.group(1)
    vid_name = _vid_to_ghidra_name(question)
    if not vid_name:
        return []
    try:
        dec = call_tool("decompile", {"addr": addr})
    except Exception:  # noqa: BLE001
        return []
    if not isinstance(dec, str) or dec.startswith("(no"):
        return []
    decl = _decl_pointer_map(dec)
    return [(vid, decl[nm]) for vid, nm in vid_name.items() if nm in decl]


# x86-64 SysV: the register a spilled argument was moved from -> its 1-based parameter index.
_REGNAME_TO_ARG = {"rdi": 1, "edi": 1, "rsi": 2, "esi": 2, "rdx": 3, "edx": 3,
                   "rcx": 4, "ecx": 4, "r8": 5, "r8d": 5, "r9": 6, "r9d": 6}
_SPILL_STORE = re.compile(r"mov\s+(?:[a-z]+\s+ptr\s+)?\[[^\]]+\]\s*,\s*([a-z][a-z0-9]+)")


def spilled_param_facts(call_tool, question) -> list:
    """A stack slot that the prologue spills an ARGUMENT REGISTER into is a copy of that parameter, so
    it has that parameter's type. Resolve slot -> register (stack_var's first store) -> SysV parameter
    -> the parameter's type (the decompiler's declared pointer type, else its library-ABI type). This
    fixes the common failure where the model mis-maps a spilled local to the WRONG parameter and
    inherits the wrong type. Returns (vid, ctype, param, register) tuples."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    addr = m.group(1)
    slots = _vid_stack_offsets(question)
    if not slots:
        return []
    try:
        dec = call_tool("decompile", {"addr": addr})
    except Exception:  # noqa: BLE001
        return []
    if not isinstance(dec, str) or dec.startswith("(no"):
        return []
    decl = _decl_pointer_map(dec)
    facts = []
    for vid, off in slots.items():
        try:
            sv = call_tool("stack_var", {"addr": addr, "offset": off})
        except Exception:  # noqa: BLE001
            continue
        if not isinstance(sv, str):
            continue
        sm = _SPILL_STORE.search(sv)                         # first store = the prologue spill
        k = _REGNAME_TO_ARG.get(sm.group(1)) if sm else None
        if not k:
            continue
        pname = f"param_{k}"
        ctype = decl.get(pname) or (_libc_type_of_param(dec, pname) or (None,))[0]
        if ctype:
            facts.append((vid, ctype, pname, sm.group(1)))
    return facts


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
                if j < len(sig) and sig[j] and _arg_is_value(a, aliases):
                    return (sig[j], cm.group(1), j + 1)
    return None


_MAX_HOPS = 3   # follow forwarder chains up to this depth (version_etc forwards 2-3 levels deep)

# Ghidra type names that carry NO commitment: the decompiler emits these when it could not infer a
# type at all, so they must not be read as evidence of anything.
_NOCOMMIT_DECL = re.compile(r"^(?:undefined\d*|void|code)$")
# ... versus the ones that are a positive commitment to "not a pointer".
_INT_DECL = {"char", "byte", "bool", "short", "ushort", "int", "uint", "long", "ulong",
             "longlong", "ulonglong", "int1", "int2", "int4", "int8", "uint1", "uint2",
             "uint4", "uint8", "size_t", "ssize_t", "wchar_t", "float", "double"}


# --- signedness oracle -----------------------------------------------------------------------------
# The compiler is FORCED to pick between these: `shr` vs `sar`, `movzx` vs `movsx`, `div` vs `idiv`
# encode the signedness of the C expression they implement, so they are facts about the source type
# rather than heuristics. Rotates are included because a C rotate is only expressible on an unsigned
# value (`(x >> n) | (x << (w - n))` is wrong for a negative x), and that is the idiom compilers emit
# `ror`/`rol` for.
#
# Motivation, measured: on `sha384sum/sha512_process_block` 171 of 179 variables scored 5/6, halting at
# `AgreeCPrimitive` -- they passed `AgreeSignIgnoredCPrimitive`, so the class, the width and the
# not-a-pointer decision were all right and the ONLY error was the sign bit. Exact-match precision there
# was 1/179 against TRex's 173/179, and those 178 false positives were 27% of every false positive the
# agent produced over a 100-function sample. Benchmark-wide, 62.7% of scalar ground truth is unsigned.
_SIGN_UNS = {"shr", "ror", "rol", "movzx", "div"}
_SIGN_SGN = {"sar", "movsx", "movsxd", "idiv"}
# Only the fixed-width spelling resolves to the same structural type ground truth uses: the scorer's
# typedef chain sends `u64` and `size_t` both to `uint64_t` -> `ulonglong`, while `ulong` is a DIFFERENT
# builtin and would not match. Verified by substitution: `uint64_t` scored 172/179 exact on that
# function where `long` scored 1/179.
_W2U = {1: "uint8_t", 2: "uint16_t", 4: "uint32_t", 8: "uint64_t"}
_DIS_LINE = re.compile(r"^(0x[0-9a-fA-F]+)\s+([a-z][a-z0-9]*)\s*(.*)$")
_R64 = {}
for _q, _d, _w, _b in (("rax", "eax", "ax", "al"), ("rbx", "ebx", "bx", "bl"),
                       ("rcx", "ecx", "cx", "cl"), ("rdx", "edx", "dx", "dl"),
                       ("rsi", "esi", "si", "sil"), ("rdi", "edi", "di", "dil"),
                       ("rbp", "ebp", "bp", "bpl"), ("rsp", "esp", "sp", "spl")):
    for _n in (_q, _d, _w, _b):
        _R64[_n] = _q
for _i in range(8, 16):
    for _s in ("", "d", "w", "b"):
        _R64[f"r{_i}{_s}"] = f"r{_i}"


def _canon_reg(tok: str):
    return _R64.get(re.sub(r"[^a-z0-9]", "", (tok or "").lower()))


def _parse_disasm(text: str) -> list:
    """[(addr:int, mnemonic, operands)] in address order, from the `disassemble` tool's text."""
    out = []
    for ln in (text or "").splitlines():
        m = _DIS_LINE.match(ln.strip())
        if m:
            out.append((int(m.group(1), 16), m.group(2), m.group(3).split("<===")[0].strip()))
    return out


def _regs_in(ops: str) -> set:
    return {r for r in (_canon_reg(t) for t in re.findall(r"[a-z][a-z0-9]*", ops or "")) if r}


def _ops_on_reg(dis, pos, reg, back: bool, span: int = 14) -> list:
    """Sign-revealing mnemonics applied to `reg` near `pos`, walking one def-use step.

    A SHA-512 style local is never shifted in place: the value is computed in a register, stored to the
    slot, and later reloaded. So the evidence sits either just BEFORE a store into the slot (the
    computation) or just AFTER a load from it (the consumption), never on the slot access itself -- which
    is why a scan of the variable's own accesses abstains on exactly the case that motivated this.

    The walk stops as soon as `reg` is redefined by a plain `mov reg, <other>`, so operations belonging
    to an unrelated value are not attributed to this one."""
    found = []
    rng = range(pos - 1, max(-1, pos - 1 - span), -1) if back else \
        range(pos + 1, min(len(dis), pos + 1 + span))
    for j in rng:
        _a, mn, ops = dis[j]
        if reg not in _regs_in(ops):
            continue
        # The register must appear as a BARE operand, not inside `[...]`. `movzx eax, byte ptr [rax]`
        # zero-extends the value the register POINTS AT, which says nothing about the pointer's own
        # signedness -- measured on `cksum/cksum_slice8` V5, where exactly this attributed `movzx` to a
        # `uchar *` and produced the oracle's only wrong claim.
        bare = re.sub(r"\[[^\]]*\]", "", ops)
        if reg not in _regs_in(bare):
            if mn == "mov" and _canon_reg((ops.split(",")[0] if "," in ops else "")) == reg:
                break
            continue
        # `movzx`/`movsx` extend their SOURCE, so only a source occurrence says anything about this
        # value. The destination often ALIASES the address register -- `movzx eax, byte ptr [rax]`
        # extends the byte rax points at, and reading `eax` as the value made this oracle's only wrong
        # claim (`cksum/cksum_slice8` V5, a `uchar *`, certified `uint64_t`).
        if mn in ("movzx", "movsx", "movsxd"):
            src = ops.split(",", 1)[1] if "," in ops else ""
            if reg not in _regs_in(re.sub(r"\[[^\]]*\]", "", src)):
                continue
        if mn in _SIGN_UNS or mn in _SIGN_SGN:
            found.append(mn)
        if mn == "mov":
            dst = _canon_reg((ops.split(",")[0] if "," in ops else ""))
            if dst == reg:                     # reg (re)defined here -- chain boundary
                break
    return found


def _sign_evidence(call_tool, addr, accesses, reg_name=None) -> tuple:
    """(unsigned_hits, signed_hits, why) for one variable, from its storage accesses.

    `reg_name` is the canonical 64-bit register for a REGISTER variable, else None for a stack slot.
    For a slot, `movzx eax, byte ptr [rbp-N]` really does zero-extend the slot's contents and is
    evidence; for a register, the register inside `[...]` is an ADDRESS, so the extension describes the
    pointee -- `cksum/cksum_slice8` V5 (`uchar *`) was mis-claimed exactly so."""
    uns, sgn, why = [], [], []
    for acc in accesses or []:
        m = re.match(r"\s*(0x[0-9a-fA-F]+)\s*:\s*([a-z][a-z0-9]*)\s*(.*)$", str(acc))
        if not m:
            continue
        # A window CENTRED on the access, not one long dump from the function entry: `AGENTIC_OUT_CAP`
        # truncates the tool's text (40000 chars ~ 1115 instructions), so on a large function -- exactly
        # the case this oracle was built for -- every access past that point fell outside the window and
        # the oracle silently abstained on all 179 variables of sha512_process_block.
        try:
            dis = _parse_disasm(call_tool("disassemble",
                                          {"addr": m.group(1), "n_instructions": 34}))
        except Exception:  # noqa: BLE001
            continue
        if not dis:
            continue
        pos = {a: i for i, (a, _mn, _o) in enumerate(dis)}.get(int(m.group(1), 16))
        if pos is None:
            continue
        mn, ops = m.group(2), m.group(3)
        if mn in _SIGN_UNS or mn in _SIGN_SGN:                # directly on the slot / register
            # For a REGISTER variable the register must appear OUTSIDE `[...]`. Inside brackets it is
            # an ADDRESS, so `movzx eax, byte ptr [rdx]` describes the POINTEE, not rdx -- that is
            # exactly what mis-claimed `cksum/cksum_slice8` V5 (`uchar *`) as an unsigned integer.
            if reg_name and reg_name not in _regs_in(re.sub(r"\[[^\]]*\]", "", ops)):
                continue
            (uns if mn in _SIGN_UNS else sgn).append(mn)
            why.append(f"{mn} at {m.group(1)}")
            continue
        parts = [p.strip() for p in ops.split(",")]
        if len(parts) != 2:
            continue
        dst_mem, src_mem = "[" in parts[0], "[" in parts[1]
        if dst_mem and not src_mem:                           # store INTO the slot: look BACK
            reg = _canon_reg(parts[1])
            hits = _ops_on_reg(dis, pos, reg, back=True) if reg else []
        elif src_mem and not dst_mem:                         # load FROM the slot: look FORWARD
            reg = _canon_reg(parts[0])
            hits = _ops_on_reg(dis, pos, reg, back=False) if reg else []
        else:
            continue
        for h in hits:
            (uns if h in _SIGN_UNS else sgn).append(h)
        if hits:
            why.append(f"{'/'.join(sorted(set(hits)))} on the value at {m.group(1)}")
    return (len(uns), len(sgn), "; ".join(why[:3]))


def _reg_of(res):
    """The canonical 64-bit register `register_usage` reported on, e.g. {"register": "rdx"} -> rdx."""
    m = re.search(r'"register"\s*:\s*"([a-z0-9]+)"', str(res))
    return _canon_reg(m.group(1)) if m else None


def signedness_facts(call_tool, question) -> list:
    """Recover the SIGN of an integer variable from opcodes the compiler had no choice about.

    Returns (vid, ctype, why) for variables with unsigned-only evidence and no signed evidence. Signed
    evidence only VETOES; it is never emitted, because the model already defaults to signed, so a
    `signed` claim buys nothing while risking an override."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    addr = m.group(1)
    sizes = _vid_sizes(question)
    regs, slots = _vid_to_reg_offsets(question), _vid_stack_offsets(question)
    facts = []
    for vid in sorted(set(regs) | set(slots), key=lambda v: int(v[1:])):
        w = sizes.get(vid)
        if w not in _W2U:
            continue                                          # only sized integers can carry a sign
        try:
            if vid in slots:
                res = call_tool("stack_var", {"addr": addr, "offset": slots[vid]})
            else:
                res = call_tool("register_usage", {"addr": addr, "reg": regs[vid]})
        except Exception:  # noqa: BLE001
            continue
        try:
            acc = json.loads(res).get("accesses") if isinstance(res, str) else None
        except Exception:  # noqa: BLE001
            acc = re.findall(r'"(0x[0-9a-fA-F]+:[^"]+)"', str(res))
        u, s, why = _sign_evidence(call_tool, addr, acc or [],
                                   reg_name=None if vid in slots else _reg_of(res))
        if u and not s:
            facts.append((vid, _W2U[w], why))
    return facts


def _vid_to_reg_offsets(question: str) -> dict:
    """{'V1': '0x38', ...} — a REGISTER variable's Ghidra register-space offset, as `register_usage`
    wants it."""
    return {f"V{vm.group(1)}": vm.group(2) for vm in _V_REGISTER.finditer(question or "")}


def _vid_sizes(question: str) -> dict:
    """{'V1': 8, 'V2': 4} from the VARIABLES block. The slot width is GIVEN, so it overrides a
    declared integer width read out of a callee: the callee's parameter may be a truncated view of
    the value (`int param_3` for an 8-byte slot), and the claim we are making is only "not a
    pointer" -- the width should come from the fact we are certain about."""
    return {m.group(1): int(m.group(2))
            for m in re.finditer(r"^(V\d+)\t[^\t]+\t(\d+)\s*$", question or "", re.M)}


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


# A cast token, for stripping: either something ending in `*`, or a known scalar type name. It must
# NOT match `(param_1)`, which is why a bare identifier is not accepted here.
_CAST_TOK = re.compile(r"\(\s*(?:[A-Za-z_][\w ]*\*+|u?int\d{0,2}_t|undefined\d*|long long|"
                       r"unsigned \w+|long|ulong|int|uint|char|byte|short|ushort|longlong|"
                       r"ulonglong|size_t|ssize_t|wchar_t|float|double|bool)\s*\)")


def _arg_is_value(arg: str, aliases) -> bool:
    """Is this call argument the value ITSELF, rather than something computed FROM it?

    Both the libc lookup and the forwarding walk used to accept any argument that merely MENTIONED the
    parameter, which silently equates `f(p)` with `f(*p)` and `f(p[i])` -- and those transfer nothing,
    because the callee's parameter type then describes the POINTEE. Measured on `stat/c_strcasecmp`
    (`char *s1`): the walk followed `c_tolower(*s1)` into `int c_tolower(int)` and certified the string
    as an integer, wrong for 4 of the function's 8 variables. Only an exact match, modulo casts and
    redundant parens, licenses transferring the callee's type back to the caller's value."""
    a = _CAST_TOK.sub("", arg or "").strip()
    while a.startswith("(") and a.endswith(")"):
        a = a[1:-1].strip()
    return a in aliases


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
        args = [a.strip() for a in cm.group(2).split(",")]
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
        args = [a.strip() for a in cm.group(2).split(",")]
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
                args = [a.strip() for a in cm.group(2).split(",")]
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


# --- normalized Ω oracles (return {"vid","ctype","source","claim","reason"}) + registration --------
# --- struct-shape oracle --------------------------------------------------------------------------
# Production decompilers render an aggregate pointer as a pointer to a PRIMITIVE because they never
# assemble the observed field accesses into a struct: on the classic singly-linked-list example,
# Ghidra emits `undefined4 *`, Binary Ninja `int32_t *`, Hex-Rays `unsigned int *`. The evidence for
# the aggregate is nonetheless present and deterministic -- a load at `[p + N]` of a given width is a
# field, and a field whose value flows back into p is a self-reference. `struct_shape` reports those
# observations; this renders them as a C type. No model involvement, and no ground truth.
_W2T = {1: "char", 2: "short", 4: "int", 8: "long"}


def _render_shape(fields: dict, selfrefs) -> str:
    """`{'0x0': 4, '0x8': 8}` + selfref `['0x8']` -> `struct t1 { int field_0; struct t1 *field_8; } *`.
    A self-referential aggregate is TAGGED (`t1`) because C cannot express recursion anonymously."""
    sr = set(selfrefs or ())
    parts = []
    for off_hex, w in sorted(fields.items(), key=lambda kv: int(kv[0], 16)):
        off = int(off_hex, 16)
        parts.append(f"struct t1 *field_{off}" if off_hex in sr
                     else f"{_W2T.get(w, 'long')} field_{off}")
    return f"struct {'t1 ' if sr else ''}{{ {'; '.join(parts)}; }} *"


def struct_shape_facts(call_tool, question) -> list:
    """Certify an aggregate pointer for a register parameter whose field accesses are observable, and
    for every slot that provably holds the same pointer (its prologue home, and any local assigned a
    self-referential field). Returns (vid, ctype, why) tuples."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    addr = m.group(1)
    args, slots = _vid_to_arg(question), _vid_stack_offsets(question)
    byoff = {hex(int(o, 16)): vid for vid, o in slots.items()}   # normalized frame offset -> vid
    facts = []
    for vid, k in sorted(args.items()):
        try:
            sh = call_tool("struct_shape", {"addr": addr, "reg": f"param_{k}"})
            sh = json.loads(sh) if isinstance(sh, str) else sh
        except Exception:  # noqa: BLE001
            continue
        if not isinstance(sh, dict) or not sh.get("is_aggregate") or not sh.get("fields"):
            continue
        ctype = _render_shape(sh["fields"], sh.get("self_ref_offsets"))
        facts.append((vid, ctype, f"param_{k} fields {sorted(sh['fields'])}"))
        home = sh.get("home_slot_qoff")               # the spill slot IS the same pointer
        if home and hex(int(home, 16)) in byoff:
            facts.append((byoff[hex(int(home, 16))], ctype, f"home slot of param_{k}"))
        for soff, foff in (sh.get("alias_slots") or {}).items():
            # only a slot holding a SELF-REFERENTIAL field is known to be this same struct pointer;
            # a slot holding any other field is some other type and is left to the agents.
            if foff in set(sh.get("self_ref_offsets") or ()) and hex(int(soff, 16)) in byoff:
                facts.append((byoff[hex(int(soff, 16))], ctype,
                              f"holds self-referential field_{int(foff, 16)}"))
    return facts


def _oracle_struct_shape(call_tool, question) -> list:
    out = []
    for vid, ctype, why in struct_shape_facts(call_tool, question):
        # MODE `shape`: more informative than a bare pointer, less than a named source type. It
        # overrides a non-pointer or a shapeless pointer (`void *`, `struct *`) but DEFERS to any
        # pointer whose pointee the agents named -- we recover layout, never a source-level name.
        out.append({"vid": vid, "ctype": ctype, "mode": "shape", "why": why})
    return out


def _oracle_callee_signature(call_tool, question) -> list:
    out = []
    for vid, ctype, callee, argpos in callee_type_recall_facts(call_tool, question):
        out.append({
            "vid": vid, "ctype": ctype, "source": "deterministic_callee_signature",
            "floor": _is_vague_pointer(ctype),
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
            "floor": _is_vague_pointer(ctype),
            "claim": (f"{vid} has C type `{ctype}` — this is the decompiler's own recovered POINTER "
                      f"type for the variable. Treat as established; the decompiler's pointer "
                      f"inference overrides a scalar guess for {vid}."),
            "reason": "decompiler declared this a pointer type"})
    return out


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


def _oracle_spilled_param(call_tool, question) -> list:
    out = []
    for vid, ctype, pname, reg in spilled_param_facts(call_tool, question):
        out.append({
            "vid": vid, "ctype": ctype, "source": "deterministic_spilled_param",
            "floor": _is_vague_pointer(ctype),
            "claim": (f"{vid} has C type `{ctype}` — its stack slot is where the prologue spills "
                      f"`{reg}` (`{pname}`), so it is a copy of that parameter and shares its type. "
                      f"Treat as established; this overrides a guess that mis-maps the slot to another "
                      f"parameter."),
            "reason": f"prologue spills {reg} ({pname}) into this slot"})
    return out


def _vid_to_ghidra_name(question: str) -> dict:
    """{'V1': 'param_1', 'V4': 'local_28', ...} — a queried variable's storage resolved to the
    decompiler's identifier. A register maps by the SysV calling convention, a stack slot -0xNN to
    Ghidra's `local_NN`. (Same rules the oracles use, factored out so the evidence gatherer and the
    oracles cannot drift apart.)"""
    vid_name = {}
    for vm in _V_REGISTER.finditer(question or ""):
        nm = _REGOFF_TO_PARAM.get(int(vm.group(2), 16))
        if nm:
            vid_name[f"V{vm.group(1)}"] = nm
    for vm in _V_STACK.finditer(question or ""):
        vid_name[f"V{vm.group(1)}"] = f"local_{abs(int(vm.group(2), 16)):x}"
    return vid_name


def variable_evidence(call_tool, question) -> str:
    """Assemble, deterministically, the per-variable evidence the model provably never gathers itself.

    Measured 2026-07-26 over 72 logged agent tool calls on 4 functions: `xrefs_to`, `read_values` and
    `compute` were chosen ZERO times, and no worker ever followed a value into a callee — even though
    every `disassemble` result opens with the callee list. The agent is competent at INFERRING a type
    from evidence in hand and has no policy for DECIDING what to gather; so the gathering happens here,
    in code, and the model is left with only the inference.

    One line per variable, deliberately: a partial-but-bulky context measurably HURTS this model (the
    disassemble-window A/B: doubling the assembly cost -5.6 and -11.8 on the two functions that already
    worked). The aim is completeness per variable, not volume.
    """
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return ""
    vid_name = _vid_to_ghidra_name(question)
    if not vid_name:
        return ""
    try:
        dec = call_tool("decompile", {"addr": m.group(1)})
    except Exception:  # noqa: BLE001
        return ""
    if not isinstance(dec, str) or dec.startswith("(no"):
        return ""
    decl = dict(_decl_pointer_map(dec))
    # ...plus every NON-pointer local/param declaration. `_decl_pointer_map` deliberately keeps only
    # pointers (it feeds an oracle that certifies pointer types); for evidence we want the whole
    # declaration table. Verified on cut_fields against ground truth: local_18->size_t, local_20->size_t,
    # local_28->long, local_34/local_38->uint are all right, and the model currently has to re-derive
    # them from the decompilation by hand.
    for dm in re.finditer(r"^\s*([A-Za-z_][\w ]*?[\w])\s+(param_\d+|local_[0-9a-f]+)\s*;", dec, re.M):
        base = re.sub(r"\s+", " ", dm.group(1)).strip()
        if base not in ("return", "else", "goto", "case"):
            decl.setdefault(dm.group(2), base)
    # the signature line carries the parameter declarations (they are not in the body)
    sm = re.search(r"^[\w \*]+\s+\w+\s*\((.*?)\)\s*$", dec, re.M)
    if sm:
        for a in sm.group(1).split(","):
            am = re.match(r"\s*([A-Za-z_][\w ]*?[\w])\s*(\**)\s*(param_\d+)\s*$", a)
            if am:
                decl.setdefault(am.group(3), (am.group(1) + " " + am.group(2)).strip())
    lines = []
    for vid in sorted(vid_name, key=lambda v: int(v[1:])):
        nm = vid_name[vid]
        bits = []
        # (a) the call the value flows into — the signal the agent never goes and gets. Applied to
        #     STACK LOCALS too, not just register params (the callee_signature oracle covers only
        #     the register case), which is what makes this more than a restatement of the oracles.
        hit = _libc_type_of_param(dec, nm)
        if hit:
            ctype, callee, apos = hit
            bits.append(f"passed to {callee}() as argument {apos}, whose ABI fixes that parameter as `{ctype}`")
        # (b) what the decompiler itself declared for the slot
        if nm in decl:
            bits.append(f"decompiler declares it `{decl[nm]}`")
        if not bits:
            bits.append("no call-flow or pointer declaration found — infer from its access pattern")
        lines.append(f"{vid} ({nm}): " + "; ".join(bits))
    if not lines:
        return ""
    return ("DETERMINISTIC EVIDENCE (already gathered for you from the decompilation and the callees' "
            "ABI signatures — this is factual, do NOT re-derive it with tools):\n" + "\n".join(lines))


register_domain_evidence("variable_evidence", variable_evidence)

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


# --- the oracles as INDIVIDUAL tools --------------------------------------------------------------
# `static_type_oracles` runs all of them and is the right call when nothing is known. Exposing each
# one separately is what makes selection meaningful: the oracles differ in the EVIDENCE they read, so
# a reviewer looking at a function full of libc calls wants a different one than a reviewer looking at
# a stack slot that mirrors a parameter. Each description therefore leads with the evidence it needs,
# which is the only thing the model has to choose on.
_ORACLE_PARAMS = {"addr": {"type": "string"}, "variables": {"type": "string"}}


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


@_tool("signedness", "Recover the SIGN of an integer variable from opcodes the compiler had no "
                     "choice about (shr/sar, movzx/movsx, div/idiv, rotates).")
def signedness(ctx, addr: str, variables: str) -> list:
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


def _oracle_signedness(call_tool, question) -> list:
    out = []
    for vid, ctype, why in signedness_facts(call_tool, question):
        out.append({
            "vid": vid, "ctype": ctype, "source": "deterministic_signedness",
            "floor": False, "mode": "sign",
            "claim": (f"{vid} IS UNSIGNED — {why}. The compiler must choose between the unsigned and "
                      f"signed form of these instructions (`shr`/`sar`, `movzx`/`movsx`, `div`/`idiv`; "
                      f"a rotate is only expressible on an unsigned value), so this is a fact about the "
                      f"source type, not an inference. Its C type is `{ctype}`. If your type for {vid} "
                      f"is a signed integer, replace it; if {vid} is a pointer, ignore this."),
            "reason": f"unsigned-only opcodes on the value ({why}); no signed opcode anywhere"})
    return out


register_domain_oracle("callee_signature", _oracle_callee_signature)
register_domain_oracle("decompiler_pointer", _oracle_decompiler_pointer)
register_domain_oracle("interprocedural_param_usage", _oracle_interprocedural_param_usage)
register_domain_oracle("spilled_param", _oracle_spilled_param)
register_domain_oracle("signedness", _oracle_signedness)
# Listed LAST in any oracle order: it recovers LAYOUT, never a source-level name, so a
# callee-signature `FILE *` or an interprocedural `char *` should claim the entity first.
register_domain_oracle("struct_shape", _oracle_struct_shape)
