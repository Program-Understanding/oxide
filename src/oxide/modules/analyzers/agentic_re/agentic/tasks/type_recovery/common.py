"""Shared machinery for the type-recovery oracles: the C-library ABI table, the question
parsers that turn a variable line into a storage location, and the pointer-class predicates.

A name lives here iff more than one oracle reaches it; everything else lives with its oracle.
"""
from __future__ import annotations

import json
import os
import re


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

# LIBC PROTOTYPE KNOWLEDGE IS OFF BY DEFAULT (changed 2026-07-31; opt back in with AGENTIC_LIBC=1).
#
# TRex deliberately does not use libc signatures (their S5.2: they beat Ghidra "despite not
# implementing interprocedural type propagation, which Ghidra uses ... along with external functions
# it knows, such as those in libc"), so a reviewer would reasonably ask how much of our margin is
# just that orthogonal, well-understood advantage. We measured it rather than argued it.
#
# MEASURED, paired, same function run both ways (n=376 of a planned 5000, sweep stopped early):
#   paired delta -0.001 .. +0.018 points, 95% CI [-0.48, +0.51] -- indistinguishable from zero
#   margin over TRex retained: 100.1%
#   21 functions worse, 21 better, 334 unchanged
# So the table costs 63 of 342 oracle facts (18.4%) yet buys no aggregate accuracy: the types it
# certifies are evidently recoverable through the decompiler-pointer / spilled-param oracles and the
# model itself. Turning it OFF removes the strongest external-knowledge objection at no measured cost.
#
# CAVEATS, because the null is easy to overread:
#   * n=376 bounds the effect to about +-0.5 points, not to zero. A sub-0.5-point cost is not excluded.
#   * Aggregate-zero hides real per-function churn (cp/copy_attr -43.6, sort/heap_free -22.2, offset
#     by cksum/md5_stream +38.1). libc knowledge is REDISTRIBUTIVE here, not inert.
#
# Emptying the table disables it at the ONE place all three consumers read:
#   * callee_signature      -- entirely libc-driven, so it now ALWAYS abstains (see roster note below)
#   * interprocedural       -- Tier 1 (chain terminates at a libc position) never fires; the
#                              declared-type Tier 2 fallback is unaffected
#   * spilled_param         -- loses its libc fallback, keeps the decompiler's declared pointer
# The tool ROSTER is deliberately still unchanged, so this remains the exact configuration that was
# measured. `callee_signature` therefore stays on the verifier's menu while always returning nothing;
# dropping it is a separate, unmeasured change (tool-count changes are known to move this model).
if os.environ.get("AGENTIC_LIBC", "").strip().lower() not in ("1", "true", "yes"):
    _LIBC_SIG = {}


# Ghidra x86-64 register-space offsets -> SysV integer argument position (1-based): rdi,rsi,rdx,rcx,r8,r9.
_REGOFF_TO_ARG = {0x38: 1, 0x30: 2, 0x10: 3, 0x08: 4, 0x80: 5, 0x88: 6}


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


# x86-64 SysV: the register a spilled argument was moved from -> its 1-based parameter index.
_REGNAME_TO_ARG = {"rdi": 1, "edi": 1, "rsi": 2, "esi": 2, "rdx": 3, "edx": 3,
                   "rcx": 4, "ecx": 4, "r8": 5, "r8d": 5, "r9": 6, "r9d": 6}


_SPILL_STORE = re.compile(r"mov\s+(?:[a-z]+\s+ptr\s+)?\[[^\]]+\]\s*,\s*([a-z][a-z0-9]+)")


# Argument list allowing ONE level of nested parens, so a forwarded call with casts
# (`FUN_x(param_1, (int)param_2, param_3)`) is captured whole instead of truncating at the first `(`.
_CALL_ARGS = r"\(((?:[^()]|\([^()]*\))*)\)"


_LIBC_CALL = re.compile(r"\b([A-Za-z_]\w*)\s*" + _CALL_ARGS)


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


def _vid_sizes(question: str) -> dict:
    """{'V1': 8, 'V2': 4} from the VARIABLES block. The slot width is GIVEN, so it overrides a
    declared integer width read out of a callee: the callee's parameter may be a truncated view of
    the value (`int param_3` for an 8-byte slot), and the claim we are making is only "not a
    pointer" -- the width should come from the fact we are certain about."""
    return {m.group(1): int(m.group(2))
            for m in re.finditer(r"^(V\d+)\t[^\t]+\t(\d+)\s*$", question or "", re.M)}


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


# --- normalized Ω oracles (return {"vid","ctype","source","claim","reason"}) + registration --------
# --- struct-shape oracle --------------------------------------------------------------------------
# Production decompilers render an aggregate pointer as a pointer to a PRIMITIVE because they never
# assemble the observed field accesses into a struct: on the classic singly-linked-list example,
# Ghidra emits `undefined4 *`, Binary Ninja `int32_t *`, Hex-Rays `unsigned int *`. The evidence for
# the aggregate is nonetheless present and deterministic -- a load at `[p + N]` of a given width is a
# field, and a field whose value flows back into p is a self-reference. `struct_shape` reports those
# observations; this renders them as a C type. No model involvement, and no ground truth.
_W2T = {1: "char", 2: "short", 4: "int", 8: "long"}
# --- the oracles as INDIVIDUAL tools --------------------------------------------------------------
# `static_type_oracles` runs all of them and is the right call when nothing is known. Exposing each
# one separately is what makes selection meaningful: the oracles differ in the EVIDENCE they read, so
# a reviewer looking at a function full of libc calls wants a different one than a reviewer looking at
# a stack slot that mirrors a parameter. Each description therefore leads with the evidence it needs,
# which is the only thing the model has to choose on.
_ORACLE_PARAMS = {"addr": {"type": "string"}, "variables": {"type": "string"}}


# ... and -> the decompiler's SysV parameter identifier.
_REGOFF_TO_PARAM = {0x38: "param_1", 0x30: "param_2", 0x10: "param_3", 0x08: "param_4",
                    0x80: "param_5", 0x88: "param_6"}


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
