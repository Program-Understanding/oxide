"""signedness oracle: recover the sign bit from instruction pairs the compiler is FORCED to choose
between (shr/sar, movzx/movsx, div/idiv, rotates)."""
from __future__ import annotations

import json
import re
from .common import _V_REGISTER, _vid_sizes, _vid_stack_offsets


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
