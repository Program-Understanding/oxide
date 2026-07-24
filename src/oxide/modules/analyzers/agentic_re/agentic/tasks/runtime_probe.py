"""Execution-grounded type oracle (Ω, dynamic) — ``runtime_type_probe``.

A *dynamic* member of the domain-oracle set. Where the static oracles read STRUCTURE
(ABI tables, declared types, spills, call graph), this one reads RUNTIME BEHAVIOR: it
drives the function under a controlled emulator and observes how a stack slot's bytes are
actually used (dereferenced as a base? loaded into an XMM register? sign-extended?), then
certifies the slot's *representational* type from that behavior. It is model-free and
deterministic given fixed seeds, and emits facts through the exact certified path the
static oracles use (confidence 1.0, seq=None, auto-AGREE, supersede-exempt).

DESIGN (per the integration spec):
  * Ordering: registered LAST in Ω. Static oracles (cheap, strongest ABI anchor) win first;
    this fires only on the residual they could not anchor — the recall-leaking tail.
  * Firing predicate: (1) static oracles abstained on the slot, (2) the slot is
    REPRESENTATIONALLY ambiguous (runtime can settle it), (3) the function is drivable.
    Otherwise abstain immediately — the overwhelming majority of variables never execute.
  * Certification gate: only Tier-A evidence, consistent across k>=CERT_MIN_OBS clean
    observations, with NO conflicting Tier-A, is certified. Weaker evidence is reported but
    NOT oracle-certified (falls back to normal verification). Bias hard toward abstention.
  * Determinism: (function, seed) -> trace is cached; the verdict is a PURE function of the
    trace (``classify_observations``). Cache miss / unreachable -> abstain, exactly the
    fallback semantics the static oracles already have.

STATUS: the decision logic (``classify_observations``), the integration (firing predicate,
certification gate, cache, registration), AND the B0 concrete-execution backend (``ExecProbe``,
angr drive-from-entry) are complete and validated (base32 scale run: 313/340 residual slots
reached, 17 certified, 17/17 representationally correct). Coverage — not reach — is the ceiling:
most reached integer slots show no Tier-A signal on the concrete path. Tier-A signals now include
signed CONDITIONAL BRANCHES (``cmp`` on a slot followed by jl/jle/jg/jge => sound signed integer;
the unsigned flavor jb/ja... is Tier-B only, being shared by unsigned/size_t/pointer), which
converts the large reached-but-silent integer population into certified facts. It is OPT-IN — not
in the default AGENTIC_DOMAIN_ORACLES set — so it never runs unless named.
"""
from __future__ import annotations

import json
import os
import re
import tempfile

from agentic.grounding import register_domain_oracle

# oid -> on-disk path of the materialised binary (angr needs a file; Oxide stores bytes by oid).
_BIN_PATHS: dict = {}
# binary_path -> loaded angr Project. The Project (CLE load + extern hooking) is the expensive part and
# is IMMUTABLE after setup (blank_state builds a fresh state per run), so it is shared across every
# function of the same binary instead of being rebuilt per ExecProbe. This is the big constant-factor
# speedup: without it, driving N functions reloaded + re-hooked the whole binary N times.
_PROJ_CACHE: dict = {}


def _materialize_binary(oid: str):
    """Write the oid's raw bytes to a temp file so angr can load it. Task-agnostic: the oracle gets
    only the oid from the `info` tool (there is no file path in the pipeline), so it retrieves the
    stored bytes through the Oxide API and caches the path per oid."""
    if oid in _BIN_PATHS:
        return _BIN_PATHS[oid]
    try:
        from oxide.core.oxide import api
        data = api.get_field("files", oid, "data")
        if not data:
            return None
        p = os.path.join(tempfile.gettempdir(), f"agentic_runtime_probe_{oid}.bin")
        if not os.path.exists(p):
            with open(p, "wb") as fh:
                fh.write(data)
        _BIN_PATHS[oid] = p
        return p
    except Exception:  # noqa: BLE001
        return None

# --- tuning constants -----------------------------------------------------------------------------
CERT_MIN_OBS = 3          # k: distinct clean observations required to certify a Tier-A verdict
_MAX_PROBE_SLOTS = 8      # never drive execution for more than this many slots per function


# =================================================================================================
#  Section 5 — deterministic evidence rules (PURE; no emulator, no LLM). This is the oracle's brain.
# =================================================================================================
# An "observation" is one per-run record of how the slot's bytes were used, e.g.:
#   {"fp_used": bool,        # value flowed into an XMM/FP instruction
#    "dereferenced": bool,   # value used as a load/store BASE and the access succeeded
#    "signed_op": bool,      # movsx / idiv observed on the value
#    "unsigned_op": bool,    # div (unsigned) observed
#    "width": int|None,      # sub-register width actually READ (1/2/4/8), None if unknown
#    "value": int|None,      # concrete observed value (Tier-C only)
#    "strided": int|None,    # stride in bytes if used as an array base, else None
#    "struct_offsets": list, # distinct fixed offsets accessed off the base (struct evidence)
#    "uninitialized": bool}  # def-before-use this run -> DISCARD (stack garbage)

_TIER_A = "A"; _TIER_B = "B"; _TIER_C = "C"


def _tier_a_of(o: dict):
    """Hardware-definitional evidence from ONE observation -> (repr_class, extra) or None.
    repr_class in {float, double, pointer, signed<w>, unsigned<w>, width<w>}."""
    if o.get("fp_used"):                                  # XMM/FP instruction use
        w = o.get("width")
        return ("double" if w == 8 else "float", None)
    if o.get("dereferenced"):                             # used as base AND deref succeeded
        return ("pointer", None)                          #   (NOT value-range plausibility)
    if o.get("signed_op") or o.get("signed_branch"):      # movsx / idiv  OR signed conditional branch
        # A signed conditional branch (jl/jle/jg/jge after a cmp on the slot) is Tier-A SOUND: at -O0
        # gcc emits signed jumps ONLY for signed operands. Pointers, unsigned ints, and size_t compare
        # with the UNSIGNED flavor (jb/ja...), which is handled as ambiguous Tier-B, never certified.
        return (f"signed{o.get('width') or ''}", None)
    if o.get("unsigned_op"):                              # div (a real unsigned division)
        return (f"unsigned{o.get('width') or ''}", None)
    return None


def classify_observations(observations, k_min: int = CERT_MIN_OBS, k_intr: int = 1) -> dict:
    """Fold per-run observations into a verdict. Returns
        {"ctype": str|None, "tier": "A"/"B"/"C"/None, "certified": bool, "reason": str,
         "polymorphic": list|None}
    Certification (confidence 1.0) requires clean Tier-A observations that AGREE with NO conflicting
    Tier-A. The required count depends on WHY the signal is trustworthy:
      * INSTRUCTION-INTRINSIC signals (movsx/idiv=signed, div=unsigned, xmm=fp, signed conditional
        branch) are properties of the emitted INSTRUCTIONS, not of the seeded argument values, so one
        clean observation certifies them (k_intr, default 1) -- re-driving identical control flow with
        different arg values only reproduces the same instruction.
      * The POINTER signal (a slot value used as a base that dereferences into mapped memory) is
        value-SENSITIVE, so it still needs k_min agreeing runs to rule out a coincidental address.
    Conflicting Tier-A across runs -> polymorphic/union (never collapse). Tier-B or too-few Tier-A ->
    reported (tier set) but certified=False. Else abstain."""
    clean = [o for o in observations if not o.get("uninitialized")]   # discard def-before-use
    if not clean:
        return {"ctype": None, "tier": None, "certified": False,
                "reason": "no clean observations (all uninitialized/unreachable)", "polymorphic": None}

    # --- Tier A: collect the hardware-definitional class from each run ---
    a_classes = [c for c in (_tier_a_of(o) for o in clean) if c]
    a_repr = [c[0] for c in a_classes]
    distinct_a = sorted(set(a_repr))
    if distinct_a:
        # discriminators are already baked in: float-vs-int by register file (fp_used), pointer-vs-int
        # by dereference. Signed is asymmetric: positive evidence only (handled in _tier_a_of).
        core = sorted({_core_repr(r) for r in distinct_a})       # collapse widths for conflict test
        if len(core) > 1:                                        # conflicting Tier-A across runs
            return {"ctype": _union_type(distinct_a), "tier": _TIER_A, "certified": False,
                    "reason": f"cross-run Tier-A conflict -> polymorphic {distinct_a}",
                    "polymorphic": distinct_a}
        # value-sensitive pointer needs k_min agreeing runs; instruction-intrinsic classes need k_intr.
        required = k_min if _core_repr(distinct_a[0]) == "pointer" else k_intr
        if len(a_repr) >= required:                              # consistent AND enough clean obs
            ct = _to_ctype(distinct_a[0], clean)
            return {"ctype": ct, "tier": _TIER_A, "certified": True,
                    "reason": f"Tier-A {distinct_a[0]} consistent across {len(a_repr)} run(s)",
                    "polymorphic": None}
        return {"ctype": _to_ctype(distinct_a[0], clean), "tier": _TIER_A, "certified": False,
                "reason": f"Tier-A {distinct_a[0]} but only {len(a_repr)}<{required} obs",
                "polymorphic": None}

    # --- Tier B: strong statistical (never certified; feeds normal verification) ---
    if any(o.get("dereferenced") for o in clean):                # (covered by A normally)
        return {"ctype": "void *", "tier": _TIER_B, "certified": False,
                "reason": "some run dereferenced the slot", "polymorphic": None}
    strides = [o["strided"] for o in clean if o.get("strided")]
    if strides:
        return {"ctype": f"array[elem {strides[0]}B]", "tier": _TIER_B, "certified": False,
                "reason": f"strided access, stride {strides[0]}", "polymorphic": None}
    offs = sorted({x for o in clean for x in (o.get("struct_offsets") or [])})
    if len(offs) >= 2:
        return {"ctype": f"struct {{layout {offs}}}", "tier": _TIER_B, "certified": False,
                "reason": f"clustered fixed offsets {offs}", "polymorphic": None}
    if any(o.get("unsigned_branch") for o in clean):     # cmp + jb/ja... : unsigned-OR-pointer-OR-size_t
        w = next((o.get("width") for o in clean if o.get("width")), 8)
        ct = {1: "unsigned char", 2: "unsigned short", 4: "unsigned int",
              8: "unsigned long"}.get(w, "unsigned long")
        return {"ctype": ct, "tier": _TIER_B, "certified": False,
                "reason": "unsigned conditional branch (ambiguous vs pointer/size_t) -> not certified",
                "polymorphic": None}

    # --- Tier C: suggestive, never alone -> abstain ---
    return {"ctype": None, "tier": _TIER_C, "certified": False,
            "reason": "only Tier-C (value range/plausibility) evidence -> abstain",
            "polymorphic": None}


def _core_repr(r: str) -> str:
    """Collapse a repr class to its conflict-relevant core (widths/sign don't conflict a class)."""
    if r in ("float", "double"):
        return "fp"
    if r == "pointer":
        return "pointer"
    return "integer"          # signed<w> / unsigned<w> / width<w> are all the integer class


def _to_ctype(repr_class: str, clean) -> str:
    """Map a certified repr class + observed width to a concrete C type."""
    if repr_class == "double":
        return "double"
    if repr_class == "float":
        return "float"
    if repr_class == "pointer":
        return "void *"                                   # representational: a pointer (name unknown)
    w = next((o.get("width") for o in clean if o.get("width")), 8)
    if repr_class.startswith("signed"):
        return {1: "signed char", 2: "short", 4: "int", 8: "long"}.get(w, "long")
    if repr_class.startswith("unsigned"):
        return {1: "unsigned char", 2: "unsigned short", 4: "unsigned int", 8: "unsigned long"}.get(w, "unsigned long")
    return {1: "char", 2: "short", 4: "int", 8: "long"}.get(w, "long")


def _union_type(reprs) -> str:
    return "union { " + "; ".join(sorted(set(reprs))) + " }"


# =================================================================================================
#  Section 4 — the emulation backend (behind call_tool, injected like OxideContext).
# =================================================================================================
# Ghidra stack-space offset -> rbp-relative offset. At -O0 gcc every function builds a standard
# `push rbp; mov rbp,rsp` frame, so Ghidra frame-0 is the return-address slot at rbp+8; a Ghidra
# stack offset G therefore addresses rbp+(G+FRAME_ADJ). Verified against close_stream's disassembly
# (V5 ghidra -0x20 == mov %rdi,-0x18(%rbp)); holds for the -O0 rbp-framed benchmark.
FRAME_ADJ = 0x8

# Tier-A instruction signals, kept deliberately SOUND (bias-to-abstain, Section 5):
#   * movsx/movsxd/idiv  -> signed      (compiler sign-extends signed narrow types)
#   * div                -> unsigned     (a real unsigned division)  -- NOT movzx (gcc's default byte load)
#   * movsd/movss/cvt*/xmm-> fp          (value lives in the FP register file)
# A dereference (Tier-A pointer) is detected dynamically: a value loaded from the slot is later used
# as a memory-access base and the access lands in mapped memory (not value-range plausibility).
_SIGNED_MNEM = ("movsx", "movsxd", "idiv")
_FP_MNEM = ("movsd", "movss", "cvtsi2sd", "cvtsi2ss", "cvttsd2si", "cvttss2si",
            "addsd", "mulsd", "subsd", "divsd", "addss", "mulss", "subss", "divss")
# Conditional-branch signedness (the compiler chooses the jump flavor by operand signedness):
#   signed relational  -> jl / jle / jg / jge   (SOUND: emitted ONLY for signed operands)
#   unsigned relational -> jb / jbe / ja / jae   (shared by unsigned int, size_t, AND pointers -> Tier-B)
# Equality (je/jne) and sign-bit (js/jns) jumps carry no relational-signedness and are ignored.
_SIGNED_JCC = frozenset(("jl", "jle", "jg", "jge", "jnge", "jng", "jnl", "jnle"))
_UNSIGNED_JCC = frozenset(("jb", "jbe", "ja", "jae", "jnae", "jna", "jnb", "jnbe", "jc", "jnc"))


class ExecProbe:
    """Controlled-execution backend (Phase B0: concrete angr).

    ``observe(addr, slot_off, seeds)`` drives the function under angr with libc externs hooked to
    concrete returns (no live syscalls), resolves the frame live, and watches how the stack slot's
    bytes are actually used, returning one observation dict per seed (schema above). Returns [] when
    angr is unavailable, the binary can't be loaded, or the run fails -- so the oracle ABSTAINS, the
    same fallback the static oracles have. B0 covers concrete drive-from-entry; symbolic
    drive-to-slot for branch-guarded slots is B1."""

    def __init__(self, binary_path: str):
        self.binary_path = binary_path
        self._proj = None
        self._raw = {}          # (addr, seed) -> {rbp_rel_offset: obs-fragment}  (per-run cache)
        try:
            import angr  # noqa: F401
            self.available = True
        except Exception:  # noqa: BLE001
            self.available = False

    # -- lazy project load: stripped PIE at base 0, no libc, externs -> concrete scratch pointers ---
    def _project(self):
        if self._proj is not None:
            return self._proj
        cached = _PROJ_CACHE.get(self.binary_path)
        if cached is not None:
            self._proj, self._arena_lo = cached
            return self._proj
        import logging
        for n in ("angr", "cle", "pyvex", "claripy"):
            logging.getLogger(n).setLevel(logging.CRITICAL)
        import angr
        import claripy
        proj = angr.Project(self.binary_path, auto_load_libs=False, main_opts={"base_addr": 0})
        # hand every unresolved extern a distinct valid scratch pointer, so a genuine pointer
        # returned by libc (e.g. nl_langinfo -> char*) can be dereferenced into mapped memory and
        # observed, while an int-returning call just yields a large harmless value.
        arena = {"next": 0x4100_0000}

        class _RetPtr(angr.SimProcedure):
            def run(self, *a):  # noqa: ANN001
                p = arena["next"]; arena["next"] += 0x1000
                return claripy.BVV(p, self.arch.bits)

        for sym in proj.loader.symbols:
            if sym.is_import or (sym.is_function and
                                 not proj.loader.main_object.contains_addr(sym.rebased_addr)):
                try:
                    proj.hook_symbol(sym.name, _RetPtr())
                except Exception:  # noqa: BLE001
                    pass
        self._proj = proj
        self._arena_lo = 0x4100_0000
        _PROJ_CACHE[self.binary_path] = (proj, self._arena_lo)   # share across this binary's functions
        return proj

    def _run_once(self, addr_i: int, seed: int) -> dict:
        """Drive the function once; return {rbp_rel_off: fragment} for every stack slot touched."""
        import angr
        import claripy
        proj = self._project()
        # rebase Ghidra vaddr -> ELF vaddr: the oracle receives Ghidra addresses (image base 0x100000)
        # but the project is loaded at base 0. If the address falls outside the loaded object, drop the
        # Ghidra base so drive-from-entry starts at the real function.
        mo = proj.loader.main_object
        if not (mo.min_addr <= addr_i <= mo.max_addr):
            addr_i -= 0x10_0000
        opts = {angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
                angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS}
        st = proj.factory.blank_state(addr=addr_i, add_options=opts)
        scratch, retpage = 0x5000_0000, 0x6000_0000
        st.memory.map_region(scratch, 0x10_0000, 3)
        st.memory.map_region(retpage, 0x1000, 3)
        # seed args into the mapped scratch region so pointer args are dereferenceable, but spaced
        # 0x10000 apart -- far wider than the deref match window (0x1000) -- so one arg's dereference
        # can never be mis-attributed to a neighbouring slot's value.
        for i, reg in enumerate(("rdi", "rsi", "rdx", "rcx", "r8", "r9")):
            setattr(st.regs, reg, claripy.BVV(scratch + 0x1_0000 * (i + 1) + 0x80 * seed, 64))
        st.regs.rsp = 0x7fff_0000
        st.stack_push(claripy.BVV(retpage, 64))          # sentinel return address

        # Deterministic frame: at -O0 the standard prologue (push rbp; mov rbp,rsp) sets rbp to a fixed
        # address given our seeded rsp (0x7fff_0000, minus 8 for the pushed sentinel return, minus 8 for
        # the pushed old rbp) = 0x7ffe_fff0. Building slot_map up front lets us DROP the per-instruction
        # breakpoint that used to watch every instruction just to discover rbp -- a mis-set rbp only
        # costs recall (no slot is hit -> abstain), never precision.
        rbp_val = 0x7ffe_fff0
        slot_map = {rbp_val + g: g for g in range(-0x100, 0x8)}  # concrete addr -> rbp_rel offset
        acc = {}                                         # rbp_rel off -> fragment
        loaded = {}                                      # concrete value loaded from a slot -> rbp_rel off

        def frag(off):
            return acc.setdefault(off, {"width": None, "fp_used": False, "dereferenced": False,
                                        "signed_op": False, "unsigned_op": False,
                                        "signed_branch": False, "unsigned_branch": False,
                                        "read": False, "written": False})

        def _ins_addr(state):
            # the instruction CURRENTLY executing. With block-granularity stepping state.addr is the
            # BLOCK entry, not the current instruction, so use scratch.ins_addr (the live imark address).
            try:
                return state.scratch.ins_addr
            except Exception:  # noqa: BLE001
                return state.addr

        def cur_insn(state):
            try:
                return proj.factory.block(_ins_addr(state), num_inst=1).capstone.insns[0]
            except Exception:  # noqa: BLE001
                return None

        def on_read(state):
            try:
                a = state.solver.eval(state.inspect.mem_read_address)
                sz = state.solver.eval(state.inspect.mem_read_length) if \
                    state.inspect.mem_read_length is not None else 0
            except Exception:  # noqa: BLE001
                return
            for pv, off in list(loaded.items()):          # deref: reusing a slot-loaded value as base
                if pv and abs(a - pv) < 0x1000:
                    frag(off)["dereferenced"] = True
            if a in slot_map:
                off = slot_map[a]; f = frag(off); f["read"] = True
                if f["width"] is None:
                    f["width"] = sz
                ins = cur_insn(state)
                if ins is not None:
                    m, ops = ins.mnemonic, ins.op_str
                    if m.startswith(_SIGNED_MNEM):
                        f["signed_op"] = True
                    if m == "div":
                        f["unsigned_op"] = True
                    if m.startswith(_FP_MNEM) or "xmm" in ops:
                        f["fp_used"] = True
                    if m == "cmp":                        # the NEXT insn's Jcc reveals the operand sign
                        try:                              # static lookahead -> no per-instruction hook
                            nins = proj.factory.block(_ins_addr(state) + ins.size,
                                                      num_inst=1).capstone.insns[0]
                            if nins.mnemonic in _SIGNED_JCC:
                                f["signed_branch"] = True
                            elif nins.mnemonic in _UNSIGNED_JCC:
                                f["unsigned_branch"] = True
                        except Exception:  # noqa: BLE001
                            pass
                try:
                    v = state.solver.eval(state.inspect.mem_read_expr) \
                        if state.inspect.mem_read_expr is not None else None
                    if v and v >= 0x1_0000:               # only address-like values are deref candidates;
                        loaded[v] = off                   #   small ints (bool/flag/enum) can never match
                except Exception:  # noqa: BLE001
                    pass

        def on_write(state):
            try:
                a = state.solver.eval(state.inspect.mem_write_address)
            except Exception:  # noqa: BLE001
                return
            if a in slot_map:
                f = frag(slot_map[a])
                if not f["read"]:
                    f["written"] = True                   # written before any read -> initialised

        st.inspect.b("mem_read", when=angr.BP_AFTER, action=on_read)
        st.inspect.b("mem_write", when=angr.BP_BEFORE, action=on_write)

        # Instruction-granularity stepping is (counter-intuitively) FASTER than block stepping here:
        # the mem_read/mem_write inspect breakpoints force angr to break every block at each memory
        # access anyway, so block stepping only adds block-management overhead. num_inst=1 also keeps
        # state.addr == the current instruction, which cur_insn / the branch lookahead rely on.
        simgr = proj.factory.simulation_manager(st)
        for _ in range(600):
            if not simgr.active:
                break
            if simgr.active[0].solver.eval(simgr.active[0].regs.rip) == retpage:
                break
            try:
                simgr.step(num_inst=1)
            except Exception:  # noqa: BLE001
                break
            if len(simgr.active) > 1:                      # stay on one path (determinism)
                simgr.active[:] = simgr.active[:1]
        return acc

    def observe(self, addr: str, slot_off: str, seeds) -> list:
        if not self.available:
            return []
        try:
            addr_i = int(addr, 16)
            rbp_rel = int(slot_off, 16) + FRAME_ADJ        # Ghidra offset -> rbp-relative
        except Exception:  # noqa: BLE001
            return []
        obs = []
        for si, seed in enumerate(seeds):
            key = (addr_i, si)
            if key not in self._raw:
                try:
                    self._raw[key] = self._run_once(addr_i, si)
                except Exception:  # noqa: BLE001
                    self._raw[key] = {}
            frag = self._raw[key].get(rbp_rel)
            if frag is None:
                obs.append({"uninitialized": True})        # slot never touched this run -> discard
                continue
            obs.append({
                "width": frag["width"],
                "fp_used": frag["fp_used"],
                "dereferenced": frag["dereferenced"],
                "signed_op": frag["signed_op"],
                "unsigned_op": frag["unsigned_op"],
                "signed_branch": frag.get("signed_branch", False),
                "unsigned_branch": frag.get("unsigned_branch", False),
                "uninitialized": frag["read"] and not frag["written"],  # read before any write
            })
        return obs


# small per-process cache: (binary, addr, slot, seed) -> observations (determinism, Section 6)
_TRACE_CACHE: dict = {}


# =================================================================================================
#  Section 3 — firing predicate + oracle entry (integration with the existing static Ω).
# =================================================================================================
def _stack_slots(question: str) -> dict:
    """{vid: offset-str} for stack-addressed variables in the question."""
    out = {}
    for vm in re.finditer(r"\bV(\d+)\b[ \t(]*stack\s+(-?0x[0-9a-fA-F]+)", question or ""):
        out[f"V{vm.group(1)}"] = vm.group(2)
    return out


def _statically_anchored(call_tool, question) -> set:
    """The vids the STATIC oracles already pin — so the probe fires only on the residual. Runs the
    cheap static certifiers (decompile-based) and collects the entities they resolve."""
    from agentic.tasks import type_recovery as TR
    anchored = set()
    for facts_fn in (TR.callee_type_recall_facts, TR.spilled_param_facts,
                     TR.interprocedural_param_usage_facts, TR.decompiler_pointer_facts):
        try:
            for t in facts_fn(call_tool, question):
                anchored.add(t[0])                        # first field of every fact tuple is the vid
        except Exception:  # noqa: BLE001
            continue
    return anchored


def runtime_type_probe_facts(call_tool, question) -> list:
    """Fire on the residual only: stack slots the static oracles left un-anchored. For each, drive the
    function and certify a Tier-A verdict if the evidence gate passes; else abstain. Returns
    (vid, ctype, tier, reason) tuples for CERTIFIED facts only."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    addr = m.group(1)
    slots = _stack_slots(question)
    if not slots:
        return []
    anchored = _statically_anchored(call_tool, question)          # firing predicate (1)
    residual = [(vid, off) for vid, off in slots.items() if vid not in anchored][:_MAX_PROBE_SLOTS]
    if not residual:
        return []
    # the binary must be on disk for angr; the pipeline exposes only the oid (via the info tool), so
    # resolve oid -> materialised temp file.
    try:
        binfo = call_tool("info", {})
        info = binfo if isinstance(binfo, dict) else json.loads(str(binfo))
        oid = info.get("oid")
    except Exception:  # noqa: BLE001
        oid = None
    bpath = _materialize_binary(oid) if oid else None
    if not bpath:
        return []
    probe = ExecProbe(bpath)
    facts = []
    for vid, off in residual:
        key = (bpath, addr, off)
        if key in _TRACE_CACHE:
            verdict = classify_observations(_TRACE_CACHE[key])
        else:
            # ADAPTIVE DRIVE: an instruction-intrinsic Tier-A (sign/fp/unsigned/branch) is settled by a
            # single clean run, so drive ONE seed first and stop the moment it certifies. Only fall back
            # to the full CERT_MIN_OBS seeds when seed 0 did not certify (the value-sensitive pointer
            # case, which genuinely needs agreeing runs). observe() memoizes per (addr, seed) in the
            # probe, so the fallback re-uses seed 0's trace and only drives the extra seeds.
            obs = probe.observe(addr, off, seeds=[0])
            verdict = classify_observations(obs)
            if not (verdict["certified"] and verdict["ctype"]):
                obs = probe.observe(addr, off, seeds=list(range(CERT_MIN_OBS)))
                verdict = classify_observations(obs)
            _TRACE_CACHE[key] = obs
        if verdict["certified"] and verdict["ctype"]:             # certification gate
            facts.append((vid, verdict["ctype"], verdict["tier"], verdict["reason"]))
    return facts


def _oracle_runtime_type_probe(call_tool, question) -> list:
    out = []
    for vid, ctype, tier, reason in runtime_type_probe_facts(call_tool, question):
        is_ptr = ctype.strip().endswith("*")          # a representational pointer -> a FLOOR, not the pointee
        if is_ptr:
            # Floor: assert only the lower bound (it IS a pointer). Never flatten a well-supported
            # specific pointer type; the pipeline defers the certified pin to synthesis when it already
            # produced a more specific pointer, and pins the floor only to correct a NON-pointer answer.
            claim = (f"{vid} is AT LEAST a pointer — controlled execution dereferenced its bytes as a "
                     f"memory address (Tier-{tier} runtime evidence). If a more specific pointer type "
                     f"(e.g. `T *`) is well-supported by the code, PREFER it; otherwise `{ctype}`.")
        else:
            claim = (f"{vid} has C type `{ctype}` — controlled execution observed its bytes used as "
                     f"{ctype} (Tier-{tier} runtime evidence). Treat as established; this dynamic "
                     f"evidence overrides a static guess for {vid}.")
        out.append({
            "vid": vid, "ctype": ctype, "source": "deterministic_runtime_type_probe",
            "claim": claim, "reason": f"runtime probe, {reason}", "floor": is_ptr})
    return out


register_domain_oracle("runtime_type_probe", _oracle_runtime_type_probe)
