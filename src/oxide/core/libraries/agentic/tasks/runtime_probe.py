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

STATUS: the decision logic (``classify_observations``) and the integration (firing predicate,
certification gate, cache, registration) are complete and tested. The emulation BACKEND
(``ExecProbe.observe``) is a conservative stub that reports ``unreachable`` until the
drive-to-slot + argument-bootstrap + observation loop is built (Phase B); the oracle therefore
ABSTAINS everywhere for now, disturbing no measured component. It is OPT-IN — not in the
default AGENTIC_DOMAIN_ORACLES set — so it never runs in the current benchmark unless named.
"""
from __future__ import annotations

import re

from oxide.core.libraries.agentic.grounding import register_domain_oracle

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
    if o.get("signed_op"):                                # movsx / idiv
        return (f"signed{o.get('width') or ''}", None)
    if o.get("unsigned_op"):                              # div
        return (f"unsigned{o.get('width') or ''}", None)
    return None


def classify_observations(observations, k_min: int = CERT_MIN_OBS) -> dict:
    """Fold per-run observations into a verdict. Returns
        {"ctype": str|None, "tier": "A"/"B"/"C"/None, "certified": bool, "reason": str,
         "polymorphic": list|None}
    Certification (confidence 1.0) requires: >= k_min clean Tier-A observations that AGREE, with
    NO conflicting Tier-A. Conflicting Tier-A across runs -> polymorphic/union (never collapse).
    Tier-B or single/weak Tier-A -> reported (tier set) but certified=False. Else abstain."""
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
        if len(a_repr) >= k_min:                                 # consistent AND enough clean obs
            ct = _to_ctype(distinct_a[0], clean)
            return {"ctype": ct, "tier": _TIER_A, "certified": True,
                    "reason": f"Tier-A {distinct_a[0]} consistent across {len(a_repr)} runs",
                    "polymorphic": None}
        return {"ctype": _to_ctype(distinct_a[0], clean), "tier": _TIER_A, "certified": False,
                "reason": f"Tier-A {distinct_a[0]} but only {len(a_repr)}<{k_min} obs",
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
class ExecProbe:
    """Controlled-execution backend. ``observe(addr, slot_off, seeds)`` returns a list of per-run
    observation dicts (schema above), or [] when the function is not drivable / the slot unreachable.

    Phase B (TODO, requires a validated emulator): Unicorn/Qiling for an isolated memory map with no
    live syscalls, OR angr's engine for drive-to-slot when the slot is behind a branch; argument
    bootstrap seeded from the static predictor and refined on execution feedback; observe frame_base+
    offset accesses across synthesized inputs; discard def-before-use reads. Until then this returns
    [] (unreachable) so the oracle ABSTAINS everywhere and disturbs nothing."""

    def __init__(self, binary_path: str):
        self.binary_path = binary_path
        try:
            import angr  # noqa: F401
            self.available = True
        except Exception:  # noqa: BLE001
            self.available = False

    def observe(self, addr: str, slot_off: str, seeds) -> list:
        # Phase-B backend not yet built -> conservatively report "unreachable" (empty observations).
        # This makes classify_observations abstain, preserving all measured behavior.
        return []


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
    from oxide.core.libraries.agentic.tasks import type_recovery as TR
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
    # the binary path is needed to drive execution; call_tool exposes it via open_binary/info.
    try:
        binfo = call_tool("info", {})
        bpath = re.search(r"(/[^\s\"]+\.(?:ndbg-bin|bin|elf)|/[^\s\"]+)", str(binfo))
        bpath = bpath.group(1) if bpath else None
    except Exception:  # noqa: BLE001
        bpath = None
    if not bpath:
        return []
    probe = ExecProbe(bpath)
    facts = []
    for vid, off in residual:
        key = (bpath, addr, off, "seed0")
        if key in _TRACE_CACHE:
            obs = _TRACE_CACHE[key]
        else:
            obs = probe.observe(addr, off, seeds=["seed0"])       # firing predicate (3): drivable?
            _TRACE_CACHE[key] = obs
        verdict = classify_observations(obs)                      # Section 5 rules (pure)
        if verdict["certified"] and verdict["ctype"]:             # certification gate
            facts.append((vid, verdict["ctype"], verdict["tier"], verdict["reason"]))
    return facts


def _oracle_runtime_type_probe(call_tool, question) -> list:
    out = []
    for vid, ctype, tier, reason in runtime_type_probe_facts(call_tool, question):
        out.append({
            "vid": vid, "ctype": ctype, "source": "deterministic_runtime_type_probe",
            "claim": (f"{vid} has C type `{ctype}` — controlled execution observed its bytes used as "
                      f"{ctype} (Tier-{tier} runtime evidence). Treat as established; this dynamic "
                      f"evidence overrides a static guess for {vid}."),
            "reason": f"runtime probe, {reason}"})
    return out


register_domain_oracle("runtime_type_probe", _oracle_runtime_type_probe)
