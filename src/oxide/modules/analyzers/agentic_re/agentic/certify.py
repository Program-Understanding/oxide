"""Deterministic post-pass: oracle collection, the certification trailer, and the two repairs that
run unconditionally.

Split out of `deepagent` (2026-07-30). Note the trailer itself is OFF by default -- the reviewer
applies oracle facts as tools it calls -- but `_rescue_undefined` and `_coerce_sizes` always run, so
this module is on the live path either way. See `_no_certify`.
"""
from __future__ import annotations

import json
import os
import re

from agentic.claims import _claims_from_messages


# --- ORACLES-IN-THE-LOOP experiment (opt-in, AGENTIC_VERIFIER_ORACLES=1) --------------------------
# The architecture's central claim is that certification must be applied BY CODE, after the agents,
# and never shown to them -- because a fact a model has seen becomes indistinguishable from a fact the
# model produced. This flag tests that claim head-on by inverting it: the reviewer is given the oracle
# tool and asked to apply the certified facts ITSELF, and the deterministic trailer is switched off so
# the oracles fire exactly once. The comparison is therefore "same facts, applied by a 12B model" vs
# "same facts, applied by code".
#
# NOT the same as the earlier A/B recorded above: that one left the trailer ON, so the oracles were
# applied twice and the model could only corrupt what code then re-fixed (version_etc_ar 86.46->70.83).
# Here the model is the only consumer, which is the configuration the design argument is about.
# The facts are INJECTED, not fetched. Offering the oracle as a TOOL was tried first and the reviewer
# never called it -- verified not to be a wiring bug (registry, MCP publication, allowlist and a live
# MCP invocation all check out; the roster printed the tool and a direct call returned certifications).
# It is the fifth instance of this model declining a tool it was explicitly instructed to use, matching
# the tool-selection audit's finding that `xrefs_to`/`read_values`/`compute` were chosen 0 times in
# 1049 calls. Appending the tool instructions also REDUCED its tool use (decompile x1 + value_usage x3
# -> decompile x1 only). Injection removes tool selection from the experiment so that the only variable
# left is the one under test: can the model APPLY certified facts as well as code applies them?
_ORACLE_SUFFIX = """

CERTIFIED FACTS for this function — deterministic, re-derived from the binary and public ABI \
knowledge. These are NOT guesses and they outrank your own reading of the decompilation:
{facts}

How to apply each kind:
  - EXACT — replace your type for that id, unconditionally.
  - FLOOR — asserts only "this id holds a pointer", pointee unknown. Use it when your type is NOT a \
pointer; KEEP your own more specific pointer when it already is one (never overwrite `char *` with \
`void *`).
  - SHAPE — a field layout with no source-level name. Use it unless you already have a NAMED pointee.
Ignore any fact whose type is wider than that id's declared byte size. For every id not listed above, \
use your own decompilation-based judgement."""


# Tool-mode hint (used with AGENTIC_VERIFIER_FORCE_TURNS): the reviewer picks the tool itself.
_ORACLE_TOOL_BLURB = {
    # Peer descriptions: each names the EVIDENCE it reads, none claims to subsume the others.
    # The combined oracle previously advertised itself as "runs all of the above at once", which made
    # the other four unselectable in practice -- the model called it and stopped every time.
    "callee_signature": "a parameter handed to a libc function whose ABI fixes that argument's type "
                        "— use when the function calls libc",
    "decompiler_pointer": "the decompiler's own recovered pointer declarations — use when you suspect "
                          "a pointer but the assembly does not settle it",
    "spilled_param": "the prologue store that copies an argument register into a stack slot — use when "
                     "stack locals mirror the parameters",
    "interprocedural_param_usage": "a parameter forwarded into another local function until it reaches "
                                   "a fixed-type library position — use when a parameter is passed on",
    "static_type_oracles": "all four at once — use when several kinds of evidence are present, or you "
                           "have no specific hypothesis about where a type would come from",
}


# --- size-consistency coercion (deterministic, no model) -----------------------------------------
# The question states each entity's byte SIZE as a given. A reported type whose width contradicts that
# size is a PROVABLE error -- an 8-byte slot cannot hold `int`, a 4-byte slot cannot hold a pointer --
# detectable without ground truth. Measured 2026-07-26 over 30 functions: 17 such variables across
# 11 functions; rewriting each to the same-family type of the DECLARED width scored 3 better / 0 worse
# / 4 tied, mean +5.52 on affected functions (+1.29 amortized). Unlike a prompt change this is a pure
# post-hoc transform of a fixed answer, so the +-11.8 run-to-run noise floor does not apply to it.
_TYPE_WIDTH = {
    "char": 1, "uchar": 1, "byte": 1, "bool": 1, "_bool": 1, "schar": 1, "signed char": 1,
    "unsigned char": 1, "int8_t": 1, "uint8_t": 1, "undefined1": 1,
    "short": 2, "ushort": 2, "unsigned short": 2, "word": 2, "int16_t": 2, "uint16_t": 2,
    "undefined2": 2,
    "int": 4, "uint": 4, "unsigned int": 4, "float": 4, "dword": 4, "int32_t": 4, "uint32_t": 4,
    "undefined4": 4, "wchar_t": 4,
    "long": 8, "ulong": 8, "unsigned long": 8, "size_t": 8, "ssize_t": 8, "double": 8, "qword": 8,
    "longlong": 8, "ulonglong": 8, "uintmax_t": 8, "intmax_t": 8, "off_t": 8, "idx_t": 8,
    "ptrdiff_t": 8, "int64_t": 8, "uint64_t": 8, "undefined8": 8,
}


_UNDEF_RE = re.compile(r"^\s*undefined\d*\s*\**\s*$", re.I)


_UNSIGNED = {"uchar", "byte", "unsigned char", "ushort", "unsigned short", "word", "uint",
             "unsigned int", "dword", "ulong", "unsigned long", "size_t", "qword", "ulonglong",
             "uintmax_t", "uint8_t", "uint16_t", "uint32_t", "uint64_t"}


_WIDTH_TYPE = {8: ("long", "ulong"), 4: ("int", "uint"), 2: ("short", "ushort"), 1: ("char", "uchar")}


def _oracle_tool_hint(oid: str, vaddr: str, roster) -> str:
    """Describe ONLY the oracle tools this reviewer actually has.

    Built from the roster rather than hard-coded because naming a tool in the prompt is itself a way
    of calling it: the model will copy a call out of the instructions even when that tool was filtered
    out of the request, and langgraph's executor runs it anyway. A hard-coded list therefore silently
    defeats any roster-level experiment -- what looked like the reviewer SELECTING the combined oracle
    was it reciting the one example the prompt spelled out."""
    have = [t for t in ("callee_signature", "decompiler_pointer", "spilled_param",
                        "interprocedural_param_usage", "static_type_oracles") if t in roster]
    if not have:
        return ""
    lines = "\n".join(f"  {i}. `{t}(oid=\"{oid}\", addr=\"{vaddr}\", variables=...)` — "
                      f"{_ORACLE_TOOL_BLURB[t]}." for i, t in enumerate(have, 1))
    return f"""

You also have DETERMINISTIC ORACLES. They read the binary directly and return CERTIFIED facts — \
derived, not guessed — as [{{{{vid, ctype, floor, oracle}}}}]. Each takes \
`(oid="{oid}", addr="{vaddr}", variables=<the variable list you were given, verbatim>)`:
{lines}
Consult the ones whose EVIDENCE matches what you can see in this function — several may apply, and \
each certifies entities the others miss, so calling more than one is normal. They are deterministic \
and cheap; the only cost of consulting one that does not apply is that it abstains.

Apply what they return as authoritative: a fact with `floor: false` replaces your type for that id; a \
fact with `floor: true` asserts only "this is a pointer", so use it when your type is NOT a pointer \
but keep your own more specific pointer when it already is one; ignore any fact wider than the id's \
declared byte size."""


def _oracle_brief(oid: str, question: str, opts: dict) -> str:
    """The certified facts, rendered for injection into the reviewer's prompt."""
    try:
        facts = _collect_oracle_facts(oid, question, opts)
    except Exception as e:  # noqa: BLE001
        print(f"[verifier-oracles] skipped — {str(e)[:120]}")
        return ""
    if not facts:
        return ""
    kind = {"exact": "EXACT", "floor": "FLOOR", "shape": "SHAPE"}
    lines = [f"  {vid}: {ctype}   [{kind.get(mode, mode)} — {oracle}]"
             for vid, (ctype, oracle, mode) in sorted(facts.items(), key=lambda kv: kv[0])]
    print(f"[verifier-oracles] injected {len(lines)} certified facts into the reviewer prompt")
    return _ORACLE_SUFFIX.format(facts="\n".join(lines))


def _verifier_oracles() -> bool:
    """Is the reviewer given the oracles as TOOLS? Default ON -- this is the shipped architecture.

    The reviewer selects the oracle whose evidence fits the function it is looking at, reads the facts,
    and adjudicates them against the decompilation itself. Set AGENTIC_VERIFIER_ORACLES=0 to withhold
    them, which is the ablation that isolates what the oracles contribute."""
    return str(os.environ.get("AGENTIC_VERIFIER_ORACLES", "1")).strip().lower() \
        not in ("0", "false", "no", "off")


def _no_certify() -> bool:
    """Is the code-applied certification trailer suppressed? Default ON (i.e. no trailer).

    In the shipped architecture the oracles are applied by the REVIEWER, which reads their claims as
    tool results and decides. `_certified_trailer` -- with its first-claim-wins precedence and the five
    claim modes -- is therefore not on the default path; it is retained, and reachable with
    AGENTIC_NO_CERTIFY=0, as the alternative-architecture ablation. Note what still runs
    unconditionally either way: `_rescue_undefined` and `_coerce_sizes`, plus each oracle's own
    physical-realizability guard, so the deterministic layer is reduced but not removed."""
    return str(os.environ.get("AGENTIC_NO_CERTIFY", "1")).strip().lower() \
        not in ("0", "false", "no", "off")


def _collect_oracle_facts(oid: str, question: str, opts: dict) -> dict:
    """Run the static type oracles IN-PROCESS and return {vid: (ctype, oracle, floor)} (first oracle
    wins per vid). Reliable because it uses the full question (with the vaddr) — unlike an LLM tool
    call, which was observed to drop the vaddr and get empty results.

    WHEN THIS RUNS: only AFTER the agents finish, from `_certified_trailer` (plus `_emit_flow_diagram`
    for rendering). The oracles are NOT a pre-pass and their facts are NOT injected into any prompt —
    the coordinator/worker/verifier never see them, they only get OVERRIDDEN by them. So the verifier
    re-derives types the oracles already knew. Feeding these facts FORWARD into a prompt is an untested
    lever, not current behaviour (`_collect_evidence` is the opt-in pre-pass that does something like
    it)."""
    from oxide.core.oxide import api
    from agentic import tools as T, grounding as G
    from agentic.tasks import type_recovery  # noqa: F401 registers the 4 static oracles (the default)
    # env is consulted too: the harness/CLI has no opts dict, so without this AGENTIC_DOMAIN_ORACLES
    # was silently inert — which also made the registered `runtime_type_probe` oracle unreachable
    # from run_trex_one.py (it is imported, registered, and then never named).
    which = (opts.get("domain_oracles")
             or os.environ.get("AGENTIC_DOMAIN_ORACLES")
             or type_recovery.DEFAULT_ORACLES)
    # runtime_type_probe is OPT-IN and lives in extras/ (the expensive, ~5%-coverage dynamic angr probe);
    # import it only when named, so the minimal pipeline never pulls angr.
    if "runtime_type_probe" in str(which):
        try:
            from agentic.extras import runtime_probe  # noqa: F401 registers the runtime oracle
        except Exception:  # noqa: BLE001
            pass
    _s, ct = T.build_tools(api, oid, memoize=False)
    # Declared byte size per variable, straight from the question (ground-truth input, not inference).
    sizes = {m.group(1): int(m.group(2))
             for m in re.finditer(r"(?m)^\s*(V\d+)\s+(?:register|stack)\s+\S+\s+(\d+)\s*$", question or "")}
    facts: dict = {}                                         # vid -> (ctype, oname, floor); first wins
    for name, fn in G.resolve_domain_oracles(which, question):
        try:
            for f in fn(ct, question):
                if f["vid"] in facts:
                    continue
                # SOUNDNESS GUARD: never certify a pointer for a slot too small to hold one. The
                # oracles are the AUTHORITATIVE layer (the trailer applies them over the LLM), so an
                # impossible certification is strictly worse than abstaining. Measured on
                # chroot/mgetgroups: callee_signature certified V2 (4B) and spilled_param certified
                # V13 (4B) as `void *` — physically impossible — overriding a verifier that had both
                # correct as `int`. The size is GIVEN ground truth, so this check is exact, not
                # heuristic. Disable with AGENTIC_NO_SIZE_GUARD=1.
                sz = sizes.get(f["vid"])
                if (sz and sz < 8 and "*" in str(f.get("ctype", ""))
                        and os.environ.get("AGENTIC_NO_SIZE_GUARD", "") not in ("1", "true", "yes")):
                    print(f"[size-guard] dropped unsound {name} certification "
                          f"{f['vid']}={f['ctype']!r} on a {sz}-byte slot")
                    continue
                # THREE certification modes (see `_certified_trailer`): `exact` overrides
                # unconditionally, `floor` is a lower bound that defers to any pointer, and `shape`
                # sits between them -- it carries layout but no source-level name.
                mode = f.get("mode") or ("floor" if f.get("floor") else "exact")
                facts[f["vid"]] = (f["ctype"], name, mode)
        except Exception:  # noqa: BLE001
            continue
    return facts


def _rescue_undefined(messages, answer: str) -> str:
    """Never let a SPECIFIC type be replaced by an `undefinedN` one.

    The verifier always wins arbitration, but its decompilation lens is not strictly superior: when
    Ghidra emits `undefined8` for a slot the assembly worker had already typed concretely, the
    verifier overwrites a CORRECT answer with a contentless one (measured on do_encode V2:
    worker `char *` -> verifier `undefined8 *`, and the same failure is on record for get_8). This
    restores the earlier specific claim whenever the final answer degenerated to `undefined*`.
    Monotone and information-preserving — it can only replace a non-answer with an answer, never
    change one concrete type into a different concrete type. Deterministic (no LLM).
    Disable with AGENTIC_NO_UNDEF_RESCUE=1."""
    if str(os.environ.get("AGENTIC_NO_UNDEF_RESCUE", "")).strip().lower() in ("1", "true", "yes", "on"):
        return answer
    claims = _claims_from_messages(messages)
    if not claims:
        return answer
    rescued = {}
    for vid in {v for d in claims for v in d}:
        cur = None
        m = re.search(rf"(?mi)^\s*-?\s*{re.escape(vid)}\s*[:=]\s*(.+?)\s*$", answer)
        if m:
            cur = m.group(1).strip().strip("`")
        # `cur is None` means the entity is ABSENT from the final answer, not that it is specific --
        # the strongest case for rescue, and it was previously skipped. It happens when the coordinator
        # never synthesized the entity at all: measured on ginstall/vasnprintf, where the coordinator
        # emitted a tool call as literal TEXT, stopped after one worker, and answered 23 of 101
        # variables. The remaining 78 were then default-filled with `undefined` DOWNSTREAM of this
        # pass, so nothing here ever saw an `undefined` to replace. Absent and `undefined` are the
        # same non-answer and both must be rescued.
        if cur is not None and not _UNDEF_RE.match(cur):
            continue                                   # final answer is already specific -> leave it
        for d in claims:                               # earliest specific claim wins
            t = d.get(vid)
            if t and not _UNDEF_RE.match(t):
                rescued[vid] = t
                break
    if not rescued:
        return answer
    appended = []
    for vid, t in rescued.items():                     # rewrite BOTH representations consistently
        pat_line = rf"(?mi)^(\s*-?\s*{re.escape(vid)}\s*[:=]\s*).+?$"
        pat_json = rf'("{re.escape(vid)}"\s*:\s*)"[^"]*"'
        hit = re.search(pat_line, answer) or re.search(pat_json, answer)
        answer = re.sub(pat_line, lambda mo: mo.group(1) + t, answer)
        answer = re.sub(pat_json, lambda mo: mo.group(1) + json.dumps(t), answer)
        if not hit:
            appended.append(f"{vid}: {t}")             # absent entirely -> add it, nothing to rewrite
    if appended:
        answer = answer.rstrip() + "\n" + "\n".join(appended) + "\n"
    print(f"[undef-rescue] restored specific types over `undefined`: {rescued}")
    return answer


def _type_width(t: str):
    """Byte width of a reported type, or None if unknown. Any pointer is 8 on x86-64."""
    t = str(t or "").strip()
    if t.endswith("*"):
        return 8
    return _TYPE_WIDTH.get(t.lower())


def _coerce_sizes(question: str, answer: str) -> str:
    """Rewrite every reported type whose width contradicts the entity's declared size."""
    if os.environ.get("AGENTIC_NO_SIZE_COERCE", "") in ("1", "true", "yes"):
        return answer
    sizes = {m.group(1): int(m.group(2)) for m in re.finditer(
        r"(?m)^\s*(V\d+)\s+(?:register|stack)\s+\S+\s+(\d+)\s*$", question or "")}
    if not sizes:
        return answer
    fixed = {}
    for vid, want in sizes.items():
        m = re.search(rf'(?mi)^\s*-?\s*{re.escape(vid)}\s*[:=]\s*(.+?)\s*$', answer)
        if not m:
            m = re.search(rf'"{re.escape(vid)}"\s*:\s*"([^"]*)"', answer)
        if not m:
            continue
        cur = m.group(1).strip()
        new = None
        # AGGREGATE SLOT. A pointer occupies 8 bytes, so a slot WIDER than that cannot hold one --
        # the slot IS those bytes. A reported `T *` on such a slot means the value is an inline ARRAY
        # of T, which is exactly how the code uses it: `p[i]` compiles identically for `int *p` and
        # `int p[6]`, so the pointer/array distinction is invisible in the instruction stream and the
        # declared size is the only thing that settles it. Observed on date/posix_time_parse V4, GT
        # `int[6]` in a 24-byte slot, reported `int*` -- scored 1/6, halting at `!AgreeIsCPointer`,
        # the earliest and most expensive failure in the metric. Forced rather than chosen: the
        # element type is the model's own pointee and the count is an exact division.
        if want > 8 and cur.endswith("*"):
            el = cur[:-1].strip()
            ew = _type_width(el)
            if el and ew and want % ew == 0:
                new = f"{el}[{want // ew}]"
        if new is None:
            w = _type_width(cur)
            if w is None or want not in _WIDTH_TYPE:
                continue
            # NARROWING ONLY. A type WIDER than the slot is impossible -- a pointer cannot occupy 4
            # bytes -- so rewriting it to an integer of the declared width is forced, not chosen. The
            # reverse is a GUESS: `int` on an 8-byte slot may be `long` OR any pointer, and picking
            # the integer family loses. Measured on comm/readlinebuffer_delim V7 (GT `char *`):
            # coercing int -> long cost 86.21 -> 79.31, while the three narrowing fixes gained
            # +25.00, +11.91 and +1.75.
            if w <= want:
                continue
            signed_t, unsigned_t = _WIDTH_TYPE[want]
            new = unsigned_t if cur.lower() in _UNSIGNED else signed_t
        fixed[vid] = (cur, new)
        answer = re.sub(rf'(?mi)^(\s*-?\s*{re.escape(vid)}\s*[:=]\s*).+?$',
                        lambda mo: mo.group(1) + new, answer)
        answer = re.sub(rf'("{re.escape(vid)}"\s*:\s*)"[^"]*"',
                        lambda mo: mo.group(1) + json.dumps(new), answer)
    if fixed:
        print("[size-coerce] " + ", ".join(f"{v}: {a} -> {b} ({sizes[v]}B slot)"
                                           for v, (a, b) in sorted(fixed.items())))
    return answer


def _certified_trailer(oid: str, question: str, answer: str, opts: dict) -> str:
    """Append the ORACLE-CERTIFIED trailer, computed DETERMINISTICALLY in-process (not via the LLM),
    reproducing pipeline._analyze_oid_impl exactly — including floor semantics. This guarantees the
    certified facts override the model's answer regardless of subagent behaviour, preserving the
    validated +2.65pp / zero-regression property."""
    oracle_facts = _collect_oracle_facts(oid, question, opts)
    if not oracle_facts:
        return answer

    def _synth_ty(vid):
        for _j in reversed(re.findall(r"\{[^{}]*\}", answer)):
            try:
                _o = json.loads(_j)
                if vid in _o:
                    return str(_o[vid])
            except Exception:  # noqa: BLE001
                pass
        _m = re.search(rf"(?mi)^\s*-?\s*{re.escape(vid)}\s*:\s*(.+?)\s*$", answer)
        return _m.group(1) if _m else ""

    from agentic.tasks.type_recovery import is_shapeless_pointer as _shapeless

    lines = []
    for vid, (ctype, _c, _mode) in sorted(oracle_facts.items(), key=lambda kv: kv[0]):
        # A FLOOR is a lower bound — "this is a pointer", pointee unknown — not an exact type, so it
        # defers whenever the model already answered with a pointer.
        #
        # ORDERING CONSTRAINT: any model-driven pass that runs BEFORE this one can preempt a correct
        # certification through exactly this rule. A targeted re-query stage (since removed) upgraded
        # sum/argmatch_to_argument V6 from `int` to `char *`; that pointer then made this floor defer,
        # suppressing a `void *` certification that was exactly right (63.89 -> 61.11). Keep model
        # passes after certification, or have them skip entities an oracle already claims.
        #
        # Deliberately NOT depth-aware. Requiring the model to match the floor's indirection depth was
        # tried and MEASURED WORSE (ginstall/hash_rehash 45.10 -> 37.25): the certifying oracle's depth
        # is itself unreliable. There, GT is `Hash_table *` (one level) while decompiler_pointer
        # certified `void **`; the depth rule trusted that and overrode the model's correctly-shaped
        # `struct *`. For a pointee-unknown fact the sound content is only ">= pointer", never the
        # exact level — so any model pointer satisfies it.
        if _mode == "floor" and "*" in _synth_ty(vid):
            continue
        # A `shape` fact recovers field LAYOUT, never a source-level struct name. It is strictly more
        # informative than a pointee-unknown answer (`void *`, or the tagless `struct *` the model
        # emits when it sees an aggregate it cannot describe), so it replaces those -- but a named
        # pointee the agents produced is a claim this oracle cannot make, so it defers to one.
        if _mode == "shape":
            cur = _synth_ty(vid)
            if "*" in cur and not _shapeless(cur):
                continue
        # A SCALAR fact is the mirror of a floor and the only NEGATIVE claim any oracle makes: its
        # content is "not a pointer", and the integer it carries is the callee's declared type, not a
        # considered choice between `long`/`size_t`/`int`. So it fires only to demote a pointer answer
        # and otherwise defers -- the model's own integer is at least as good, and the scoring rule
        # that matters (`AgreeIsCPointer`) has already been satisfied by any integer at all.
        if _mode == "scalar" and "*" not in _synth_ty(vid):
            continue
        # A SIGN fact carries one bit: "this integer is unsigned". It is orthogonal to the class and the
        # width, so it applies only to an answer that is already a non-pointer, non-array scalar and
        # abstains otherwise -- a pointer answer is a claim this oracle cannot speak to. Measured need:
        # on sha512_process_block 171 of 179 variables had the class, width and pointer-ness all correct
        # and differed from ground truth by the sign alone, scoring 5/6 on the graded metric but 0 on
        # exact match.
        if _mode == "sign":
            _cur = _synth_ty(vid)
            if "*" in _cur or "[" in _cur or not _cur.strip():
                continue
        lines.append(f"- {vid}: {ctype}")
    if lines:
        answer = (answer.rstrip()
                  + "\n\nORACLE-CERTIFIED (deterministic, authoritative — overrides the above):\n"
                  + "\n".join(lines) + "\n")
    return answer
