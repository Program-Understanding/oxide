"""Deterministic grounding + recall oracles for the native Oxide agentic RE feature.

Model-independent mechanisms that certify/refute findings (and recover lost facts) by RE-RUNNING
the cited tools and checking the fresh output. Two families:

  V* — VERIFY one finding by reproduction:
    V1  deterministic_grounding  — certify a recovered VALUE (re-run the cited compute/read tool)
    V3  call_grounding           — certify a CALL/control-flow claim (re-run the cited disassembly)
    V4  false_absence            — refute a false-NEGATIVE ("X is never called" but X IS called)

  R* — RECALL deterministic facts at synthesis, so a tool-recovered fact isn't dropped:
    R1  enumerate_program_calls  — the program's named call set (capability recall)
    R3  value_recall_facts       — computed outputs of cited transforms
    R4  coordinate_recall_facts  — vaddr -> file offset for vaddrs in the verified findings

(V2/R2 were earlier variants, since removed — the numbering is kept stable for the surviving ones.)

The V*/R* oracles above are TASK-GENERIC. TASK-SPECIFIC certifiers (the task's Ω) are NOT defined
here; a task module registers them at import via `register_domain_oracle(name, fn)` and the pipeline
dispatches only the ones a task names. See e.g. `tasks/type_recovery.py` for the callee-signature and
decompiler-pointer type oracles. This keeps the core library free of any single task's domain knowledge.
"""
from __future__ import annotations

import json
import re

# deterministic recovery tools whose output can be re-derived exactly (no model needed)
_DETERMINISTIC_TOOLS = ("compute", "read_values")
_VALUE_TOK = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_.:/+\-]{3,}")

# disassembly tools whose `call <target>` text reveals which functions the code invokes
_CALL_TOOLS = ("disassemble", "callgraph")
_CALL_RE = re.compile(r"\bcall\w*\s+([A-Za-z_][\w.@]*)")
_CALL_PREFIXES = ("sym.imp.", "sym.func.", "sym.", "reloc.", "dbg.", "fcn.", "imp.", "loc.")
_NEG_RE = re.compile(r"\b(?:not|no|never|without|absent|lacks?|missing|n't)\b", re.I)

_ADDRISH = re.compile(r"^(?:fcn|func|sub|loc)?[._]?[0-9a-f]{3,}$")
_RUNTIME_MARKERS = (
    "ubsan", "asan", "msan", "tsan", "sanitiz", "compiler_rt", "panic", "syscall_cp",
    "errno", "io.writer", "io.reader", "stack_chk", "__cxa", "register_tm", "frame_dummy",
    "gmon", "_dl_", "unwind", "personality",
    "tl_lock", "tl_unlock", "_ptc", "app_sigs", "restore_sig", "syscall_ret", "dummy")
_RUNTIME_EXACT = {"lock", "unlock"}

_TRANSFORM_TOOLS = ("compute",)


def _decode_payload(fresh: str) -> str:
    """The actual computed result from a tool's output (not the echoed args)."""
    try:
        d = json.loads(fresh)
        if isinstance(d, dict):
            return str(d.get("result") or fresh)
    except Exception:  # noqa: BLE001
        pass
    return str(fresh)


def _bare_callee(name: str) -> str:
    """Reduce a call target (sym.imp.execve, dbg.connect@plt) to its bare name (execve)."""
    b = name.split("@")[0]
    changed = True
    while changed:
        changed = False
        for pre in _CALL_PREFIXES:
            if b.startswith(pre):
                b, changed = b[len(pre):], True
    return b.strip("._").lower()


def _called_funcs(fresh: str) -> set:
    """Functions CALLED in a disassemble/callgraph output (`call <target>` insns + `CALLS:` summary)."""
    names = set(_CALL_RE.findall(fresh))
    m = re.search(r"CALLS:\s*([^\n]+)", fresh)
    if m:
        names.update(p.strip() for p in m.group(1).split(","))
    return {b for n in names if len(b := _bare_callee(n)) >= 4}


# --------------------------------------------------------------- V1: value certify
def deterministic_grounding(call_tool, finding):
    """V1 — certify a finding's VALUE: re-run the cited deterministic tool and check its fresh
    output appears verbatim in the claim. Returns (grounded, evidence)."""
    claim = str(finding.get("claim", ""))
    for ref in finding.get("evidence_refs", []) or []:
        tool, args = ref.get("tool"), (ref.get("args") or {})
        if tool not in _DETERMINISTIC_TOOLS or not args:
            continue
        try:
            fresh = call_tool(tool, args)
        except Exception:  # noqa: BLE001
            continue
        if not fresh or "error" in fresh[:40].lower():
            continue
        argvals = {str(v).lower() for v in args.values()}
        payload = _decode_payload(fresh)
        for tok in _VALUE_TOK.findall(payload):
            if tok.lower() in argvals:
                continue
            if any(c.isdigit() or c in "./:" for c in tok) and len(tok) >= 4 and tok in claim:
                return True, f"{tool}({json.dumps(args)}) reproduced '{tok}'"
    return False, ""


# --------------------------------------------------------------- V3: call certify
def call_grounding(call_tool, finding):
    """V3 — certify a CALL claim: re-run the cited disassembly and confirm a call named in the
    claim is actually in the code's call set. Returns (grounded, evidence)."""
    claim = str(finding.get("claim", ""))
    if _NEG_RE.search(claim):
        return False, ""
    claim_toks = {t.lower() for t in re.findall(r"[A-Za-z_][\w]{3,}", claim)}
    for ref in finding.get("evidence_refs", []) or []:
        tool, args = ref.get("tool"), (ref.get("args") or {})
        if tool not in _CALL_TOOLS or not args:
            continue
        try:
            fresh = call_tool(tool, args)
        except Exception:  # noqa: BLE001
            continue
        if not fresh or "error" in fresh[:40].lower():
            continue
        called = _called_funcs(fresh)
        hit = sorted(t for t in claim_toks
                     if t in called or (len(t) >= 5 and any(t in c for c in called)))
        if hit:
            return True, f"{tool}({json.dumps(args)}) shows the code calls {', '.join(hit)}"
    return False, ""


# --------------------------------------------------------------- V4: false-absence refute
def false_absence(call_tool, finding):
    """V4 — refute a false-NEGATIVE: if the claim asserts a call is ABSENT but the cited disassembly
    shows it IS present, the absence is false. Returns an evidence string or ''."""
    claim = str(finding.get("claim", ""))
    low = claim.lower()
    if not _NEG_RE.search(low):
        return ""
    claim_toks = {t.lower() for t in re.findall(r"[A-Za-z_][\w]{3,}", claim)}
    for ref in finding.get("evidence_refs", []) or []:
        tool, args = ref.get("tool"), (ref.get("args") or {})
        if tool not in _CALL_TOOLS or not args:
            continue
        try:
            fresh = call_tool(tool, args)
        except Exception:  # noqa: BLE001
            continue
        if not fresh or "error" in fresh[:40].lower():
            continue
        called = _called_funcs(fresh)
        present = []
        for t in claim_toks:
            if not (t in called or (len(t) >= 5 and any(t in c for c in called))):
                continue
            idx = low.find(t)
            if idx < 0:
                continue
            clause_start = max(low.rfind(".", 0, idx), low.rfind(";", 0, idx)) + 1
            if _NEG_RE.search(low[max(clause_start, idx - 60):idx]):
                present.append(t)
        if present:
            return (f"{tool}({json.dumps(args)}) shows the code DOES call "
                    f"{', '.join(sorted(set(present)))} — the claimed absence is false")
    return ""


# --------------------------------------------------- V5: false register-source (anti-hallucination)
_REG = r"(?:r[abcd]x|r[sd]i|r[bs]p|r(?:8|9|1[0-5])|e[abcd]x|e[sd]i|[abcd][lx])"
_REG_SRC_RE = re.compile(r"\b(?:stored|saved|copied|moved|loaded|comes?|from|holds?|is|=)\b[^.;\n]{0,28}?\b(" + _REG + r")\b", re.I)
_STORE_RE = re.compile(r"mov\s+(?:[a-z]+\s+ptr\s+)?\[[^\]]+\]\s*,\s*(" + _REG + r")\b", re.I)


def _reg_family(r: str) -> str:
    """Normalize a register to its family so rax/eax/ax/al compare equal."""
    r = r.lower()
    fam = {"rax": "a", "eax": "a", "ax": "a", "al": "a", "rbx": "b", "ebx": "b", "bx": "b", "bl": "b",
           "rcx": "c", "ecx": "c", "cx": "c", "cl": "c", "rdx": "d", "edx": "d", "dx": "d", "dl": "d",
           "rsi": "si", "esi": "si", "si": "si", "rdi": "di", "edi": "di", "di": "di",
           "rbp": "bp", "ebp": "bp", "rsp": "sp", "esp": "sp"}
    return fam.get(r, r)


def false_register_source(call_tool, finding):
    """Refute a false REGISTER-SOURCE claim. If a claim says a stack slot 'is stored from <REG>' but
    re-running stack_var shows the slot is written from a DIFFERENT register, the claim is false.
    Deterministic — catches verifier/worker hallucinations like 'V9 stored from RAX' when the code
    actually does `mov [rbp-0xf0],rcx`. Returns an evidence string (naming the real register) or ''."""
    claim = str(finding.get("claim", ""))
    m = _REG_SRC_RE.search(claim)
    if not m:
        return ""
    claimed = m.group(1)
    off = addr = None
    for ref in finding.get("evidence_refs", []) or []:
        a = ref.get("args") or {}
        if a.get("offset") and off is None:
            off = a["offset"]
        if a.get("addr") and addr is None:
            addr = a["addr"]
    if off is None:
        mo = re.search(r"(?:stack|rbp)\s*\+?\s*(-?0x[0-9a-fA-F]+)", claim)
        off = mo.group(1) if mo else None
    if not off or not addr:
        return ""
    try:
        fresh = call_tool("stack_var", {"addr": addr, "offset": off})
    except Exception:  # noqa: BLE001
        return ""
    if not fresh or "error" in str(fresh)[:40].lower():
        return ""
    stores = _STORE_RE.findall(str(fresh))
    if not stores:
        return ""
    actual = stores[0]                       # first store = the initial spill into the slot
    if _reg_family(actual) != _reg_family(claimed):
        return (f"stack_var({off}) shows the slot is written from {actual.upper()}, "
                f"not {claimed.upper()} — the claimed register source is false")
    return ""


# --------------------------------------------------------------- R4: coordinate recall
_ADDR_TOK = re.compile(r"0x[0-9a-fA-F]{3,}")


def coordinate_recall_facts(call_tool, records) -> list:
    """R4 — coordinate recall: for every vaddr in the AGREE'd findings, re-run vaddr_to_file_offset
    and surface 'vaddr X = file offset Y' as a fact. Returns a list of (fact, ref)."""
    vaddrs = set()
    for r in records:
        f = r.get("finding", {}) or {}
        if r.get("verdict", {}).get("consensus") != "AGREE":
            continue
        for tok in _ADDR_TOK.findall(str(f.get("claim", ""))):
            try:
                vaddrs.add(int(tok, 16))
            except ValueError:
                pass
    if not vaddrs:
        return []
    arg = ",".join(hex(v) for v in sorted(vaddrs))
    try:
        out = call_tool("vaddr_to_file_offset", {"vaddr": arg})
        data = json.loads(out)
    except Exception:  # noqa: BLE001
        return []
    if isinstance(data, dict):
        data = [data]
    facts, seen = [], set()
    for row in data if isinstance(data, list) else []:
        if not isinstance(row, dict):
            continue
        va, fo = row.get("vaddr"), row.get("file_offset")
        if not va or not fo or va == fo or va in seen:
            continue
        seen.add(va)
        facts.append((f"virtual address {va} corresponds to file offset {fo}",
                      {"tool": "vaddr_to_file_offset", "args": {"vaddr": va}}))
    return facts


# --------------------------------------------------------------- R1: program call set
def enumerate_program_calls(call_tool, root: str = "main", max_funcs: int = 24) -> dict:
    """R1 — capability recall: the NAMED functions the program invokes (from the call graph),
    mapped callee -> calling functions; anonymous/address-like and runtime targets are dropped."""
    out = call_tool("callgraph", {"root": root, "max_funcs": max_funcs})
    callers: dict = {}
    for line in str(out).splitlines():
        if " -> " not in line:
            continue
        lhs, rhs = line.split(" -> ", 1)
        caller = _bare_callee(lhs.strip()) or lhs.strip()
        for tgt in rhs.split(","):
            t = tgt.strip()
            if not t or t.startswith("("):
                continue
            callee = _bare_callee(t)
            if (len(callee) >= 3 and "(" not in callee and not _ADDRISH.match(callee)
                    and callee not in _RUNTIME_EXACT
                    and not any(m in callee for m in _RUNTIME_MARKERS)):
                callers.setdefault(callee, set()).add(caller)
    return callers


# --------------------------------------------------------------- R3: value recall
def value_recall_facts(call_tool, records) -> list:
    """R3 — value recall: re-run every cited deterministic transform and surface its computed
    OUTPUT as a fact, so a tool-recovered value isn't lost at synthesis. Returns a list of (fact, ref)."""
    seen, facts = set(), []
    for r in records:
        for ref in (r.get("finding", {}) or {}).get("evidence_refs", []) or []:
            tool, args = ref.get("tool"), (ref.get("args") or {})
            if tool not in _TRANSFORM_TOOLS or not args:
                continue
            sig = (tool, json.dumps(args, sort_keys=True, default=str))
            if sig in seen:
                continue
            seen.add(sig)
            try:
                fresh = call_tool(tool, args)
            except Exception:  # noqa: BLE001
                continue
            if not fresh or "error" in fresh[:40].lower():
                continue
            v = _decode_payload(fresh).strip()
            expr = str(args.get("expr") or args.get("expression") or "")
            bare_const = re.fullmatch(r"\s*[+-]?(0x[0-9a-fA-F]+|\d+)\s*", expr) is not None
            if re.fullmatch(r"-?\d+", v) and not bare_const:
                facts.append((f"`compute({expr})` = {v}", ref))
    return facts


# ============================================================================================
#  Domain-oracle registry (Ω) and dispatcher.
#  The CORE library defines NO task-specific oracle. TASK MODULES (see tasks/) register their
#  certifiers here at import via register_domain_oracle(name, fn); the pipeline dispatches only the
#  ones a task names in its Ω. Each registered oracle is `fn(call_tool, question) -> list of
#  {"vid","ctype","source","claim","reason"}`. This keeps the core free of any single task's domain
#  knowledge (design goal G3).
# ============================================================================================

DOMAIN_ORACLES: dict = {}          # name -> normalized oracle fn; populated by task modules on import


def register_domain_oracle(name: str, fn) -> None:
    """Register a task-specific deterministic oracle under `name` (idempotent overwrite). Called by a
    task module (e.g. tasks/type_recovery.py) on import; the harness imports the task module it needs."""
    DOMAIN_ORACLES[name] = fn


def resolve_domain_oracles(spec, question: str = "") -> list:
    """Map a task's Ω specification to an ordered list of (name, fn) pairs to dispatch. `spec` is a
    list of names, a comma/space-separated string, or the literal ``"auto"`` (= every currently
    registered domain oracle, since a task module registers only its own). Order is significant —
    earlier oracles take precedence when two would pin the same entity. Unknown names are ignored."""
    if isinstance(spec, str):
        names = [s for s in re.split(r"[,\s]+", spec.strip()) if s]
    else:
        names = list(spec or [])
    if names == ["auto"]:
        names = list(DOMAIN_ORACLES.keys())
    return [(n, DOMAIN_ORACLES[n]) for n in names if n in DOMAIN_ORACLES]
