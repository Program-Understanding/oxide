"""The evidence audit: label each answer by the oracle evidence that supports or contradicts it.

This is the GROUND-TRUTH-FREE half of the claim the paper makes. `Apply` decides what an oracle
constraint does TO an answer; the audit asks the orthogonal question of whether the answer the
pipeline actually produced SATISFIES the constraints that were available for it, and reports that
per variable as one of:

    unsupported   no oracle made any claim about this variable
    contradicted  at least one claim on it disagrees with the final type
    corroborated  it carries at least one claim and every one of them agrees

Two properties are deliberate. First, the audit reads only the binary-derived claims and the final
answer, never ground truth, so it is computable at analysis time on a stripped binary -- which is
the whole point of reporting it to an analyst. Second, AGREEMENT IS NOT THE OVERRIDE RULE. A claim
can agree with an answer it would not itself have produced: a `shape` claim agrees with any
pointer, while it OVERRIDES a pointer whose pointee is unnamed. `Apply` repairs violations and
refines agreements; the audit records violations only. Keeping the two readings separate is what
makes the label mean "consistent with the evidence" rather than "produced by the evidence".

The agreement column implemented here is the one tabulated in the paper; `agree()` is a direct
transcription of it, and `test_audit.py` pins every row.
"""
from __future__ import annotations

import json
import os
import re

from .common import is_shapeless_pointer

# A scalar the code reports as unsigned. Kept separate from `common._UNSIGNED` (which drives size
# coercion) because the audit must recognise the fixed-width spellings the signedness oracle emits.
_UNSIGNED_RE = re.compile(r"^\s*(?:unsigned\b|u(?:int|char|short|long)|uint\d+_t|size_t|"
                          r"ulong|ushort|uchar|byte|word|dword|qword|ulonglong|uintmax_t)",
                          re.I)

_ARRAY_RE = re.compile(r"\[\s*\d*\s*\]\s*$")

LABELS = ("corroborated", "contradicted", "unsupported")


def is_pointer(t: str) -> bool:
    return "*" in str(t or "")


def is_array(t: str) -> bool:
    return bool(_ARRAY_RE.search(str(t or "")))


def is_unsigned_scalar(t: str) -> bool:
    t = str(t or "").strip()
    return bool(t) and not is_pointer(t) and not is_array(t) and bool(_UNSIGNED_RE.match(t))


def _norm(t: str) -> str:
    """Normalize a type for the EXACT comparison: collapse whitespace and drop the space before a
    star, so `char *` and `char*` are the same claim."""
    return re.sub(r"\s+", " ", str(t or "").strip()).replace(" *", "*").lower()


def agree(mode: str, ctype: str, answer: str):
    """Does `answer` satisfy a claim of `mode` asserting `ctype`? None when undecidable.

    Transcribes the agreement column of the claim-mode table:
        exact   answer is the claimed type
        floor   answer is a pointer
        shape   answer is a pointer
        scalar  answer is not a pointer
        sign    answer is an unsigned scalar
    """
    a = str(answer or "").strip()
    if not a:
        return None                                   # nothing was answered: not a disagreement
    m = (mode or "exact").strip().lower()
    if m == "exact":
        return _norm(a) == _norm(ctype)
    if m in ("floor", "shape"):
        return is_pointer(a)
    if m == "scalar":
        return not is_pointer(a)
    if m == "sign":
        return is_unsigned_scalar(a)
    return None                                       # unknown mode: abstain rather than guess


def _as_claims(facts) -> dict:
    """Accept either shape of the oracle record and return {vid: [(ctype, oracle, mode), ...]}.

    `_collect_oracle_facts` keeps the FIRST oracle per variable, so its dump has one claim per vid
    (`{vid: [ctype, oracle, mode]}`). `collect_claims` below keeps them all
    (`{vid: [[ctype, oracle, mode], ...]}`). The audit reads both so it can run retroactively over
    already-completed runs as well as on fresh ones."""
    out = {}
    for vid, v in (facts or {}).items():
        if not v:
            continue
        if isinstance(v[0], (list, tuple)):           # already a list of claims
            out[vid] = [tuple(c) for c in v if c]
        else:                                          # a single (ctype, oracle, mode)
            out[vid] = [tuple(v)]
    return out


def audit(facts: dict, pred: dict) -> dict:
    """{vid: {label, claims, disagreeing}} for every variable in `pred`.

    `facts` is an oracle record in either shape; `pred` is {vid: final type}. Variables absent from
    `pred` are still labelled, because an entity the pipeline never answered is exactly as
    unsupported as one no oracle reached."""
    claims = _as_claims(facts)
    vids = list(pred or {}) + [v for v in claims if v not in (pred or {})]
    out = {}
    for vid in vids:
        answer = (pred or {}).get(vid, "")
        cs = claims.get(vid) or []
        if not cs:
            out[vid] = {"label": "unsupported", "claims": [], "disagreeing": []}
            continue
        bad = []
        for ctype, oracle, mode in cs:
            if agree(mode, ctype, answer) is False:
                bad.append({"oracle": oracle, "mode": mode, "ctype": ctype})
        out[vid] = {
            "label": "contradicted" if bad else "corroborated",
            "claims": [{"oracle": o, "mode": m, "ctype": c} for c, o, m in cs],
            "disagreeing": bad,
        }
    return out


def summarize(labels: dict) -> dict:
    """Counts and shares by label, for the coverage half of the evaluation."""
    n = len(labels or {})
    c = {k: 0 for k in LABELS}
    for v in (labels or {}).values():
        c[v["label"]] = c.get(v["label"], 0) + 1
    out = {"n": n, **c}
    if n:
        out.update({f"{k}_pct": round(100.0 * c[k] / n, 2) for k in LABELS})
    out["reached_pct"] = round(100.0 * (n - c["unsupported"]) / n, 2) if n else 0.0
    return out


def collect_claims(oid: str, question: str, opts: dict) -> dict:
    """Every oracle claim per variable, keeping ALL of them rather than first-wins.

    `certify._collect_oracle_facts` retains one claim per variable because it feeds an APPLY step
    where precedence matters. The audit needs the whole set: the guarantee it reports is about the
    intersection of the claims on a variable, so dropping the later ones would silently weaken both
    the corroborated label and the per-oracle precision breakdown."""
    from oxide.core.oxide import api
    from agentic import tools as T, grounding as G
    from agentic.tasks import type_recovery
    which = (opts.get("domain_oracles") or os.environ.get("AGENTIC_DOMAIN_ORACLES")
             or type_recovery.DEFAULT_ORACLES)
    _s, ct = T.build_tools(api, oid, memoize=False)
    sizes = {m.group(1): int(m.group(2))
             for m in re.finditer(r"(?m)^\s*(V\d+)\s+(?:register|stack)\s+\S+\s+(\d+)\s*$",
                                  question or "")}
    claims: dict = {}
    for name, fn in G.resolve_domain_oracles(which, question):
        try:
            for f in fn(ct, question):
                vid, ctype = f["vid"], f.get("ctype", "")
                mode = f.get("mode") or ("floor" if f.get("floor") else "exact")
                sz = sizes.get(vid)
                if sz and sz < 8 and "*" in str(ctype):
                    continue                           # same realizability guard the apply path uses
                claims.setdefault(vid, []).append((ctype, name, mode))
        except Exception:  # noqa: BLE001  one oracle must not lose the others
            continue
    return claims


def audit_run(out_dir: str, fn: str) -> dict:
    """Audit one completed run directory, writing `audit_<fn>.json`. Works retroactively: both
    inputs are artifacts every run already persists."""
    def _load(p):
        try:
            with open(p) as fh:
                return json.load(fh)
        except Exception:  # noqa: BLE001
            return {}
    facts = _load(os.path.join(out_dir, f"oracle_claims_{fn}.json")) or \
        _load(os.path.join(out_dir, f"oracles_{fn}.json"))
    pred = _load(os.path.join(out_dir, f"pred_{fn}.json"))
    labels = audit(facts, pred)
    rec = {"function": fn, "summary": summarize(labels), "variables": labels}
    with open(os.path.join(out_dir, f"audit_{fn}.json"), "w") as fh:
        json.dump(rec, fh, indent=1)
    return rec
