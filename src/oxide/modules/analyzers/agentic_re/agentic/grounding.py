"""Domain-oracle registry for the agentic RE feature.

TASK-SPECIFIC deterministic certifiers (a task's Ω) register here at import via
`register_domain_oracle(name, fn)`, and the pipeline dispatches only the ones a task names. See
`tasks/type_recovery.py` (callee-signature / decompiler-pointer / spilled-param / interprocedural) and
`tasks/runtime_probe.py` (runtime type probe). This keeps the library free of any single task's domain
knowledge — the deepagent's oracle trailer calls `resolve_domain_oracles(...)` to get the ordered set.

(The old task-generic V*/R* grounding + recall oracles — deterministic_grounding, call_grounding,
false_absence, enumerate/value/coordinate recall — were retired with the custom pipeline; the deepagent
verifies via its decompilation lens and the deterministic oracle trailer instead.)
"""
from __future__ import annotations

import re

DOMAIN_ORACLES: dict = {}          # name -> normalized oracle fn; populated by task modules on import


def register_domain_oracle(name: str, fn) -> None:
    """Register a task-specific deterministic oracle under `name` (idempotent overwrite). Called by a
    task module (e.g. tasks/type_recovery.py) on import; the harness imports the task module it needs."""
    DOMAIN_ORACLES[name] = fn


DOMAIN_EVIDENCE: dict = {}         # name -> evidence-gatherer fn; populated by task modules on import


def register_domain_evidence(name: str, fn) -> None:
    """Register a task-specific deterministic EVIDENCE GATHERER under `name`.

    Distinct from an oracle: an oracle CERTIFIES an answer and overrides the model, whereas a gatherer
    only assembles facts and hands them to the model to reason over. Measured 2026-07-26: the model
    never chooses the tools that would surface these facts (`xrefs_to`/`read_values`/`compute`: 0 calls
    in 72), and telling it to is ineffective — so the gathering is done for it, in code."""
    DOMAIN_EVIDENCE[name] = fn


def resolve_domain_evidence(spec) -> list:
    """Map a task's evidence specification to an ordered list of (name, fn) pairs (same spec grammar as
    `resolve_domain_oracles`: list, comma/space string, or "auto" = all registered)."""
    if isinstance(spec, str):
        names = [s for s in re.split(r"[,\s]+", spec.strip()) if s]
    else:
        names = list(spec or [])
    if names == ["auto"]:
        names = list(DOMAIN_EVIDENCE.keys())
    return [(n, DOMAIN_EVIDENCE[n]) for n in names if n in DOMAIN_EVIDENCE]


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
