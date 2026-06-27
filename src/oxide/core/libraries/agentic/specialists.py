"""Specialist roster — the SINGLE place that defines the agents the planner can dispatch.

Each specialist is one `Specialist(...)` declaration: the tool GROUPS it may use and its backstory
(the persona preamble prepended to the shared WORKER_BACKSTORY in prompts.py). A worker for a
specialist sees only that specialist's tool subset, so it leverages one backend's strengths; the
verifier/grounding can still call any tool.

HOW TO ADD A NEW SPECIALIST
  1. Add one `register(Specialist(name=..., groups=..., backstory="..."))` to the roster below.
       • groups : tuple of tool groups it sees (the `group=` tags on @tool in tools/*.py);
                  None = all tools (the generalist).
  2. So the planner can route to it, add its name to the hand-written menu in prompts.py
     (PLANNER_SYS) — that stays readable prose on purpose (see the menu comment there).
The accessors below (names/groups_for/backstory) then pick it up automatically.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

from oxide.core.libraries.agentic import prompts as P


@dataclass(frozen=True)
class Specialist:
    name: str
    groups: Optional[Tuple[str, ...]]   # tool groups exposed to it; None = all groups (generalist)
    backstory: str                      # persona preamble; WORKER_BACKSTORY rules appended at use


SPECIALISTS: dict = {}      # name -> Specialist


def register(spec: Specialist) -> Specialist:
    SPECIALISTS[spec.name] = spec
    return spec


# --- the roster -----------------------------------------------------------------------------
register(Specialist(
    name="ghidra",
    groups=("ghidra", "elf", "util"),
    backstory=("You are a GHIDRA specialist. Your strengths are decompilation, function and TYPE "
               "recovery, control-flow, and reading call targets. Prefer decompile, disassemble, "
               "cfg, callgraph, function_summary, xrefs_to, references_to (which code uses "
               "a string/global address)."),
))
register(Specialist(
    name="generalist",
    groups=None,
    backstory=("You are a generalist reverse-engineer with the full tool set; choose whatever "
               "tools the sub-question needs."),
))


# --- accessors (stable API used by the plugin) ----------------------------------------------
def names() -> list:
    return list(SPECIALISTS)


def groups_for(name: str):
    """Tool groups for a specialist (None = all). Unknown name -> generalist (all tools)."""
    spec = SPECIALISTS.get(name)
    return list(spec.groups) if spec and spec.groups is not None else None


def backstory(name: str) -> str:
    """Specialist persona + the shared hardened worker grounding rules."""
    spec = SPECIALISTS.get(name) or SPECIALISTS["generalist"]
    return spec.backstory + "\n\n" + P.WORKER_BACKSTORY
