"""Per-stage claim capture: what each agent asserted, before any revision.

Split out of `deepagent` (2026-07-30). Fully self-contained -- it reads a langchain message list and
writes JSON, with no dependency on the model, the tools, or the oracles.
"""
from __future__ import annotations

import json
import os
import re


def _claims_from_messages(messages) -> list:
    """Every `V<n>: <type>` claim any subagent returned, in delegation order. Subagent answers come
    back as the CONTENT of the `task` tool results, so this recovers the worker/verifier findings the
    coordinator saw."""
    out = []
    for m in messages or []:
        if getattr(m, "type", None) != "tool":
            continue
        txt = m.content if isinstance(m.content, str) else ""
        d = {}
        for mm in re.finditer(r"(?mi)^\s*-?\s*(V\d+)\s*[:=]\s*(.+?)\s*$", txt):
            t = mm.group(2).strip().strip("`").split("(")[0].split(",")[0].strip()
            if t and len(t) < 40:
                d[mm.group(1)] = t
        for jm in re.finditer(r"\{[^{}]*\}", txt):
            try:
                o = json.loads(jm.group(0))
            except Exception:  # noqa: BLE001
                continue
            if isinstance(o, dict):
                for k, v in o.items():
                    if re.fullmatch(r"V\d+", str(k)) and isinstance(v, str):
                        d[str(k)] = v.strip()
        if d:
            out.append(d)
    return out


def _claims_by_agent(messages) -> list:
    """`[{"agent": "type_worker", "claims": {"V1": "char *", ...}}, ...]` in delegation order.

    Same extraction as `_claims_from_messages`, but each subagent's findings are ATTRIBUTED to the
    subagent that produced them, by matching the `task` tool call that spawned it to the tool result
    it returned. Attribution is what makes a per-stage ablation possible: with it, the assembly
    worker's answer and the decompilation reviewer's revision of that answer can be scored
    separately, from a stored run and with no model re-run -- so a two-lens ablation becomes exact
    rather than noise-limited (§ the certification ablation has this property already; the agent
    stages did not, purely because the intermediate answers were computed and then discarded)."""
    spawned, briefs = {}, {}                                 # tool_call_id -> subagent type / brief
    for m in messages or []:
        for tc in (getattr(m, "tool_calls", None) or []):
            if (tc.get("name") if isinstance(tc, dict) else None) == "task":
                args = tc.get("args") or {}
                spawned[tc.get("id")] = str(args.get("subagent_type") or "?")
                # The DELEGATION BRIEF the coordinator actually wrote. Recorded because what a
                # subagent receives is decided by the coordinator at run time, not by the static
                # prompt: the coordinator is *instructed* to forward the workers' candidate claims to
                # the reviewer, and whether it does is an empirical question about one LLM following
                # another LLM's spec. Without this the two-lens ablation cannot say whether the
                # reviewer was revising candidates or typing the function from scratch.
                briefs[tc.get("id")] = str(args.get("description") or "")[:4000]
    out = []
    for m in messages or []:
        if getattr(m, "type", None) != "tool":
            continue
        txt = m.content if isinstance(m.content, str) else ""
        d = {}
        for mm in re.finditer(r"(?mi)^\s*-?\s*(V\d+)\s*[:=]\s*(.+?)\s*$", txt):
            t = mm.group(2).strip().strip("`").split("(")[0].split(",")[0].strip()
            if t and len(t) < 60:
                d[mm.group(1)] = t
        for jm in re.finditer(r"\{[^{}]*\}", txt):
            try:
                o = json.loads(jm.group(0))
            except Exception:  # noqa: BLE001
                continue
            if isinstance(o, dict):
                for k, v in o.items():
                    if re.fullmatch(r"V\d+", str(k)) and isinstance(v, str):
                        d[str(k)] = v.strip()
        alts = {}                                            # `ALTS V1: void * | long` (AGENTIC_TOPK)
        for am in re.finditer(r"(?mi)^\s*ALTS?\s+(V\d+)\s*[:=]\s*(.+?)\s*$", txt):
            cand = [c.strip().strip("`") for c in am.group(2).split("|")]
            cand = [c for c in cand if c and len(c) < 60]
            if cand:
                alts.setdefault(am.group(1), []).extend(cand)
        if d or alts:
            _tid = getattr(m, "tool_call_id", None)
            out.append({"agent": spawned.get(_tid, "?"), "brief": briefs.get(_tid, ""),
                        "claims": d, "alts": alts})
    return out


def _dump_tool_calls(messages) -> None:
    """Every tool call the models EMITTED, whether or not it reached the server.

    The MCP-side log only records calls that arrived. A call the model emitted with bad arguments is
    rejected before that and looks identical to a call never attempted, which is the difference
    between "the model won't select this tool" and "the model selects it and we drop it"."""
    if not os.environ.get("AGENTIC_DUMP_TOOLCALLS"):
        return
    seen = []
    for m in messages or []:
        for tc in (getattr(m, "tool_calls", None) or []):
            nm = tc.get("name") if isinstance(tc, dict) else getattr(tc, "name", None)
            seen.append(nm)
        inv = getattr(m, "invalid_tool_calls", None) or []
        for tc in inv:
            nm = (tc.get("name") if isinstance(tc, dict) else None) or "?"
            err = (tc.get("error") if isinstance(tc, dict) else "") or ""
            print(f"[toolcalls] INVALID {nm}: {str(err)[:160]}")
    from collections import Counter
    print(f"[toolcalls] emitted: {dict(Counter(seen))}")


def _log_claims(messages) -> None:
    """Persist per-subagent claims to AGENTIC_CLAIM_LOG (opt-in). Cheap, and it is the only record
    of what each stage believed BEFORE the next stage revised it."""
    path = os.environ.get("AGENTIC_CLAIM_LOG", "").strip()
    if not path:
        return
    try:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        with open(path, "w") as fh:
            json.dump(_claims_by_agent(messages), fh, indent=1)
    except Exception as e:  # noqa: BLE001  never let logging break a run
        print(f"[claim-log] skipped — {str(e)[:120]}")
