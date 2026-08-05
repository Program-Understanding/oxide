"""Run-flow recorder and turn-by-turn sequence diagram for any LangChain / deepagents run.

STANDALONE. This module imports nothing from its host package: only the standard library and,
optionally, `langchain_core` (for the callback base class), the Mermaid CLI (to rasterise), and
Pillow (to compose the final figure). Every one of those is optional -- without langchain the
recorder is inert, without the Mermaid CLI you still get the `.mmd` source, without Pillow you
still get the diagram, just not the input/output panels. Copy the file into any project that
drives a tool-calling agent and it works there unchanged.

    from flow_recorder import FlowRecorder, emit, rescore

    rec = FlowRecorder()
    result = agent.invoke(inputs, config={"callbacks": [rec]})

    emit(rec, "out/run", title="cut/cut_fields @0x102f27",
         inventory=[("V1", "register 0x38", 8), ("V6", "stack -0x30", 4)],
         answer=result["messages"][-1].content)
    # -> out/run_turns.mmd, .svg, .png

    rescore(score=86.11, ground_truth={"V1": "FILE *"})   # re-render with an overlay

What it records, from three LangChain callbacks: every tool call with its arguments and its
returned result, every delegation to a subagent (with the brief the parent wrote and the findings
the child returned), and the model's reasoning text between tool calls. Phases are segmented by
delegation, which matches the serial parent -> child flow without reconstructing the run-id tree.

Everything domain-specific -- what a "variable" is, which tools are oracles, what the ground truth
was -- is INJECTED through `emit`, never imported. The default view is the sequence diagram; pass
`views=` to also write the overview flowchart or the markdown log.
"""
from __future__ import annotations

from dataclasses import dataclass, field

import json
import os
import re
import shutil
import subprocess

try:
    from langchain_core.callbacks import BaseCallbackHandler
except Exception:  # noqa: BLE001  # langchain not installed -> feature simply unavailable
    BaseCallbackHandler = object  # type: ignore


# tools that ARE the orchestration (handled specially), vs analysis tools (grouped under a phase)
_PLAN_TOOL = "write_todos"
_DELEGATE_TOOL = "task"
_ORCHESTRATION = {_PLAN_TOOL, _DELEGATE_TOOL}
# Tools whose return is a LIST OF PER-ENTITY FACTS rather than prose. Their output is kept whole
# (a prefix cap would show the first record and hide the rest) and rendered as `id=value` pairs.
# Callers with different fact tools can extend this set before recording; it is only a display hint.
FACT_TOOLS = {"static_type_oracles", "callee_signature", "decompiler_pointer", "spilled_param",
              "interprocedural_param_usage", "signedness", "struct_shape"}
_ORACLE_TOOL_NAMES = FACT_TOOLS          # backwards-compatible alias


@dataclass
class Style:
    """How the sequence diagram is drawn. Every field has a working default; override only what
    your pipeline needs. Pass an instance to `emit(..., style=Style(...))`.

    root            label for the orchestrating agent (the one that delegates)
    tools           label for the lifeline every tool call goes to
    facts           label for the deterministic-facts lifeline, drawn only when facts are applied
                    by code rather than fetched by the agent itself
    agent_suffix    appended to each discovered sub-agent name ("planner" -> "planner agent")
    icons           prefix participants with emoji; set False for plain ASCII
    icon_for        name substring -> emoji, first match wins
    roles           sub-agent name -> verb shown on its delegation arrow ("adjudicate", "search")
    entity_re       regex for the entity ids your agents argue about, used to summarise a
                    delegation as a span ("V1-V6"). Set None if your domain has no such ids.
    fact_tools      tools whose output is a list of per-entity facts, rendered as `id=value` pairs
    max_tools       tool calls drawn per phase before the rest are summarised
    max_reason      characters of a reasoning note
    show_reasoning  draw the model's between-call reasoning as notes
    show_plan       draw the plan rows above the first delegation
    """
    root: str = "Coordinator"
    tools: str = "Tools"
    facts: str = "Facts"
    agent_suffix: str = " agent"
    icons: bool = True
    icon_for: dict = field(default_factory=lambda: {
        "coordinator": "\U0001f9ed", "verif": "\U0001f50d", "worker": "\u2699\ufe0f",
        "tool": "\U0001f527", "fact": "\u2705", "oracle": "\u2705"})
    roles: dict = field(default_factory=dict)
    entity_re: str = r"V\d+"
    fact_tools: frozenset = frozenset(FACT_TOOLS)
    max_tools: int = 40
    max_reason: int = 180
    show_reasoning: bool = True
    show_plan: bool = True
    item_noun: str = "variables"     # what the input panel counts ("sources", "claims", ...)

    def icon(self, name, kind=""):
        if not self.icons:
            return ""
        low = (str(name) + " " + kind).lower()
        for key, ico in self.icon_for.items():
            if key in low:
                return ico + " "
        return "\U0001f916 "                                    # generic agent

    def role(self, target):
        if target in self.roles:
            return self.roles[target]
        low = str(target).lower()
        return "adjudicate" if "verif" in low else "work on"


DEFAULT_STYLE = Style()


def _short(s, n=60):
    s = str(s).replace("\n", " ").strip()
    return s if len(s) <= n else s[:n] + "…"


class FlowRecorder(BaseCallbackHandler):
    """Records an ORDERED event stream of the run: plan (write_todos), delegations (task), and analysis
    tool calls with their outputs. Phases are segmented by `task` delegations — the tools a subagent
    runs land in the phase opened by the delegation that spawned it, which matches the observed serial
    coordinator -> worker -> verifier flow without fragile run-id tree reconstruction."""

    def __init__(self):
        self.events: list[dict] = []          # ordered: {type, ...}
        self._pending: dict = {}              # run_id -> event awaiting its tool output

    # -- LangChain callback hooks --------------------------------------------------------------------
    def on_tool_start(self, serialized, input_str, *, run_id=None, parent_run_id=None, **kw):  # noqa: D401
        name = (serialized or {}).get("name") or kw.get("name") or "tool"
        args = self._parse(input_str)
        if name == _PLAN_TOOL:
            self.events.append({"type": "plan", "todos": self._todos(args)})
        elif name == _DELEGATE_TOOL:
            # a delegation: record the assignment AND (via _pending) the subagent's returned conclusion
            _full = args.get("description", "") or args.get("_raw", "")
            ev = {"type": "delegate", "target": self._target(args),
                  "desc": _short(_full, 110), "vids": _span(_full),
                  "result": "", "types": {}}
            self.events.append(ev)
            if run_id is not None:
                self._pending[run_id] = ev
        else:
            ev = {"type": "tool", "name": name, "input": self._tool_in(args),
                  "input_full": _short(json.dumps(args, default=str), 120), "output": ""}
            self.events.append(ev)
            if run_id is not None:
                self._pending[run_id] = ev

    def on_tool_end(self, output, *, run_id=None, **kw):
        ev = self._pending.pop(run_id, None)
        if ev is None:
            return
        text = self._as_text(output)
        if ev["type"] == "delegate":                       # subagent's returned findings + parsed types
            ev["result"] = _short(text, 200)
            ev["types"] = _final_types(text)
        else:
            # Oracle returns are one verbose record PER VARIABLE (each carries a prose `claim` and
            # `reason`), so a 600-char cap kept only the first and the figure then reported "certified
            # 1" for a call that certified six. Keep the whole payload for those; it is parsed down to
            # `vid=ctype` pairs before display anyway.
            cap = 6000 if ev.get("name") in _ORACLE_TOOL_NAMES else 600
            ev["output"] = _short(text, cap)

    def on_llm_end(self, response, *, run_id=None, **kw):
        """Capture the model's REASONING text (the assistant message content between tool calls) so the
        figure/report can show WHY an agent did what it did, not just the tool mechanics."""
        try:
            gens = getattr(response, "generations", None) or []
            for batch in gens:
                for g in batch:
                    msg = getattr(g, "message", None)
                    txt = (getattr(msg, "content", None) if msg is not None else getattr(g, "text", "")) or ""
                    txt = txt if isinstance(txt, str) else ""
                    # strip gemma channel/thinking markers (<|channel>..<channel|>, <|..|>) + labels
                    txt = re.sub(r"<\|?channel\|?>.*?<\|?/?channel\|?>", "", txt, flags=re.S)
                    txt = re.sub(r"<\|?[^>]*\|?>", "", txt)
                    txt = re.sub(r"(?im)^\s*(thought|analysis|final)\s*$", "", txt).strip()
                    if len(txt) >= 20:                     # skip empty / pure tool-call / marker-only turns
                        self.events.append({"type": "reason", "text": _short(txt, 200)})
        except Exception:  # noqa: BLE001
            pass

    # -- manual recording API ------------------------------------------------------------------------
    # Callbacks are the easy path when you control `invoke`/`astream`. These three let ANY driver feed
    # the recorder: a framework without callbacks, a post-hoc replay of a transcript you already
    # collected, or a test. They append the same events the callbacks do, so every view works the same.
    def record_delegation(self, target, brief="", result=""):
        """One sub-agent hand-off: who it went to, the brief, and what came back."""
        ev = {"type": "delegate", "target": str(target or "agent"), "desc": _short(brief, 110),
              "vids": _span(brief), "result": _short(result, 200), "types": _final_types(result)}
        self.events.append(ev)
        return ev

    def record_tool_call(self, name, args=None, result=""):
        """One tool call and the result it returned."""
        args = args if isinstance(args, dict) else ({} if args is None else {"_raw": str(args)})
        cap = 6000 if str(name) in _ORACLE_TOOL_NAMES else 600
        ev = {"type": "tool", "name": str(name), "input": self._tool_in(args),
              "input_full": _short(json.dumps(args, default=str), 120),
              "output": _short(self._as_text(result), cap)}
        self.events.append(ev)
        return ev

    def record_reasoning(self, text):
        """One block of model reasoning between tool calls. Short/empty text is ignored."""
        t = re.sub(r"<\|?[^>]*\|?>", "", str(text or "")).strip()
        if len(t) >= 20:
            self.events.append({"type": "reason", "text": _short(t, 200)})

    @classmethod
    def from_messages(cls, messages, delegate_tools=(_DELEGATE_TOOL,)):
        """Build a recorder from a FINISHED LangChain message list, with no callback wiring.

        Use this when the driver streams updates instead of taking callbacks, or when you only have
        the transcript after the fact. Understands the standard shapes: an assistant message carrying
        `.tool_calls`, and a tool message carrying `.tool_call_id` / `.name` / `.content`. Plain dicts
        with the same keys work too.

            rec = FlowRecorder.from_messages(result["messages"])
            emit(rec, "out/run", answer=result["messages"][-1].content)
        """
        rec = cls()
        pending = {}                                   # tool_call_id -> (name, args)
        for m in messages or []:
            get = (lambda k, d=None: m.get(k, d)) if isinstance(m, dict) else \
                  (lambda k, d=None: getattr(m, k, d))
            content = get("content", "") or ""
            tcs = get("tool_calls", None) or []
            tcid = get("tool_call_id", None)
            if tcid is not None:                        # a tool RESULT
                name, args = pending.pop(tcid, (get("name", "tool"), {}))
                if str(name) in delegate_tools:
                    rec.record_delegation(args.get("subagent_type") or args.get("target") or "agent",
                                          args.get("description") or args.get("brief") or "", content)
                else:
                    rec.record_tool_call(name, args, content)
                continue
            if isinstance(content, str) and content.strip():
                rec.record_reasoning(content)
            for tc in tcs:                              # remember the call until its result arrives
                g = (lambda k: tc.get(k)) if isinstance(tc, dict) else (lambda k: getattr(tc, k, None))
                cid, nm, ar = g("id"), g("name"), g("args") or {}
                if cid is not None:
                    pending[cid] = (nm, ar if isinstance(ar, dict) else {})
                elif str(nm) in delegate_tools:          # no id to correlate: record the hand-off now
                    rec.record_delegation((ar or {}).get("subagent_type", "agent"),
                                          (ar or {}).get("description", ""), "")
                else:
                    rec.record_tool_call(nm, ar, "")
        return rec

    # -- helpers -------------------------------------------------------------------------------------
    @staticmethod
    def _parse(input_str):
        if isinstance(input_str, dict):
            return input_str
        s = str(input_str)
        try:
            return json.loads(s)
        except Exception:  # noqa: BLE001
            pass
        try:  # langchain often hands the args as a Python-repr dict (single quotes)
            import ast
            v = ast.literal_eval(s)
            if isinstance(v, dict):
                return v
        except Exception:  # noqa: BLE001
            pass
        return {"_raw": s}

    @staticmethod
    def _as_text(output):
        if hasattr(output, "content"):
            output = output.content
        o = output
        if isinstance(o, str):
            import ast
            for loader in (json.loads, ast.literal_eval):
                try:
                    o = loader(output)
                    break
                except Exception:  # noqa: BLE001
                    continue
        # unwrap the MCP envelope: {"type":"tool","data":{"content":[{"text":..}]}} OR a [{"text":..}] list
        try:
            content = o.get("data", {}).get("content") if isinstance(o, dict) else o
            if isinstance(content, list) and content and isinstance(content[0], dict):
                # JOIN every content part, not just the first. A tool returning a LIST (the oracles
                # return one record per certified variable) arrives as one MCP content item per
                # element, so `content[0]` silently kept a single fact -- the figure then reported
                # "certified 1" for a call that had certified six.
                return "".join(str(c.get("text", "")) for c in content
                               if isinstance(c, dict)).strip()
        except Exception:  # noqa: BLE001
            pass
        return json.dumps(o)[:120] if isinstance(o, (dict, list)) else str(o).strip()

    @staticmethod
    def _todos(args):
        todos = args.get("todos") or []
        out = []
        for t in todos:
            c = t.get("content") if isinstance(t, dict) else str(t)
            if c:
                out.append(_short(c, 200))     # keep the full plan step (was 55 -> truncated)
        return out

    @staticmethod
    def _target(args):
        # deepagents' task tool carries the chosen subagent under a few possible keys
        for k in ("subagent_type", "subagent", "agent", "name"):
            v = args.get(k)
            if v:
                return str(v)
        blob = (str(args.get("description", "")) + " " + str(args.get("_raw", ""))).lower()
        if "verifier" in blob or "adjudicat" in blob:
            return "verifier"
        return "type_worker"

    @staticmethod
    def _tool_in(args):
        for k in ("offset", "addr", "claim", "n_instructions"):
            if k in args:
                return f"{k}={_short(args[k], 24)}"
        return _short(next(iter(args.values()), ""), 24) if args else ""


def summarize_output(name, text):
    """Turn a raw tool result into a short, HUMAN-READABLE summary (the meaningful fact), instead of a
    blind character-truncation. e.g. a `disassemble` result becomes 'N instrs; calls a, b, …' and a
    `decompile` result becomes its C signature — so the figure/log reads clearly."""
    t = str(text or "").strip()
    if not t:
        return ""
    if name == "decompile":
        for line in t.splitlines():
            line = line.strip()
            if line and "(" in line and ")" in line and not line.startswith(("{", "//")):
                return "signature: " + _short(line, 80)         # the C prototype is the useful part
        return _short(t, 70)
    if name == "disassemble":
        n = re.search(r"instructions \d+-\d+ of (\d+)", t)
        calls = re.search(r"CALLS:\s*([^\n]+)", t)
        parts = []
        if n:
            parts.append(f"{n.group(1)} instructions")
        if calls:
            cs = [c.strip() for c in calls.group(1).split(",")][:4]
            parts.append("calls " + ", ".join(cs) + ("…" if calls.group(1).count(",") >= 4 else ""))
        return "; ".join(parts) or _short(t, 70)
    if name == "stack_var":
        off = re.search(r'"query_offset":\s*"([^"]+)"', t)
        rbp = re.search(r'"rbp_offset":\s*"([^"]+)"', t)
        found = re.search(r'"found":\s*(true|false)', t)
        parts = []
        if off:
            parts.append(f"slot {off.group(1)}")
        if rbp:
            parts.append(f"= rbp{rbp.group(1)}")
        if found:
            parts.append("found" if found.group(1) == "true" else "NOT found")
        return ", ".join(parts) or _short(t, 70)
    if name == "xrefs_to":
        return f"{t.count('0x')} xref(s)"
    if name == "read_values":
        return _short(t, 70)
    return _short(t, 70)


# ---- Mermaid emission ------------------------------------------------------------------------------
def _phases(events):
    """Segment the event stream into phases: an initial coordinator plan, then one phase per delegation
    carrying the tools, the model reasoning, and the subagent's returned types that followed it."""
    plan_todos, coord_reasons, phases, cur = [], [], [], None
    for ev in events:
        t = ev["type"]
        if t == "plan":
            plan_todos = ev["todos"] or plan_todos
        elif t == "delegate":
            cur = {"target": ev["target"], "desc": ev["desc"], "vids": ev.get("vids", ""),
                   "tools": [], "reasons": [], "ev": ev}
            phases.append(cur)
        elif t == "tool":
            if cur is None:
                cur = {"target": None, "desc": "", "tools": [], "reasons": [], "ev": None}
                phases.append(cur)
            cur["tools"].append(ev)
        elif t == "reason":
            (cur["reasons"] if cur is not None else coord_reasons).append(ev["text"])
    # The declared plan is gone: the coordinator no longer calls `write_todos`, because a tool that is
    # not offered cannot be narrated as prose -- the failure that ended a run before any subagent
    # executed. Rather than lose the plan row, synthesize it from the delegations that ACTUALLY
    # happened. This is strictly more faithful than the old row, which showed what the model said it
    # would do; this shows what it did.
    if not plan_todos and phases:
        for p in phases:
            span, who = p.get("vids") or "", p["target"]
            if who is None:
                plan_todos.append(f"analyze {span} directly" if span else "analyze directly")
            elif who == "verifier":
                plan_todos.append(f"adjudicate {span} with the verifier" if span
                                  else "adjudicate all findings with the verifier")
            else:
                plan_todos.append(f"delegate {span} to {who}" if span else f"delegate to {who}")
        plan_todos.append("synthesize the final answer")
    return plan_todos, coord_reasons, phases


def _span(text, pattern=r"V\d+") -> str:
    """"V1-V6, V9" from any text mentioning variable ids.

    Extracted from the delegation's FULL description at record time, because the stored `desc` is
    truncated for display and the variable list is the part that gets cut."""
    if not pattern:
        return ""
    ids = re.findall(r"\b(?:%s)\b" % pattern, str(text or ""))
    if not ids:
        return ""
    pre = re.match(r"^\D*", ids[0]).group(0)                 # shared prefix, e.g. "V"
    try:
        ns = sorted({int(re.sub(r"\D", "", i)) for i in ids})
    except ValueError:
        return ", ".join(dict.fromkeys(ids))[:60]
    out, i = [], 0
    while i < len(ns):
        j = i
        while j + 1 < len(ns) and ns[j + 1] == ns[j] + 1:
            j += 1
        out.append(f"{pre}{ns[i]}" if i == j else f"{pre}{ns[i]}-{pre}{ns[j]}")
        i = j + 1
    return ", ".join(out)


_vid_span = _span   # backwards-compatible alias


def _plan_tag(todo, style=None):
    """Classify a coordinator plan step by who executes it: a delegation (spawns a traced sub-agent) or
    a coordinator-internal step (grouping / synthesis — no sub-agent, nothing to trace)."""
    st = style or DEFAULT_STYLE
    t = str(todo).lower()
    for name in list(st.roles) + ["verifier", "type_worker", "worker"]:
        if str(name).lower() in t:
            return f"→ {name}{st.agent_suffix}"
    if "delegate" in t or "recover" in t:
        return f"→ sub{st.agent_suffix}"
    return f"{st.root.lower()} (internal)"


def _phase_types(ph):
    """The types a subagent RETURNED for its task. Prefer the captured task-tool output; fall back to the
    subagent's last reasoning turn (which IS its final conclusion) since deepagents' `task` tool does not
    always surface its return through on_tool_end."""
    ev = ph.get("ev")
    if ev and ev.get("types"):
        return ev["types"]
    for r in reversed(ph.get("reasons", [])):
        t = _final_types(r)
        if t:
            return t
    return {}


def _norm_ty(s):
    """Loose type-normalisation for pred-vs-GT matching: collapse whitespace/case and treat pointer
    spelling uniformly, so 'char *' == 'char*' and 'FILE *' == 'file *'."""
    return re.sub(r"\s+", "", str(s).lower()).replace("const", "")


def _match(pred, gt):
    """✓ exact (normalised), ~ same pointer-ness / integer-family (partial), ✗ otherwise."""
    if not gt:
        return "?"
    p, g = _norm_ty(pred), _norm_ty(gt)
    if p == g:
        return "✓"
    if ("*" in p) == ("*" in g) and ("*" in p or _int_fam(p) == _int_fam(g)):
        return "~"
    return "✗"


def _int_fam(t):
    return bool(re.search(r"(int|long|size_t|idx_t|ssize|char|short|uint|ulong|_bool|byte)", t)) and "*" not in t


def _seq_esc(s):
    """Escape text for a Mermaid sequence message: no newlines, no ; or : that break parsing."""
    s = str(s).replace("\n", " ").replace(";", ",").replace(":", "-")
    s = s.replace('"', "'").replace("[", "(").replace("]", ")").replace("{", "(").replace("}", ")")
    s = s.replace("#", "").replace("<", "").replace(">", "")
    return re.sub(r"\s+", " ", s).strip()


def _oracle_result(name, out, style=None):
    """Render an oracle tool's return as the FACTS it certified, one per variable.

    The generic summariser truncates to a prefix, which for an oracle shows the first record and hides
    the rest -- the useful content is exactly which entities were certified as what."""
    if name not in ((style or DEFAULT_STYLE).fact_tools):
        return summarize_output(name, out)
    facts = re.findall(r"['\"]vid['\"]\s*:\s*['\"](V\d+)['\"].{0,120}?['\"]ctype['\"]\s*:\s*['\"]([^'\"]+)['\"]",
                       str(out), re.S)
    if not facts:
        return "no certification — all oracles abstained"
    shown = "; ".join(f"{v}={t}" for v, t in facts[:8])
    return f"certified {len(facts)}: {shown}" + (" …" if len(facts) > 8 else "")


def _participants(phases, style):
    """Discover the lifelines from the run itself: the root, one per distinct delegation target in
    the order they first appear, then tools. Returns (ids, declaration_lines)."""
    ids = {"__root__": "C", "__tools__": "T", "__facts__": "O"}
    decls = [f"  participant C as {style.icon(style.root, 'coordinator')}{style.root}"]
    seen = []
    for ph in phases:
        t = ph.get("target")
        if t and t not in seen:
            seen.append(t)
    for k, t in enumerate(seen):
        pid = f"A{k}"
        ids[t] = pid
        decls.append(f"  participant {pid} as {style.icon(t)}{t}{style.agent_suffix}")
    decls.append(f"  participant T as {style.icon(style.tools, 'tool')}{style.tools}")
    return ids, decls


def to_sequence(recorder, meta, oracle_facts, answer, scoring=None, max_tools_per_phase=None,
                style=None):
    """A Mermaid SEQUENCE diagram of the complete run, turn by turn: every delegation, every reasoning
    turn, every tool call and the result it returned, what each sub-agent concluded, any deterministic
    facts applied afterwards, and the final answer.

    Participants are discovered from the run, so any set of sub-agent names works. Pass a `Style` to
    change labels, icons, verbs, caps, or the entity-id pattern."""
    st = style or DEFAULT_STYLE
    cap = max_tools_per_phase or st.max_tools
    plan_todos, coord_reasons, phases = _phases(recorder.events)
    ids, decls = _participants(phases, st)
    L = ["```mermaid", "sequenceDiagram", "  autonumber"] + decls
    # The facts lifeline models a deterministic POST-PASS. When the agent fetches the facts itself they
    # are ordinary tool calls, already drawn on the tools lifeline, so no separate actor is added.
    by_code = meta.get("certified_by_code", True)
    if by_code:
        L.append(f"  participant O as {st.icon(st.facts, 'fact')}{st.facts}")
    if st.show_plan:
        for k, t in enumerate(plan_todos, 1):
            L.append(f"  Note over C: \U0001f4dd plan {k}. [{_plan_tag(t, st)}] {_seq_esc(t)}")
    if st.show_reasoning:
        for r in coord_reasons[:1]:
            L.append(f"  Note over C: \U0001f4ad {_seq_esc(r[:70])}")

    for i, ph in enumerate(phases):
        target = ph.get("target")
        actor = ids.get(target, "C") if target else "C"
        if target:                                   # a real hand-off; a root-run phase has none
            assigned = _span(ph["desc"], st.entity_re) or _short(ph["desc"], 48)
            L.append(f"  C->>{actor}: task {i + 1} — {st.role(target)} {_seq_esc(assigned)}".rstrip())
        shown = ph["tools"][:cap]
        for t in shown:
            L.append(f"  {actor}->>T: {_seq_esc(t['name'])}({_seq_esc(t['input'])})")
            if t.get("output"):
                L.append(f"  T-->>{actor}: {_seq_esc(_oracle_result(t['name'], t['output'], st))}")
        if len(ph["tools"]) > len(shown):
            L.append(f"  Note over {actor}: … +{len(ph['tools']) - len(shown)} more tool calls")
        # WHY: the reasoning behind this phase's conclusion, shown just before its result arrow. Models
        # with thinking disabled emit none -- fall back to the evidence the phase actually inspected.
        if st.show_reasoning:
            genuine = [x for x in ph["reasons"] if not _final_types(x, st.entity_re)]
            if genuine:
                L.append(f"  Note over {actor}: \U0001f4ad reasoning: "
                         f"{_seq_esc(genuine[-1][:st.max_reason])}")
            elif ph["tools"]:
                _c = {}
                for t in ph["tools"]:
                    _c[t["name"]] = _c.get(t["name"], 0) + 1
                ev = ", ".join(f"{n}×{k}" for k, n in _c.items())
                L.append(f"  Note over {actor}: \U0001f4ad reasoning: inferred from the evidence it "
                         f"gathered — {_seq_esc(ev)}")
        types = _phase_types(ph)
        if types and target:
            tt = ", ".join(f"{k}-{_seq_esc(v)}" for k, v in list(types.items())[:10])
            L.append(f"  {actor}-->>C: \u2705 result: {tt}")

    consulted = meta.get("oracles_consulted", [])
    fired = {v[1] for v in oracle_facts.values() if isinstance(v, (list, tuple))} if oracle_facts else set()
    if by_code and (consulted or oracle_facts):
        L.append(f"  C->>O: run {len(consulted)} deterministic checks ({_seq_esc(', '.join(consulted))})")
        for vid, val in sorted(oracle_facts.items()):
            ctype, oracle, floor = (val if isinstance(val, (list, tuple)) and len(val) == 3
                                    else (val, "?", False))
            L.append(f"  O-->>C: ✓ {vid}- {_seq_esc(ctype)} via {_seq_esc(oracle)}"
                     + (" (floor)" if floor else ""))
        for o in consulted:                                     # make abstaining producers explicit
            if o not in fired:
                L.append(f"  Note over O: {_seq_esc(o)} — consulted, abstained")
    # final result as the LAST arrow: the root emits the synthesized answer.
    ans = _final_types(answer, st.entity_re)
    if ans:
        score = (scoring or {}).get("score")
        stxt = f" · score {score:.2f}%" if score is not None else ""
        tail = ", ".join(f"{k}-{_seq_esc(v)}" for k, v in sorted(ans.items(), key=lambda kv: int(re.sub(r'\D', '', kv[0]) or 0)))
        ncert = len([1 for v in oracle_facts.values() if isinstance(v, (list, tuple))]) if oracle_facts else 0
        if ncert:
            _src = ("applied by code (authoritative)" if by_code else "fetched by the agent itself")
            L.append(f"  Note over C: \U0001f4ad reasoning: synthesized from the adjudicated results,"
                     f" with {ncert} {_src}")
        L.append(f"  C->>C: \U0001f4cb FINAL ANSWER{stxt}: {tail}")
    L.append("```")
    return "\n".join(L)


def _final_types(answer, pattern=r"V\d+"):
    """The FINAL per-variable types exactly as the scorer sees them: the model's synthesized map, then
    the deterministic ORACLE-CERTIFIED block applied as an authoritative override. Mirrors run_trex_one's
    parsing so the diagram's Output matches the scored answer (the oracle block overrides the last JSON,
    which is the model's PRE-oracle synthesis)."""
    answer = answer or ""
    # base map: prefer the last well-formed JSON object; else the body "V: type" lines
    out = {}
    for j in reversed(re.findall(r"\{[^{}]*\}", answer)):
        try:
            o = json.loads(j)
            if o and all(isinstance(v, str) for v in o.values()):
                out = dict(o)
                break
        except Exception:  # noqa: BLE001
            pass
    if not out:
        for m in re.finditer(r"(?mi)^\s*-?\s*(%s)\s*:\s*(.+?)\s*$" % (pattern or r"V\d+"), answer):
            out[m.group(1)] = m.group(2).strip()
    # ORACLE-CERTIFIED block: authoritative override (same regex the scorer uses)
    om = re.search(r"ORACLE-CERTIFIED[^\n]*\n((?:\s*[-*]\s*V?\d+\s*[:=][^\n]*\n?)+)", answer)
    if om:
        for m in re.finditer(r"(?mi)^\s*[-*]\s*(V\d+)\s*[:=]\s*(.+?)\s*$", om.group(1)):
            out[m.group(1)] = m.group(2).strip()
    return out


def _load_font(size, bold=False):
    import glob
    from PIL import ImageFont
    pats = [f"/usr/share/fonts/**/DejaVuSans{'-Bold' if bold else ''}.ttf",
            f"/usr/share/fonts/**/*DejaVuSans{'-Bold' if bold else ''}*.ttf"]
    for pat in pats:
        for p in glob.glob(pat, recursive=True):
            try:
                return ImageFont.truetype(p, size)
            except Exception:  # noqa: BLE001
                pass
    return ImageFont.load_default()


def compose_sequence_figure(seq_png, meta, answer, scoring, out_path, style=None):
    """Stack ONE figure = [Input text panel] on top of [the sequence-diagram image] on top of [Output
    text panel with the final answer + mean score]. Keeps input/output as clean TEXT (not sequence notes)
    while still giving a single self-contained image. Best-effort; returns out_path or None."""
    try:
        from PIL import Image, ImageDraw
    except Exception:  # noqa: BLE001
        return None
    seq = Image.open(seq_png).convert("RGB")
    W = max(seq.width, 900)
    title_f, body_f = _load_font(30, bold=True), _load_font(22)

    _title = meta.get("title") or (f"function @{meta.get('vaddr', '?')}" if meta.get("vaddr") else "run")
    _n = meta.get("nvars") or len(meta.get("variables") or [])
    _noun = (style or DEFAULT_STYLE).item_noun
    in_lines = [(f"🎯 INPUT — {_title}" + (f"  ({_n} {_noun})" if _n else ""), title_f)]
    for row in meta.get("variables", []):
        vid, loc, sz = (list(row) + ["", ""])[:3]
        in_lines.append((f"    {vid}    {loc}" + (f"    {sz} bytes" if sz != "" else ""), body_f))

    ans = _final_types(answer, (style or DEFAULT_STYLE).entity_re)
    gt = (scoring or {}).get("ground_truth") or {}
    score = (scoring or {}).get("score")
    _vk = lambda k: int(re.sub(r"\D", "", k) or 0)  # noqa: E731
    # Per-variable scores from the scorer's own finer-grained output, as in the flowchart and the
    # markdown: the tick/tilde marker is a STRING comparison and disagrees with the metric in the
    # title (the scorer resolves typedefs, and grades partial credit on a scale whose maximum is
    # type-dependent -- 6 for a scalar, 9 for a pointer).
    per = (scoring or {}).get("per_var") or {}
    otitle = "📋 OUTPUT — final answer" + (" vs ground truth" if gt else "") + (f"    ·    mean score: {score:.2f}%" if score is not None else "")
    if per:
        otitle += f"    ({sum(p['score'] for p in per.values())}/{sum(p['max'] for p in per.values())} points)"
    out_lines = [(otitle, title_f)]
    for vid in sorted(ans, key=_vk):
        p = per.get(vid)
        mark = (f"{p['score']}/{p['max']}" + (f"  ({p['halt']})" if p.get("halt") else "")) if p \
            else _match(ans[vid], gt.get(vid))
        line = f"    {vid}: {ans[vid]}" + (f"    vs GT {gt.get(vid, '?')}    {mark}" if gt else "")
        out_lines.append((line, body_f))

    def panel(lines, bg):
        lh, pad = 34, 24
        h = pad * 2 + lh * len(lines)
        img = Image.new("RGB", (W, h), bg)
        d = ImageDraw.Draw(img)
        y = pad
        for text, f in lines:
            d.text((pad, y), text, fill="#111111", font=f)
            y += lh
        d.line([(0, 0), (W, 0)], fill="#cccccc", width=2)
        return img

    top, bot = panel(in_lines, "#dbeafe"), panel(out_lines, "#dbeafe")
    seqc = seq if seq.width == W else Image.new("RGB", (W, seq.height), "white")
    if seqc is not seq:
        seqc.paste(seq, ((W - seq.width) // 2, 0))
    total = Image.new("RGB", (W, top.height + seqc.height + bot.height), "white")
    total.paste(top, (0, 0))
    total.paste(seqc, (0, top.height))
    total.paste(bot, (0, top.height + seqc.height))
    total.save(out_path)
    return out_path


def render(mmd_block, out_base):
    """Write `<out_base>.mmd` (mermaid source, deps-free) and render HIGH-DEFINITION outputs via the
    Mermaid CLI: a vector `.svg` (infinitely crisp) and a high-scale `.png`. Scale/width configurable via
    AGENTIC_FLOW_SCALE (default 3) / AGENTIC_FLOW_WIDTH (default 1600). Returns (mmd_path, png_or_svg_path
    or None). `mmd_block` may include the ``` fences (stripped for the raw .mmd file)."""
    raw = re.sub(r"^```mermaid\n|\n```$", "", mmd_block.strip())
    mmd_path = f"{out_base}.mmd"
    with open(mmd_path, "w") as fh:
        fh.write(raw + "\n")
    scale = os.environ.get("AGENTIC_FLOW_SCALE", "3")
    width = os.environ.get("AGENTIC_FLOW_WIDTH", "1600")
    # Chromium (which mermaid-cli drives via puppeteer) refuses to launch as root / in a sandboxed CI
    # without --no-sandbox; write a puppeteer config so rendering works headless.
    pcfg = f"{out_base}.puppeteer.json"
    try:
        with open(pcfg, "w") as fh:
            json.dump({"args": ["--no-sandbox", "--disable-setuid-sandbox"]}, fh)
    except Exception:  # noqa: BLE001
        pcfg = None
    base_cmd = None
    if shutil.which("mmdc"):
        base_cmd = ["mmdc"]
    elif shutil.which("npx"):
        base_cmd = ["npx", "-y", "@mermaid-js/mermaid-cli"]
    produced = None
    if base_cmd:
        # SVG first (true HD, vector) then a high-scale PNG; return the PNG when present else the SVG.
        for ext, extra in (("svg", []), ("png", ["-s", scale, "-w", width])):
            out = f"{out_base}.{ext}"
            cmd = base_cmd + ["-i", mmd_path, "-o", out, "-b", "white"] + extra
            if pcfg:
                cmd += ["-p", pcfg]
            try:
                subprocess.run(cmd, check=True, capture_output=True, timeout=240)
                if os.path.exists(out):
                    produced = out if ext == "png" else (produced or out)
            except Exception:  # noqa: BLE001  # renderer missing/offline -> .mmd still written
                pass
    if produced:
        return mmd_path, produced
    return mmd_path, None


# =====================================================================================================
#  Public API. Everything above is machinery; these three names are what a caller needs.
# =====================================================================================================

# Last emitted run, so `rescore` can redraw with an overlay computed after the run finished (a score
# is usually only known once something downstream has graded the answer).
_LAST: dict = {}

def emit(recorder, out_base, *, title=None, inventory=None, answer="", facts=None,
         consulted=(), applied_in_code=False, scoring=None, quiet=False, style=None):
    """Draw the run and write `<out_base>_turns.{mmd,svg,png}`. Returns the best path written.

    recorder        a FlowRecorder that was attached to the run
    out_base        path prefix; the sequence view writes `<out_base>_turns.{mmd,svg,png}`
    title           free text for the input panel (e.g. "cut/cut_fields @0x102f27")
    inventory       [(id, location, size)] rows for the input panel; optional
    answer          the run's final text, parsed for `id: value` lines to fill the output panel
    facts           {id: (value, source, mode)} deterministic facts to draw as a separate lifeline
    consulted       names of fact producers that ran, so the ones that abstained can be shown
    applied_in_code True when a post-pass applied `facts`; False when the agent consumed them itself,
                    in which case they are already ordinary tool calls and no extra lifeline is drawn
    scoring         {"score": float, "ground_truth": {...}, "per_var": {...}} overlay; optional
    style           a `Style` controlling labels, icons, verbs, caps and the entity-id pattern
    """
    facts = facts or {}
    inventory = list(inventory or [])
    meta = {"title": title, "vaddr": title or "", "nvars": len(inventory),
            "variables": inventory, "oracles_consulted": list(consulted),
            "certified_by_code": bool(applied_in_code)}
    _LAST.clear()
    _LAST.update({"recorder": recorder, "meta": meta, "facts": facts, "answer": answer,
                  "base": out_base, "quiet": quiet, "style": style or DEFAULT_STYLE})
    return _render(scoring)


def rescore(score=None, ground_truth=None, per_var=None):
    """Redraw the last emitted run with a result overlay. No-op if nothing was emitted."""
    if not _LAST:
        return None
    try:
        return _render({"score": score, "ground_truth": ground_truth or {},
                        "per_var": per_var or {}})
    except Exception as e:  # noqa: BLE001  an overlay must never break the caller
        print(f"[flow] overlay skipped — {str(e)[:120]}")
        return None


def _render(scoring=None):
    """Draw the sequence view from `_LAST`. Best-effort: never raises into the caller."""
    F = _LAST
    if not F:
        return None
    rec, meta, facts, answer, base = (F["recorder"], F["meta"], F["facts"], F["answer"], F["base"])
    out = None
    try:
        _, img = render(to_sequence(rec, meta, facts, answer, scoring, style=F.get("style")),
                        base + "_turns")
        if img and img.endswith(".png"):
            out = compose_sequence_figure(img, meta, answer, scoring, base + "_turns.png",
                                          F.get("style")) or img
        else:
            out = img or (base + "_turns.mmd")
    except Exception as e:  # noqa: BLE001
        print(f"[flow] render failed — {str(e)[:140]}")
    if out and not F.get("quiet"):
        print(f"[flow] {out}" + ("  (+ overlay)" if scoring else ""))
    return out
