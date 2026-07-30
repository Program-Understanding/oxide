"""Optional run-flow recorder + Mermaid diagram for the deepagents type-recovery pipeline.

Enabled per-run via AGENTIC_FLOW_DIAGRAM=1 (or the `flow_diagram` opt / config). It attaches a LangChain
callback handler to the agent run that records the ACTUAL flow — the coordinator's task decomposition,
each subagent delegation, the tools each phase called (with results), the verifier's adjudication, and
the deterministic oracle certification — then emits a Mermaid flowchart so a human can SEE what the
multi-agent system did behind the scenes and judge whether it is correct.

Self-contained: writing the `.mmd` needs no dependency (view it in any Mermaid viewer). If the Mermaid
CLI is reachable (`mmdc`, or `npx @mermaid-js/mermaid-cli`) a PNG is rendered too. Everything here is a
no-op unless the flag is set, so importing it costs nothing.
"""
from __future__ import annotations

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
# deterministic oracles, exposed as ordinary tools
_ORACLE_TOOL_NAMES = {"static_type_oracles", "callee_signature", "decompiler_pointer",
                      "spilled_param", "interprocedural_param_usage"}


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
                  "desc": _short(_full, 110), "vids": _vid_span(_full),
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
    if name in ("read_values", "compute"):
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
                cur = {"target": "type_worker", "desc": "", "tools": [], "reasons": [], "ev": None}
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
            if who == "verifier":
                plan_todos.append(f"adjudicate {span} with the verifier" if span
                                  else "adjudicate all findings with the verifier")
            else:
                plan_todos.append(f"delegate {span} to {who}" if span else f"delegate to {who}")
        plan_todos.append("synthesize the final answer")
    return plan_todos, coord_reasons, phases


def input_vars_from_question(question):
    """Parse the `<Vid> <register 0x..|stack -0x..> <size>` variable lines out of a type-recovery
    question, returning [(vid, location, size_bytes)] for the diagram's Input node."""
    out = []
    for m in re.finditer(r"(?m)^\s*(V\d+)\s+((?:register|stack)\s+-?0x[0-9a-fA-F]+)\s+(\d+)\b", question or ""):
        out.append((m.group(1), m.group(2).strip(), m.group(3)))
    return out


def _vid_span(text) -> str:
    """"V1-V6, V9" from any text mentioning variable ids.

    Extracted from the delegation's FULL description at record time, because the stored `desc` is
    truncated for display and the variable list is the part that gets cut."""
    ns = sorted({int(m.group(1)) for m in re.finditer(r"\bV(\d+)\b", str(text or ""))})
    if not ns:
        return ""
    out, i = [], 0
    while i < len(ns):
        j = i
        while j + 1 < len(ns) and ns[j + 1] == ns[j] + 1:
            j += 1
        out.append(f"V{ns[i]}" if i == j else f"V{ns[i]}-V{ns[j]}")
        i = j + 1
    return ", ".join(out)


def _plan_tag(todo):
    """Classify a coordinator plan step by who executes it: a delegation (spawns a traced sub-agent) or
    a coordinator-internal step (grouping / synthesis — no sub-agent, nothing to trace)."""
    t = str(todo).lower()
    if "verif" in t:
        return "→ verifier agent"
    if "delegate" in t or "type_worker" in t or "worker" in t or "recover" in t:
        return "→ type_worker agent"
    return "coordinator (internal)"


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


def _esc(s):
    return str(s).replace('"', "'").replace("[", "(").replace("]", ")").replace("{", "(").replace("}", ")")


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


def to_mermaid(recorder, meta, oracle_facts, answer, scoring=None):
    """Build a Mermaid flowchart of the run: input (function + variables) -> coordinator(plan) -> worker
    phases (tools) -> verifier (tools) -> deterministic oracle certification -> final answer (with
    ground-truth match + score when `scoring` is supplied by the harness)."""
    vaddr = meta.get("vaddr", "?")
    nvars = meta.get("nvars", "?")
    variables = meta.get("variables") or []
    plan_todos, coord_reasons, phases = _phases(recorder.events)

    L = ["```mermaid", "flowchart TD",
         "  classDef coord fill:#fef9c3,stroke:#ca8a04,color:#000;",
         "  classDef worker fill:#dcfce7,stroke:#16a34a,color:#000;",
         "  classDef verifier fill:#ffedd5,stroke:#ea580c,color:#000;",
         "  classDef oracle fill:#fee2e2,stroke:#dc2626,color:#000;",
         "  classDef io fill:#dbeafe,stroke:#2563eb,color:#000;",
         ""]
    vlines = "<br/>".join(f"{vid}  {_esc(loc)}  {sz}B" for vid, loc, sz in variables[:18])
    vlines += "<br/>…" if len(variables) > 18 else ""
    in_body = (f"🎯 <b>Input</b> — function @{vaddr}<br/>{nvars} variables (location, bytes)<br/>{vlines}"
               if variables else f"🎯 <b>Input</b> — function @{vaddr}<br/>{nvars} variables")
    L.append(f'  IN["{in_body}"]:::io')

    # coordinator plan
    plan_txt = "<br/>".join(f"• {_esc(t)}  <b>[{_plan_tag(t)}]</b>" for t in plan_todos) or "plan &amp; delegate"
    L.append(f'  COORD["🧭 Coordinator agent — decompose &amp; delegate<br/>{plan_txt}"]:::coord')
    L.append("  IN --> COORD")

    # worker + verifier phases — each shows assigned vars, ALL tool calls (input→result), the model's
    # reasoning, and the types the subagent concluded/adjudicated (the intermediate result).
    worker_ids, verifier_ids = [], []
    for i, ph in enumerate(phases):
        tools = ph["tools"]
        counts = {}
        for t in tools:
            counts[t["name"]] = counts.get(t["name"], 0) + 1
        tsum = ", ".join(f"{n}×{c}" for n, c in counts.items()) or "(no tool calls)"
        is_ver = ph["target"] == "verifier"
        nid = f"{'VER' if is_ver else 'W'}{i}"
        assigned = " ".join(re.findall(r"\bV\d+\b", ph["desc"]))
        head = ("🔍 verifier agent · decompilation lens" if is_ver
                else f"⚙️ type_worker agent · {_esc(assigned) or f'group {i + 1}'}")
        body = f"{head}<br/><b>tools:</b> {_esc(tsum)}"
        for t in [x for x in tools if x.get("output")][:5]:      # up to 5 concrete input->summary lines
            body += f"<br/>· {_esc(t['name'])}({_esc(t['input'])}) → {_esc(summarize_output(t['name'], t['output']))}"
        # show only GENUINE prose reasoning — drop any turn that is just the type-list conclusion, since
        # that duplicates the '→ concluded/adjudicated' line below.
        _genuine = [r for r in ph["reasons"] if not _final_types(r)]
        if _genuine:
            body += f"<br/><i>💭 {_esc(_genuine[-1][:80])}</i>"
        types = _phase_types(ph)
        if types:
            tt = ", ".join(f"{k}:{_esc(v)}" for k, v in list(types.items())[:8])
            body += f"<br/><b>→ {'adjudicated' if is_ver else 'concluded'}:</b> {tt}"
        cls = "verifier" if is_ver else "worker"
        L.append(f'  {nid}["{body}"]:::{cls}')
        L.append(f"  COORD --> {nid}")
        (verifier_ids if is_ver else worker_ids).append(nid)

    # workers feed the verifier (if a verifier phase exists)
    for w in worker_ids:
        for v in verifier_ids:
            L.append(f"  {w} --> {v}")

    prev_layer = verifier_ids or worker_ids or ["COORD"]

    # deterministic oracle certification — list ALL consulted oracles (✓ fired vs · abstained), not just
    # the ones that produced a fact, so an abstaining oracle (e.g. runtime_type_probe) is visibly run.
    consulted = meta.get("oracles_consulted", [])
    fired = {v[1] for v in oracle_facts.values() if isinstance(v, (list, tuple))} if oracle_facts else set()
    if consulted or oracle_facts:
        cons = ", ".join(f"{_esc(o)}{'✓' if o in fired else '·abstain'}" for o in consulted)
        rows = [f"<b>oracles run:</b> {cons}"] if consulted else []
        for vid, val in sorted(oracle_facts.items()):
            ctype, oracle, floor = (val if isinstance(val, (list, tuple)) and len(val) == 3
                                    else (val, "?", False))
            rows.append(f"{vid}: {_esc(ctype)} — {_esc(oracle)}{' (floor)' if floor else ''}")
        if not oracle_facts:
            rows.append("<i>all consulted oracles abstained — nothing to certify</i>")
        ocert = "<br/>".join(rows[:12]) + ("<br/>…" if len(rows) > 12 else "")
        _applied = meta.get("certified_by_code", True)
        _title = ("✅ Deterministic oracle certification (run in code, not LLM)" if _applied else
                  "🔎 Oracles — consulted by the verifier as tools; NOT applied by code")
        L.append(f'  ORACLE["{_title}<br/>{ocert}"]:::oracle')
        for p in prev_layer:
            L.append(f"  {p} --> ORACLE")
        prev_layer = ["ORACLE"]

    # final answer — vs ground truth + score when the harness supplied scoring
    ans_map = _final_types(answer)
    gt = (scoring or {}).get("ground_truth") or {}
    score = (scoring or {}).get("score")
    _vk = lambda k: int(re.sub(r"\D", "", k) or 0)  # noqa: E731
    per = (scoring or {}).get("per_var") or {}
    if gt:
        rows = []
        for vid in sorted(ans_map, key=_vk):
            # The tick/tilde marker is a STRING comparison and disagrees with the metric in the
            # caption: the scorer resolves typedefs (`idx_t` == `long`) and grades partial credit on a
            # per-variable scale whose maximum is type-dependent (6 for a scalar, 9 for a pointer).
            p = per.get(vid)
            mark = (f"— <b>{p['score']}/{p['max']}</b>" + (f" {_esc(p['halt'])}" if p.get("halt") else "")) \
                if p else _match(ans_map[vid], gt.get(vid))
            rows.append(f"{vid}: {_esc(ans_map[vid])} vs {_esc(gt.get(vid, '?'))} {mark}")
        arows = "<br/>".join(rows[:18]) + ("<br/>…" if len(rows) > 18 else "")
        _tot = sum(p["score"] for p in per.values()) if per else None
        _mx = sum(p["max"] for p in per.values()) if per else None
        title = "📋 <b>Output</b> — predicted vs ground truth" + (f"  ·  score {score:.2f}%" if score is not None else "")
        if _tot is not None:
            title += f"  ({_tot}/{_mx} points, mean {_tot/max(1,len(per)):.2f}/{_mx/max(1,len(per)):.2f})"
        L.append(f'  ANS["{title}<br/>{arows}"]:::io')
    else:
        arows = "<br/>".join(f"{k}: {_esc(v)}" for k, v in sorted(ans_map.items(), key=lambda kv: _vk(kv[0]))[:16])
        L.append(f'  ANS["📋 <b>Output</b> — final answer<br/>{arows or _esc(_short(answer, 80))}"]:::io')
    for p in prev_layer:
        L.append(f"  {p} --> ANS")

    L.append("```")
    return "\n".join(L)


def _seq_esc(s):
    """Escape text for a Mermaid sequence message: no newlines, no ; or : that break parsing."""
    s = str(s).replace("\n", " ").replace(";", ",").replace(":", "-")
    s = s.replace('"', "'").replace("[", "(").replace("]", ")").replace("{", "(").replace("}", ")")
    s = s.replace("#", "").replace("<", "").replace(">", "")
    return re.sub(r"\s+", " ", s).strip()


def _oracle_result(name, out):
    """Render an oracle tool's return as the FACTS it certified, one per variable.

    The generic summariser truncates to a prefix, which for an oracle shows the first record and hides
    the rest -- the useful content is exactly which entities were certified as what."""
    if name not in _ORACLE_TOOL_NAMES:
        return summarize_output(name, out)
    facts = re.findall(r"['\"]vid['\"]\s*:\s*['\"](V\d+)['\"].{0,120}?['\"]ctype['\"]\s*:\s*['\"]([^'\"]+)['\"]",
                       str(out), re.S)
    if not facts:
        return "no certification — all oracles abstained"
    shown = "; ".join(f"{v}={t}" for v, t in facts[:8])
    return f"certified {len(facts)}: {shown}" + (" …" if len(facts) > 8 else "")


def to_sequence(recorder, meta, oracle_facts, answer, scoring=None, max_tools_per_phase=40):
    """A Mermaid SEQUENCE diagram of the COMPLETE flow, turn by turn: every delegation, every LLM
    reasoning turn (Note), every tool call and its returned result (message + reply), the types each
    subagent returned, the deterministic oracle certification, and the final answer. This is the
    exhaustive temporal view — nothing is grouped away."""
    plan_todos, coord_reasons, phases = _phases(recorder.events)
    L = ["```mermaid", "sequenceDiagram", "  autonumber",
         "  participant C as 🧭 Coordinator agent",
         "  participant W as ⚙️ type_worker agent",
         "  participant V as 🔍 verifier agent",
         "  participant T as 🔧 Tools/MCP"]
    # The `Oracles` lifeline models the deterministic POST-PASS. When the oracles are exposed as tools
    # and called by the reviewer they are not a separate actor -- they are ordinary calls on the
    # Tools/MCP lifeline, already drawn above with their real arguments and real returned facts.
    if meta.get("certified_by_code", True):
        L.append("  participant O as ✅ Oracles")
    for k, t in enumerate(plan_todos, 1):
        L.append(f"  Note over C: 📝 plan {k}. [{_plan_tag(t)}] {_seq_esc(t)}")
    for r in coord_reasons[:1]:
        L.append(f"  Note over C: 💭 {_seq_esc(r[:70])}")

    for i, ph in enumerate(phases):
        actor = "V" if ph["target"] == "verifier" else "W"
        assigned = " ".join(re.findall(r"\bV\d+\b", ph["desc"]))
        role = "adjudicate" if actor == "V" else "recover types"
        L.append(f"  C->>{actor}: task #{i + 1} — {role} {_seq_esc(assigned)}")
        shown = ph["tools"][:max_tools_per_phase]
        for t in shown:
            L.append(f"  {actor}->>T: {_seq_esc(t['name'])}({_seq_esc(t['input'])})")
            if t.get("output"):
                L.append(f"  T-->>{actor}: {_seq_esc(_oracle_result(t['name'], t['output']))}")
        if len(ph["tools"]) > len(shown):
            L.append(f"  Note over {actor}: … +{len(ph['tools']) - len(shown)} more tool calls")
        # WHY: the model's reasoning behind this task's conclusion, shown right before the result arrow.
        # Workers (gemma, thinking off) emit no prose — fall back to the evidence basis they inspected.
        genuine = [x for x in ph["reasons"] if not _final_types(x)]
        if genuine:
            L.append(f"  Note over {actor}: 💭 reasoning: {_seq_esc(genuine[-1][:180])}")
        elif ph["tools"]:
            _c = {}
            for t in ph["tools"]:
                _c[t["name"]] = _c.get(t["name"], 0) + 1
            ev = ", ".join(f"{n}×{k}" for k, n in _c.items())
            L.append(f"  Note over {actor}: 💭 reasoning: inferred from assembly evidence — {_seq_esc(ev)}")
        types = _phase_types(ph)
        if types:
            tt = ", ".join(f"{k}-{_seq_esc(v)}" for k, v in list(types.items())[:10])
            L.append(f"  {actor}-->>C: ✅ result: {tt}")

    consulted = meta.get("oracles_consulted", [])
    fired = {v[1] for v in oracle_facts.values() if isinstance(v, (list, tuple))} if oracle_facts else set()
    if meta.get("certified_by_code", True) and (consulted or oracle_facts):
        L.append(f"  C->>O: run {len(consulted)} deterministic oracles ({_seq_esc(', '.join(consulted))})")
        for vid, val in sorted(oracle_facts.items()):
            ctype, oracle, floor = (val if isinstance(val, (list, tuple)) and len(val) == 3
                                    else (val, "?", False))
            L.append(f"  O-->>C: ✓ {vid}- {_seq_esc(ctype)} via {_seq_esc(oracle)}"
                     + (" (floor)" if floor else ""))
        for o in consulted:                                     # make abstaining oracles explicit
            if o not in fired:
                L.append(f"  Note over O: {_seq_esc(o)} — consulted, abstained")
    # final result as the LAST arrow of the sequence: the coordinator emits the synthesized answer.
    ans = _final_types(answer)
    if ans:
        score = (scoring or {}).get("score")
        stxt = f" · score {score:.2f}%" if score is not None else ""
        tail = ", ".join(f"{k}-{_seq_esc(v)}" for k, v in sorted(ans.items(), key=lambda kv: int(re.sub(r'\D', '', kv[0]) or 0)))
        ncert = len([1 for v in oracle_facts.values() if isinstance(v, (list, tuple))]) if oracle_facts else 0
        _src = ("deterministically oracle-certified (authoritative)"
                if meta.get("certified_by_code", True) else "oracle facts the verifier fetched itself")
        L.append(f"  Note over C: 💭 reasoning: synthesized from the verifier's adjudicated types,"
                 f" with {ncert} {_src}")
        L.append(f"  C->>C: 📋 FINAL ANSWER{stxt}: {tail}")
    L.append("```")
    return "\n".join(L)


def to_markdown(recorder, meta, oracle_facts, answer, scoring=None):
    """A full, untruncated step-by-step log of the run — the complete 'underlying process' as a companion
    to the figure: input variables, plan, then per phase the reasoning + every tool call (input -> output)
    + the concluded types, then the deterministic oracle certification and the final answer vs GT/score."""
    plan_todos, coord_reasons, phases = _phases(recorder.events)
    M = [f"# Agentic run — function @{meta.get('vaddr', '?')}  ({meta.get('nvars', '?')} variables)", ""]
    variables = meta.get("variables") or []
    if variables:
        M.append("## Input — variables (location, size)")
        M.append("| id | location | bytes |")
        M.append("|----|----------|-------|")
        for vid, loc, sz in variables:
            M.append(f"| {vid} | {loc} | {sz} |")
        M.append("")
    M.append("## 1. Coordinator agent — decompose & delegate")
    for t in plan_todos:
        M.append(f"- {t}  _[{_plan_tag(t)}]_")
    for r in coord_reasons[:3]:
        M.append(f"> 💭 {r}")
    M.append("")
    for i, ph in enumerate(phases, 1):
        role = "verifier agent (decompilation lens)" if ph["target"] == "verifier" else "type_worker agent (assembly lens)"
        assigned = " ".join(re.findall(r"\bV\d+\b", ph["desc"]))
        M.append(f"## {i + 1}. {role}" + (f" — assigned {assigned}" if assigned else ""))
        if ph["desc"]:
            M.append(f"*delegated:* {ph['desc']}")
        for r in [x for x in ph["reasons"] if not _final_types(x)][:4]:   # skip type-list conclusions
            M.append(f"> 💭 {r}")
        if ph["tools"]:
            M.append("\n| # | tool | input | result |")
            M.append("|---|------|-------|--------|")
            for j, t in enumerate(ph["tools"], 1):
                res = summarize_output(t["name"], t.get("output", "")).replace("|", "\\|").replace("\n", " ")
                M.append(f"| {j} | `{t['name']}` | {t.get('input_full', t['input'])} | {res} |")
        types = _phase_types(ph)
        if types:
            verb = "Adjudicated" if ph["target"] == "verifier" else "Concluded"
            M.append(f"\n**{verb} types:** " + ", ".join(f"{k}: {v}" for k, v in types.items()))
        M.append("")
    consulted = meta.get("oracles_consulted", [])
    fired = {v[1] for v in oracle_facts.values() if isinstance(v, (list, tuple))} if oracle_facts else set()
    if consulted or oracle_facts:
        M.append("## Deterministic oracle certification" if meta.get("certified_by_code", True)
                 else "## Oracles — consulted by the verifier as tools, NOT applied by code")
        M.append("*Run in code after the agent finishes (NOT LLM tools). Each consulted oracle:*")
        for o in consulted:
            n = sum(1 for v in oracle_facts.values() if isinstance(v, (list, tuple)) and v[1] == o)
            M.append(f"- `{o}` — " + (f"**certified {n} variable(s)** ✓" if o in fired
                                      else "consulted, *abstained* (no fact)"))
        if oracle_facts:
            M.append("\n**Certified types (authoritative — override the agent):**")
            for vid, val in sorted(oracle_facts.items()):
                ctype, oracle, floor = (val if isinstance(val, (list, tuple)) and len(val) == 3 else (val, "?", False))
                M.append(f"- **{vid}**: `{ctype}` — via `{oracle}`" + (" *(floor)*" if floor else ""))
        M.append("")
    ans = _final_types(answer)
    gt = (scoring or {}).get("ground_truth") or {}
    score = (scoring or {}).get("score")
    _vk = lambda k: int(re.sub(r"\D", "", k) or 0)  # noqa: E731
    if gt:
        M.append("## Output — predicted vs ground truth" + (f"  (mean score: **{score:.2f}%**)" if score is not None else ""))
        _per = (scoring or {}).get("per_var") or {}
        M.append("| id | predicted | ground truth | score | lost at |")
        M.append("|----|-----------|--------------|-------|---------|")
        for vid in sorted(ans, key=_vk):
            p = _per.get(vid)
            sc_ = f"**{p['score']}/{p['max']}**" if p else _match(ans[vid], gt.get(vid))
            M.append(f"| {vid} | `{ans[vid]}` | `{gt.get(vid, '?')}` | {sc_} | "
                     f"{(p.get('halt') or '') if p else ''} |")
    else:
        M.append("## Output — final answer")
        for k in sorted(ans, key=_vk):
            M.append(f"- {k}: `{ans[k]}`")
    return "\n".join(M) + "\n"


def _final_types(answer):
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
        for m in re.finditer(r"(?mi)^\s*-?\s*(V\d+)\s*:\s*(.+?)\s*$", answer):
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


def compose_sequence_figure(seq_png, meta, answer, scoring, out_path):
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

    in_lines = [(f"🎯 INPUT — function @{meta.get('vaddr', '?')}  ({meta.get('nvars', '?')} variables)", title_f)]
    for vid, loc, sz in meta.get("variables", []):
        in_lines.append((f"    {vid}    {loc}    {sz} bytes", body_f))

    ans = _final_types(answer)
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
