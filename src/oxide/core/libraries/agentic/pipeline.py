"""agentic_re pipeline — the sequential, planner-driven orchestration loop.

This is the HEART of the agentic feature. Given a binary oid + a natural-language question it:

  plan (LLM, FULL ordered task list) -> for each task top-to-bottom:
      specialist agent(s) -> verify findings -> planner ASSESS (mark done / unsolvable)
      -> REPLAN the task (bounded retries) -> REVISE the plan (add tasks for new leads)
  -> deterministic call/value recall -> tiered synthesis
"""
from __future__ import annotations

import json
import re
from typing import List

from oxide.core.oxide import api

from oxide.core.libraries.agentic import prompts as P
from oxide.core.libraries.agentic import llm as L
from oxide.core.libraries.agentic import tools as T
from oxide.core.libraries.agentic import grounding as G
from oxide.core.libraries.agentic import trace as TR
from oxide.core.libraries.agentic import specialists as S


# ----------------------------------------------------------------------------- planning
def _cap(key: str, default: int) -> int:
    """Integer cap overridable via env AGENTIC_<KEY> or [agentic] config <key> (else `default`)."""
    return L.cfg_int(key, default)


def _new_task(tid: str, desc: str, specialists: list, origin: str) -> dict:
    return {"id": tid, "description": desc, "specialists": specialists, "status": "pending",
            "result": "", "raw_findings": [], "retries": 0, "origin": origin}


def _normalize_specialists(t: dict) -> list:
    """Coerce a task's specialist field to a list. Accepts `specialists: [...]` or a single
    `specialist: "..."`; defaults to ["generalist"]. Unknown names fall back to the full tool set
    inside S.groups_for, so any string is safe."""
    sp = t.get("specialists")
    if isinstance(sp, str):
        sp = [sp]
    if not sp:
        one = t.get("specialist")
        sp = [one] if one else []
    return [str(s) for s in sp if s] or ["generalist"]


def _coerce_tasks(raw: list, start_idx: int, origin: str) -> List[dict]:
    """Turn raw planner task JSON into normalized task dicts with stable T-ids."""
    out = []
    for j, t in enumerate(raw):
        desc = (t.get("description") or t.get("question") or "").strip()
        if not desc:
            continue
        out.append(_new_task(t.get("id", f"T{start_idx + len(out) + 1}"), desc,
                             _normalize_specialists(t), origin))
    return out


def _make_plan(planner, question: str, label: str, cap: int) -> List[dict]:
    """Ask the planner for a FULL ORDERED task list. Returns up to `cap` task dicts."""
    txt = planner.complete(P.PLAN_SYS, P.plan_user(question, label))
    d = P.extract_json(txt) or {}
    raw = d.get("plan") or [{"id": "T1", "description": question, "specialists": ["generalist"]}]
    return _coerce_tasks(raw, 0, "plan")[:cap]


# ----------------------------------------------------------------------------- specialist agents
def _worker_pass(spec, schemas, ct, worker, subtask, max_iter, log) -> List[dict]:
    """ONE ReAct pass of a specialist on a (sub)task; returns its parsed findings."""
    with TR.span(f"worker {subtask['id']} [{spec}]", "CHAIN", subtask["question"]) as _w_out:
        out = L.run_react(worker, S.backstory(spec), P.worker_user(subtask), schemas, ct,
                          max_iter, f"worker {subtask['id']}/{spec}", log)
        d = P.extract_json(out) or {}
        findings = []
        for f in (d.get("findings") or []):
            if not f.get("claim"):
                continue
            f.setdefault("evidence_refs", [])
            f["subtask_id"] = subtask["id"]
            findings.append(f)
        _w_out(json.dumps([f.get("claim") for f in findings]))
    return findings


def _worker_decompose(worker, question: str, subtask: dict) -> List[str]:
    """The agent triages the task: SIMPLE -> [] (one pass); COMPLEX -> ordered sub-step strings
    (<=4) to do one-by-one. Toggle off with AGENTIC_WORKER_DECOMPOSE=0 / [agentic] worker_decompose=0."""
    if str(L.cfg_get("worker_decompose", "1")).strip().lower() in ("0", "false", "no", "off"):
        return []
    d = P.extract_json(worker.complete(
        P.WORKER_DECOMPOSE_SYS,
        P.decompose_user(question, subtask["question"], subtask.get("prior", "")))) or {}
    if not d.get("complex"):
        return []
    return [str(s).strip() for s in (d.get("steps") or []) if str(s).strip()][:4]


def _run_worker(cfg, api_obj, oid: str, subtask: dict, max_iter: int, log) -> List[dict]:
    """Run ONE specialist on a task. The agent first triages the task: a SIMPLE task is answered in
    a single pass; a COMPLEX task is split into ORDERED sub-steps done ONE BY ONE — each sub-step
    sees the previous sub-steps' findings — and all findings are pooled and attributed to the task.
    The worker sees only its specialist's tool subset (+ backstory); call_tool can still dispatch
    any tool (so grounding/recall can re-run anything)."""
    spec = subtask.get("specialist", "generalist")
    schemas, ct = T.build_tools(api_obj, oid, groups=S.groups_for(spec))
    worker = L.make_llm("worker", cfg)
    question = subtask.get("goal") or subtask["question"]

    steps = _worker_decompose(worker, question, subtask)
    if not steps:                                          # SIMPLE -> one pass (the common case)
        return _worker_pass(spec, schemas, ct, worker, subtask, max_iter, log)

    # COMPLEX -> sequential sub-steps, each building on the previous ones' findings.
    print(f"    ⤷ {spec} split {subtask['id']} into {len(steps)} sub-steps")
    TR.note("AGENT_DECOMPOSE", {"task_id": subtask["id"], "specialist": spec, "steps": steps})
    pooled: List[dict] = []
    prior_lines = [subtask["prior"]] if subtask.get("prior") else []
    for si, step in enumerate(steps):
        sub = {**subtask, "id": f"{subtask['id']}.{si + 1}", "question": step,
               "prior": "\n".join(prior_lines).strip()}
        print(f"      · {sub['id']}: {step[:70]}")
        fs = _worker_pass(spec, schemas, ct, worker, sub, max_iter, log)
        for f in fs:
            f["subtask_id"] = subtask["id"]                # attribute to the PARENT task
        pooled.extend(fs)
        prior_lines.append(f"- {step}: " + "; ".join(f.get("claim", "") for f in fs)[:280])
    return pooled


def _dispatch_task(cfg, oid: str, question: str, task: dict, prior: str, max_iter: int,
                   log) -> List[dict]:
    """Run the task's specialist agent(s) one by one and pool their findings. Each specialist
    gets the task description as its sub-question plus the prior-task-results context."""
    pooled: List[dict] = []
    for spec in task["specialists"]:
        sub = {"id": task["id"], "question": task["description"], "goal": question,
               "specialist": spec, "prior": prior}
        try:
            pooled.extend(_run_worker(cfg, api, oid, sub, max_iter, log))
        except Exception as e:  # noqa: BLE001
            print(f"  ⚠ {task['id']}/{spec} failed: {str(e)[:80]}")
    return pooled


# ----------------------------------------------------------------------------- verification
def _adjudicate(verifier, call_tool, finding: dict, log) -> dict:
    """Deterministic fast-paths first (V1/V3/V4), then the tool-using LLM verifier."""
    grounded, ev = G.deterministic_grounding(call_tool, finding)
    if grounded:
        return {"consensus": "AGREE", "reason": f"deterministically reproduced — {ev}", "corrected_claim": ""}
    cg, cev = G.call_grounding(call_tool, finding)
    if cg:
        return {"consensus": "AGREE", "reason": f"deterministically reproduced — {cev}", "corrected_claim": ""}
    absent = G.false_absence(call_tool, finding)
    if absent:
        present = absent.split("DOES call ", 1)[1].split(" —", 1)[0]
        return {"consensus": "DISAGREE", "reason": absent,
                "corrected_claim": f"the code DOES call {present}"}
    # tool-using LLM verifier (different model family) — gets the FULL tool set (can re-run anything)
    refs = json.dumps(finding.get("evidence_refs", []))[:1500]
    raw = L.run_react(verifier, P.VERIFIER_BACKSTORY, P.verifier_user(finding.get("claim"), refs),
                      T.TOOL_SCHEMAS, call_tool, 8, "verifier", log)
    d = P.extract_json(raw) or {}
    consensus = str(d.get("consensus", "")).upper()
    # INCONCLUSIVE is now a first-class verdict the verifier may emit (uncertain != refuted), so only
    # fall through to the reformat salvage when NO valid verdict was parsed at all.
    if consensus not in ("AGREE", "DISAGREE", "INCONCLUSIVE") and raw.strip():
        reformat = verifier.complete(P.REFORMAT_SYS, P.reformat_user(finding.get("claim"), raw))
        d = P.extract_json(reformat) or {}
        consensus = str(d.get("consensus", "")).upper()
    if consensus not in ("AGREE", "DISAGREE", "INCONCLUSIVE"):
        consensus = "INCONCLUSIVE"
    return {"consensus": consensus, "reason": str(d.get("reason", ""))[:300],
            "corrected_claim": d.get("corrected_claim", "")}


def _dedup_claims(findings: List[dict]) -> List[dict]:
    """Collapse exact-duplicate claims (same subject+content) before the expensive verification.
    Key on (subject, content) so different hypotheses for the same subject are both kept."""
    def _key(f):
        c = str(f.get("claim", "")).strip()
        m = re.match(r"\s*[*<]*([A-Za-z0-9_\-]+)[>*]*\s*[:=]\s*(.+)", c)
        if m:
            return (m.group(1).lower(), re.sub(r"[^a-z0-9]+", "", m.group(2).lower()))
        return ("", re.sub(r"[^a-z0-9]+", " ", c.lower()).strip())
    seen, out = set(), []
    for f in findings:
        k = _key(f)
        if k[1] and k in seen:
            continue
        seen.add(k)
        out.append(f)
    return out


def _apply_verifier_correction(records: List[dict], f: dict, v: dict, main_ct) -> None:
    """Promote a verifier's DISAGREE correction to a certified fact ONLY when it asserts something
    positive (not an admission of absence/ignorance) and isn't itself a false-absence — so a vague
    refutation can't overwrite a concrete finding (e.g. char* -> undefined*)."""
    cc = (v.get("corrected_claim") or "").strip()
    _vague = re.search(r"undefined|unknown|cannot|could ?n'?t|undetermin|not (present|"
                       r"accessed|referenced|found|in (the )?decompile)|no (evidence|access|"
                       r"usage|such)|unused|likely not", cc, re.I)
    if v.get("consensus") == "DISAGREE" and len(cc) > 10 and not _vague \
            and cc.lower() != str(f.get("claim", "")).strip().lower():
        if G.false_absence(main_ct, {"claim": cc, "evidence_refs": f.get("evidence_refs", [])}):
            print(f"    ⊘ dropped false-absence correction: {cc[:70]}")
        else:
            records.append({"finding": {"claim": cc, "confidence": 1.0,
                            "source": "verifier_correction",
                            "evidence_refs": f.get("evidence_refs", []),
                            "subtask_id": f.get("subtask_id")},
                            "verdict": {"consensus": "AGREE"}})


# ----------------------------------------------------------------------------- assess / revise
def _assess_task(planner, question, task, verified, suspected, prior) -> dict:
    """Planner reads this task's verified/suspected findings and decides solved? + a result."""
    d = P.extract_json(planner.complete(
        P.TASK_ASSESS_SYS, P.assess_user(question, task, verified, suspected, prior))) or {}
    return {"solved": bool(d.get("solved", False)), "result": str(d.get("result", "")),
            "reason": str(d.get("reason", "")), "retry_task": str(d.get("retry_task", "")).strip()}


def _revise_plan(planner, question, plan, just_done, start_idx: int, cap: int) -> List[dict]:
    """Planner may APPEND new tasks when a finding opens a lead. Returns deduped new task dicts
    (bounded by `cap` = remaining task budget)."""
    if cap <= 0:
        return []
    d = P.extract_json(planner.complete(
        P.PLAN_REVISE_SYS, P.revise_user(question, plan, just_done))) or {}
    new = _dedup_against_plan(_coerce_tasks(d.get("add_tasks") or [], start_idx, "revise"), plan)[:cap]
    if new:
        print(f"  + REVISE: added {len(new)} task(s) — {str(d.get('reason', ''))[:80]}")
        TR.note("REVISE", {"added": [{"id": t["id"], "description": t["description"],
                                      "specialists": t["specialists"]} for t in new],
                           "reason": str(d.get("reason", ""))})
    return new


def _dedup_against_plan(new: List[dict], plan: List[dict]) -> List[dict]:
    seen = {str(t.get("description", "")).strip().lower() for t in plan}
    out = []
    for t in new:
        k = str(t["description"]).strip().lower()
        if k and k not in seen:
            seen.add(k)
            out.append(t)
    return out


def _completed_count(plan: List[dict]) -> int:
    return sum(1 for t in plan if t["status"] in ("done", "unsolvable"))


def _prior_results(plan: List[dict], i: int, cap: int = 5000) -> str:
    """Capped concatenation of the results of DONE tasks before index i (sequential context)."""
    lines = [f"- {t['id']}: {t['result']}" for t in plan[:i]
             if t["status"] == "done" and (t.get("result") or "").strip()]
    return "\n".join(lines)[:cap]


def _print_plan(plan: List[dict]) -> None:
    print(f"\n── PLAN ({len(plan)} tasks) ──")
    for t in plan:
        print(f"  {t['id']} [{t['status']}] ({','.join(t['specialists'])})  {t['description'][:78]}")


def _synthesize(planner, question, verified, suspected) -> str:
    ans = planner.complete(P.SYNTH_SYS + "\n\n" + P.COMPOSE_RULE + "\n\n" + P.BRANCH_TARGET_RULE
                           + "\n\n" + P.COORDINATE_RULE,
                           P.synth_user(question, verified, suspected))
    return planner.complete(P.CONSISTENCY_SYS, P.consistency_user(question, verified, ans))


# ----------------------------------------------------------------------------- public entry
def run(oid: str, question: str, cfg: dict, max_rounds: int, max_subtasks: int,
        max_iter: int) -> str:
    """Run the sequential planner-driven analysis on ONE oid; returns the tiered answer.
    Called by the plugin (plugins/agentic_re.py). Caps are env-overridable (see _analyze_oid_impl)."""
    with TR.span(f"binre.run: {question[:60]}", "AGENT", f"{oid}\n{question}") as _root_out:
        ans = _analyze_oid_impl(oid, question, cfg, max_rounds, max_subtasks, max_iter)
        _root_out(ans)
        return ans


def _analyze_oid_impl(oid: str, question: str, cfg: dict, max_rounds: int, max_subtasks: int,
                      max_iter: int) -> str:
    log = lambda m: print(m)
    # caps (env / [agentic] config overridable); the legacy opts supply the defaults.
    max_tasks = _cap("max_tasks", max_subtasks)
    max_retries = _cap("max_retries", max_rounds)
    max_calls = _cap("max_llm_calls", 0)

    # warm the heavy extractor so the workers only read cached results
    api.retrieve("ghidra_disasm", [oid])
    api.retrieve("function_extract", [oid])

    planner = L.make_llm("planner", cfg)
    verifier = L.make_llm("verifier", cfg)
    _schemas, main_ct = T.build_tools(api, oid)   # full-tool dispatcher for verify/grounding/recall

    with TR.span("planner: make ordered plan", "CHAIN", question) as _p_out:
        plan = _make_plan(planner, question, oid, max_tasks)
        _p_out(json.dumps([t["description"] for t in plan]))
    _print_plan(plan)
    TR.note("PLAN", [{"id": t["id"], "description": t["description"],
                      "specialists": t["specialists"]} for t in plan])

    records: List[dict] = []          # {"finding","verdict"} across ALL tasks -> recall + synth
    i = 0
    while i < len(plan):
        if max_calls and L.USAGE["calls"] >= max_calls:
            print(f"── BUDGET: {L.USAGE['calls']} LLM calls ≥ cap {max_calls}; stopping ──")
            break
        if _completed_count(plan) >= max_tasks:
            print(f"── BUDGET: {max_tasks} tasks completed; stopping ──")
            break
        task = plan[i]
        if task["status"] != "pending":
            i += 1
            continue
        print(f"\n▶ {task['id']}: {task['description'][:78]}  [{','.join(task['specialists'])}]")
        TR.note("TASK_START", {"id": task["id"], "description": task["description"],
                               "specialists": task["specialists"], "attempt": task["retries"] + 1})
        prior = _prior_results(plan, i)

        with TR.span(f"task {task['id']}", "CHAIN", task["description"]) as _t_out:
            # DISPATCH specialist agent(s) -> ANALYZE (verify each finding) -- serial.
            findings = _dedup_claims(_dispatch_task(cfg, oid, question, task, prior, max_iter, log))
            task_records: List[dict] = []
            for f in findings:
                with TR.span(f"adjudicate: {str(f.get('claim', ''))[:48]}", "CHAIN",
                             f.get("claim", "")) as _a_out:
                    v = _adjudicate(verifier, main_ct, f, log)
                    _a_out(json.dumps(v))
                rec = {"finding": f, "verdict": v}
                records.append(rec)
                task_records.append(rec)
                mark = {"AGREE": "✓", "DISAGREE": "✗"}.get(v["consensus"], "~")
                print(f"    {mark} {str(f['claim'])[:80]}")
                _apply_verifier_correction(records, f, v, main_ct)
            task["raw_findings"] = findings
            tverified = [r["finding"] for r in task_records if r["verdict"]["consensus"] == "AGREE"]
            tsuspected = [r["finding"] for r in task_records if r["verdict"]["consensus"] != "AGREE"]

            # ASSESS: planner synthesizes the task result + marks solved/unsolved.
            assess = _assess_task(planner, question, task, tverified, tsuspected, prior)
            _t_out(json.dumps(assess))
        TR.note("ASSESS", {"id": task["id"], "solved": assess["solved"],
                           "result": assess["result"], "reason": assess["reason"],
                           "findings": [f.get("claim") for f in findings],
                           "verified": [f.get("claim") for f in tverified]})

        if assess["solved"]:
            task["status"] = "done"
            task["result"] = assess["result"]
            print(f"  ✓ {task['id']} DONE — {assess['result'][:78]}")
            TR.note("TASK_END", {"id": task["id"], "status": "done", "result": task["result"]})
        elif task["retries"] < max_retries:
            task["retries"] += 1
            if assess["retry_task"]:
                task["description"] = assess["retry_task"]
            task["origin"] = "retry"
            print(f"  ↻ {task['id']} REPLAN ({task['retries']}/{max_retries}) — {assess['reason'][:68]}")
            TR.note("REPLAN", {"id": task["id"], "attempt": task["retries"] + 1,
                               "new_description": task["description"], "reason": assess["reason"]})
            continue
        else:
            task["status"] = "unsolvable"
            task["result"] = assess["result"]
            print(f"  ✗ {task['id']} CAN'T-BE-SOLVED — {assess['reason'][:64]}")
            TR.note("TASK_END", {"id": task["id"], "status": "unsolvable", "reason": assess["reason"]})

        new = _revise_plan(planner, question, plan, task, len(plan), max_tasks - len(plan))
        if new:
            plan.extend(new)
            _print_plan(plan)
        i += 1

    # DETERMINISTIC capability recall (R1)
    try:
        prog_calls = G.enumerate_program_calls(main_ct)
        if prog_calls:
            names = ", ".join(f"`{c}`" for c in sorted(prog_calls))
            records.append({"finding": {
                "claim": ("Deterministic call set (parsed from the program's call graph) — the "
                          f"program invokes these functions: {names}. Treat their presence as established."),
                "confidence": 1.0, "source": "deterministic_callgraph",
                "evidence_refs": [{"tool": "callgraph", "args": {"root": "main"}}]},
                "verdict": {"consensus": "AGREE", "reason": "deterministically enumerated from the call graph"}})
            print(f"  + deterministic call set: {', '.join(sorted(prog_calls))}")
    except Exception as e:  # noqa: BLE001
        print(f"  (call-set enumeration skipped: {str(e)[:80]})")

    # DETERMINISTIC value recall (R3)
    try:
        for fact, ref in G.value_recall_facts(main_ct, records):
            records.append({"finding": {
                "claim": "Deterministically recovered value — " + fact + ". Reproduced by re-running the tool; treat as established.",
                "confidence": 1.0, "source": "deterministic_value_recall", "evidence_refs": [ref]},
                "verdict": {"consensus": "AGREE", "reason": "re-ran the cited transform — value reproduced"}})
            print(f"  + recovered value: {fact}")
    except Exception as e:  # noqa: BLE001
        print(f"  (value recall skipped: {str(e)[:80]})")

    # DETERMINISTIC coordinate recall (R4)
    try:
        for fact, ref in G.coordinate_recall_facts(main_ct, records):
            records.append({"finding": {
                "claim": "Deterministic coordinate conversion — " + fact + ". Reproduced by re-running vaddr_to_file_offset; treat as established.",
                "confidence": 1.0, "source": "deterministic_coordinate_recall", "evidence_refs": [ref]},
                "verdict": {"consensus": "AGREE", "reason": "re-ran vaddr_to_file_offset — conversion reproduced"}})
            print(f"  + coordinate: {fact}")
    except Exception as e:  # noqa: BLE001
        print(f"  (coordinate recall skipped: {str(e)[:80]})")

    verified = [r["finding"] for r in records if r["verdict"]["consensus"] == "AGREE"]
    
    _vclaims = {str(f.get("claim", "")).strip().lower() for f in verified}
    suspected = [r["finding"] for r in records
                 if r["verdict"]["consensus"] != "AGREE"
                 and str(r["finding"].get("claim", "")).strip().lower() not in _vclaims]
    _d = sum(1 for t in plan if t["status"] == "done")
    _u = sum(1 for t in plan if t["status"] == "unsolvable")
    _p = sum(1 for t in plan if t["status"] == "pending")
    print(f"\n── PLAN STATUS: {_d} done, {_u} unsolvable, {_p} pending ──")
    print(f"── SYNTHESIZE ({len(verified)} verified, {len(suspected)} suspected"
          f"/{len(records)} total) ──")
    with TR.span("synthesize: tiered answer", "CHAIN", f"{len(verified)} verified findings") as _s_out:
        answer = _synthesize(planner, question, verified, suspected)
        _s_out(answer)
    TR.note("ANSWER", answer)
    print(f"── TOKENS: {L.USAGE['completion']:,} out / {L.USAGE['prompt']:,} in across "
          f"{L.USAGE['calls']} model calls ──")
    return answer
