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
from concurrent.futures import ThreadPoolExecutor
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
        evidence: List[dict] = []                    # the worker's REAL (tool, args, result) trail
        out = L.run_react(worker, S.backstory(spec), P.worker_user(subtask), schemas, ct,
                          max_iter, f"worker {subtask['id']}/{spec}", log,
                          output_schema=P.WORKER_FINDINGS_SCHEMA, evidence_sink=evidence)
        d = P.extract_json(out) or {}
        findings = []
        for f in (d.get("findings") or []):
            if not f.get("claim"):
                continue
            f.setdefault("evidence_refs", [])
            # Attach the worker's ACTUAL tool output so the verifier can confirm the claim against what
            # the worker saw, rather than re-deriving from scratch (a light step-cap can't reproduce a
            # multi-tool investigation, so correct findings were dying as INCONCLUSIVE -> undefined).
            f["worker_evidence"] = evidence
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
# A verifier DISAGREE justified ONLY by absence ("returned no slot / no such variable / doesn't
# exist / empty result / not found") is not a positive contradiction — the verifier's own rule is
# "absence of evidence is NOT contradiction -> INCONCLUSIVE". Models violate it, and a false absence
# DISAGREE drags a CORRECT finding to undefined. Downgrade such verdicts to INCONCLUSIVE so they
# can't refute; keep DISAGREE only when it offers a CONCRETE alternative value. Generic (any entity).
_ABSENCE_RE = re.compile(
    r"\bno\b.{0,24}\b(slot|stack\s*var\w*|variable|value|entry|access\w*|reference|call|register|"
    r"such|match|result|offset)\b|does\s*n[o']?t\s+exist|not\s+exist|doesn.?t\s+exist|"
    r"empty\s+result|returned\s+no\b|there\s+is\s+no\b|not\s+found|no\s+entry|"
    r"nothing\s+(was\s+)?(found|returned)", re.I)


def _absence_only_disagree(reason: str, corrected: str) -> bool:
    """True if a DISAGREE is justified purely by absence (couldn't find it), with no concrete
    alternative value in corrected_claim."""
    if not _ABSENCE_RE.search(reason or ""):
        return False
    cc = (corrected or "").strip()
    return not cc or len(cc) < 8 or bool(_ABSENCE_RE.search(cc))


def _guard_absence(verdict: dict) -> dict:
    """Downgrade an absence-only DISAGREE to INCONCLUSIVE in place; returns the verdict."""
    if verdict.get("consensus") == "DISAGREE" and \
            _absence_only_disagree(verdict.get("reason", ""), verdict.get("corrected_claim", "")):
        verdict["consensus"] = "INCONCLUSIVE"
        verdict["reason"] = "[absence-only refutation downgraded] " + str(verdict.get("reason", ""))
    return verdict


def _adjudicate(verifier, call_tool, finding: dict, log, question: str = "") -> dict:
    """Deterministic fast-paths first (storage identity, then V1/V3/V4), then the tool-using LLM verifier."""
    sv = G.storage_consistency_violation(question, finding)
    if sv:
        return {"consensus": "DISAGREE", "reason": f"storage mismatch — {sv}", "corrected_claim": ""}
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
    # require_grounding=False: the verifier already has its own grounding discipline; forcing it would
    # turn every quick verdict into a full 8-step investigation (the grounding guard is for WORKERS).
    raw = L.run_react(verifier, P.VERIFIER_BACKSTORY,
                      P.verifier_user(finding.get("claim"), refs, finding.get("worker_evidence")),
                      T.TOOL_SCHEMAS, call_tool, _cap("verify_max_iter", 8), "verifier", log,
                      require_grounding=False)
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
    verdict = _guard_absence({"consensus": consensus, "reason": str(d.get("reason", ""))[:300],
                              "corrected_claim": d.get("corrected_claim", "")})
    # register-source guard (V5): a DISAGREE whose corrected_claim asserts a register source the tool
    # CONTRADICTS is a hallucination — downgrade to INCONCLUSIVE so it can't refute the real finding.
    if verdict["consensus"] == "DISAGREE" and str(verdict.get("corrected_claim", "")).strip():
        if G.false_register_source(call_tool, {"claim": verdict["corrected_claim"],
                                               "evidence_refs": finding.get("evidence_refs", [])}):
            verdict["consensus"] = "INCONCLUSIVE"
            verdict["reason"] = "[false register-source refutation downgraded] " + verdict["reason"]
    return verdict


def _adjudicate_batch(verifier, call_tool, findings: List[dict], log, question: str = "") -> List[tuple]:
    """SAFE call-reducer: same deterministic oracles per finding (storage identity, V1/V3/V4), then ONE
    batched LLM verifier call for ALL remaining findings instead of one call each. Returns
    [(finding, verdict)]. Same claims + criteria, judged together — score-neutral; only LLM calls collapse."""
    verdicts: List = [None] * len(findings)
    pending = []                                   # (idx, finding) needing the LLM verifier
    for idx, f in enumerate(findings):
        sv = G.storage_consistency_violation(question, f)
        if sv:
            verdicts[idx] = {"consensus": "DISAGREE", "reason": f"storage mismatch — {sv}",
                             "corrected_claim": ""}
            continue
        grounded, ev = G.deterministic_grounding(call_tool, f)
        if grounded:
            verdicts[idx] = {"consensus": "AGREE", "reason": f"deterministically reproduced — {ev}",
                             "corrected_claim": ""}
            continue
        cg, cev = G.call_grounding(call_tool, f)
        if cg:
            verdicts[idx] = {"consensus": "AGREE", "reason": f"deterministically reproduced — {cev}",
                             "corrected_claim": ""}
            continue
        absent = G.false_absence(call_tool, f)
        if absent:
            present = absent.split("DOES call ", 1)[1].split(" —", 1)[0]
            verdicts[idx] = {"consensus": "DISAGREE", "reason": absent,
                             "corrected_claim": f"the code DOES call {present}"}
            continue
        pending.append((idx, f))

    if pending:
        items = [{"id": j + 1, "claim": f.get("claim"), "refs": f.get("evidence_refs", [])}
                 for j, (idx, f) in enumerate(pending)]
        with TR.span(f"adjudicate-batch: {len(pending)} findings", "CHAIN",
                     json.dumps([it["claim"] for it in items])[:200]) as _b_out:
            raw = L.run_react(verifier, P.VERIFIER_BATCH_SYS, P.verifier_batch_user(items),
                              T.TOOL_SCHEMAS, call_tool, _cap("verify_max_iter", 8), "verifier-batch", log,
                              require_grounding=False)
            d = P.extract_json(raw) or {}
            by_id = {}
            for v in (d.get("verdicts") or []):
                try:
                    by_id[int(v.get("id"))] = v
                except (TypeError, ValueError):
                    pass
            _b_out(json.dumps({"n": len(pending), "parsed": len(by_id)}))
        for j, (idx, f) in enumerate(pending):
            v = by_id.get(j + 1) or {}
            cons = str(v.get("consensus", "")).upper()
            if cons not in ("AGREE", "DISAGREE", "INCONCLUSIVE"):
                cons = "INCONCLUSIVE"             # missing/unparsed verdict -> abstain (never overrides)
            verdicts[idx] = _guard_absence({"consensus": cons, "reason": str(v.get("reason", ""))[:300],
                                             "corrected_claim": v.get("corrected_claim", "")})
    return list(zip(findings, verdicts))


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


def _entity_subj(claim) -> str:
    """The referent a finding predicates ABOUT, generically: the first identifier token of the
    form <alpha><digits> (e.g. a variable id `V5`, a block `BB3`). Such ids are how independent
    tasks refer to the same logical entity; everything else (prose, addresses) yields None and is
    never superseded. Belief-revision key only — not type/RE specific."""
    m = re.search(r"\b([A-Za-z]{1,5}[0-9]{1,4})\b", str(claim))
    return m.group(1) if m else None


_ABSTAIN_RE = re.compile(r"undefined|unknown|undetermin|cannot|could ?n'?t|not (present|accessed|"
                         r"referenced|found|determin)|no (evidence|usage|access)|unused", re.I)
_STOP_TOKENS = {"the", "a", "an", "is", "are", "was", "of", "to", "in", "and", "it", "its",
                "as", "for", "this", "that", "with", "at", "on", "be"}


def _value_tokens(claim, subj: str) -> set:
    """Content tokens of a claim with the entity subject and stopwords removed — the basis for
    Jaccard-clustering prose variants of one asserted value into a single consensus group."""
    c = re.sub(r"\b" + re.escape(subj) + r"\b", " ", str(claim).lower())
    return set(re.findall(r"[a-z0-9_*]+", c)) - _STOP_TOKENS


def _jaccard(a: set, b: set) -> float:
    return len(a & b) / len(a | b) if (a or b) else 1.0


def _supersede(records: List[dict]) -> int:
    """Generic belief revision over VERIFIED findings, CONSENSUS over recency (recency-wins was the
    measured root cause of per-function score variance — a later task is just another stochastic
    draw and routinely swapped/dropped values an earlier task had right). Per entity subject
    (`_entity_subj`): (1) a concrete value always beats an ABSTENTION (undefined/unknown/absent);
    (2) concrete findings are clustered by token-Jaccard overlap (>=0.5) so prose variants of one
    value group together, and the value backed by the MOST distinct tasks wins — recency only breaks
    ties (so a genuine later correction backed by >=2 tasks still wins). Deterministic-recall
    findings carry seq=None and are exempt (always kept). Marks losers with `_superseded`; returns
    the count."""
    agree = [r for r in records if r["verdict"]["consensus"] == "AGREE" and r.get("seq") is not None]
    by_subj: dict = {}
    for r in agree:
        s = _entity_subj(r["finding"].get("claim", ""))
        if s is not None:
            by_subj.setdefault(s, []).append(r)
    n = 0
    for s, rs in by_subj.items():
        concrete = [r for r in rs if not _ABSTAIN_RE.search(str(r["finding"].get("claim", "")))]
        if concrete and len(concrete) < len(rs):           # (1) concrete beats abstention
            for r in rs:
                if r not in concrete:
                    r["_superseded"] = True
                    n += 1
        if len(concrete) < 2:
            continue
        clusters: List[list] = []                          # (2) Jaccard-cluster the concrete values
        for r in concrete:
            toks = _value_tokens(r["finding"].get("claim", ""), s)
            for cl in clusters:
                if _jaccard(toks, cl[0][1]) >= 0.5:
                    cl.append((r, toks))
                    break
            else:
                clusters.append([(r, toks)])
        if len(clusters) < 2:
            continue                                       # one value (however phrased) -> no conflict
        win = max(clusters, key=lambda cl: (len({r["seq"] for r, _ in cl}),
                                            max(r["seq"] for r, _ in cl)))
        for cl in clusters:
            if cl is not win:
                for r, _ in cl:
                    r["_superseded"] = True
                    n += 1
    return n


def _apply_verifier_correction(records: List[dict], f: dict, v: dict, main_ct, seq=None) -> None:
    """Promote a verifier's DISAGREE correction to a certified fact ONLY when it asserts something
    positive (not an admission of absence/ignorance) and isn't itself a false-absence — so a vague
    refutation can't overwrite a concrete finding (e.g. char* -> undefined*)."""
    cc = (v.get("corrected_claim") or "").strip()
    _vague = re.search(r"undefined|unknown|cannot|could ?n'?t|undetermin|not (present|"
                       r"accessed|referenced|found|in (the )?decompile)|no (evidence|access|"
                       r"usage|such)|unused|likely not", cc, re.I)
    if v.get("consensus") == "DISAGREE" and len(cc) > 10 and not _vague \
            and cc.lower() != str(f.get("claim", "")).strip().lower():
        _cc_finding = {"claim": cc, "evidence_refs": f.get("evidence_refs", [])}
        if G.false_absence(main_ct, _cc_finding):
            print(f"    ⊘ dropped false-absence correction: {cc[:70]}")
        elif G.false_register_source(main_ct, _cc_finding):     # V5: reject hallucinated reg source
            print(f"    ⊘ dropped false register-source correction: {cc[:70]}")
        else:
            records.append({"finding": {"claim": cc, "confidence": 1.0,
                            "source": "verifier_correction",
                            "evidence_refs": f.get("evidence_refs", []),
                            "subtask_id": f.get("subtask_id")},
                            "verdict": {"consensus": "AGREE"}, "seq": seq})


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


def _synthesize(planner, question, verified, suspected, task_results=None) -> str:
    ans = planner.complete(P.SYNTH_SYS + "\n\n" + P.COMPOSE_RULE + "\n\n" + P.BRANCH_TARGET_RULE
                           + "\n\n" + P.COORDINATE_RULE,
                           P.synth_user(question, verified, suspected, task_results))
    return planner.complete(P.CONSISTENCY_SYS,
                            P.consistency_user(question, verified, ans, task_results))


# ----------------------------------------------------------------------------- public entry
def run(oid: str, question: str, cfg: dict, max_rounds: int, max_subtasks: int,
        max_iter: int, fixed_plan: list | None = None) -> str:
    """Run the sequential planner-driven analysis on ONE oid; returns the tiered answer.
    Called by the plugin (plugins/agentic_re.py). Caps are env-overridable (see _analyze_oid_impl).
    fixed_plan: optional caller-supplied task list ([{id, description, specialists}, ...]) — skips
    the planner's plan call AND plan revision, so the task structure is deterministic; the planner
    still assesses/replans individual tasks and synthesizes."""
    # Reset the per-run LLM-usage counter so the max_llm_calls budget is PER-FUNCTION. L.USAGE is a
    # module-level accumulator; without this, a process that analyzes many functions (run_trex.py
    # --all) would carry the count across functions and starve every function after the budget is hit.
    L.USAGE["prompt"] = L.USAGE["completion"] = L.USAGE["calls"] = 0
    with TR.span(f"binre.run: {question[:60]}", "AGENT", f"{oid}\n{question}") as _root_out:
        ans = _analyze_oid_impl(oid, question, cfg, max_rounds, max_subtasks, max_iter, fixed_plan)
        _root_out(ans)
        return ans


def _analyze_oid_impl(oid: str, question: str, cfg: dict, max_rounds: int, max_subtasks: int,
                      max_iter: int, fixed_plan: list | None = None) -> str:
    log = lambda m: print(m)
    # caps (env / [agentic] config overridable); the legacy opts supply the defaults.
    max_tasks = _cap("max_tasks", max_subtasks)
    max_retries = _cap("max_retries", max_rounds)
    max_calls = _cap("max_llm_calls", 0)
    verify_conc = max(1, _cap("verify_concurrency", 1))    # adjudicate N findings concurrently (1=serial)
    # early-exit (AGENTIC_EARLY_EXIT=1): the entity ids the question asks about (e.g. V1..Vn); once
    # every one has a VERIFIED finding, remaining tasks are skipped. Empty set = feature off.
    early_ids = (set(re.findall(r"\b[A-Z]{1,4}[0-9]{1,4}\b", question))
                 if _cap("early_exit", 0) == 1 else set())

    # warm the heavy extractor so the workers only read cached results
    api.retrieve("ghidra_disasm", [oid])
    api.retrieve("function_extract", [oid])

    planner = L.make_llm("planner", cfg)
    verifier = L.make_llm("verifier", cfg)
    # Deterministic layer's dispatcher: memoize=False so oracles/recall/verification always get the
    # FULL tool output. (The truncated [REPEAT CALL] stub is only for the workers' own memoized
    # dispatchers; feeding it to an oracle made it silently mis-read a truncated decompilation.)
    _schemas, main_ct = T.build_tools(api, oid, memoize=False)   # verify / grounding / recall / Ω

    if fixed_plan:
        # Caller-supplied deterministic plan: no planner call, and no revision below — the task
        # STRUCTURE is fixed; only task content (worker findings, assess results) is model-driven.
        plan = _coerce_tasks(fixed_plan, 0, "fixed")[:max_tasks]
    else:
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

            def _adj_one(f):
                # one finding's verification (independent of the others). The file trace is lock-guarded
                # (trace._TRACE_LOCK), so concurrent spans/writes are safe.
                with TR.span(f"adjudicate: {str(f.get('claim', ''))[:48]}", "CHAIN",
                             f.get("claim", "")) as _a_out:
                    v = _adjudicate(verifier, main_ct, f, log, question)
                    _a_out(json.dumps(v))
                return f, v

            # SAFE call-reducer: one batched verifier call for all findings (AGENTIC_VERIFY_BATCH=1),
            # else the legacy per-finding path (optionally concurrent to fill the idle GPU).
            if _cap("verify_batch", 0) == 1 and findings:
                results = _adjudicate_batch(verifier, main_ct, findings, log, question)
            elif verify_conc > 1 and len(findings) > 1:
                with ThreadPoolExecutor(max_workers=verify_conc) as _ex:
                    results = list(_ex.map(_adj_one, findings))
            else:
                results = [_adj_one(f) for f in findings]

            # apply verdicts SEQUENTIALLY (shared state: records, corrections, prints).
            for f, v in results:
                rec = {"finding": f, "verdict": v, "seq": i}
                records.append(rec)
                task_records.append(rec)
                mark = {"AGREE": "✓", "DISAGREE": "✗"}.get(v["consensus"], "~")
                print(f"    {mark} {str(f['claim'])[:80]}")
                _apply_verifier_correction(records, f, v, main_ct, seq=i)
            task["raw_findings"] = findings
            tverified = [r["finding"] for r in task_records if r["verdict"]["consensus"] == "AGREE"]
            tsuspected = [r["finding"] for r in task_records if r["verdict"]["consensus"] != "AGREE"]

            # ASSESS: with a FIXED plan, assess DETERMINISTICALLY — the task's result IS its verified
            # findings (solved iff it verified anything). This skips the assess LLM call, removes the
            # replan/dropped-findings failure (a group with 1-2 uncovered vars was marked "unsolvable",
            # which both wasted retries AND excluded its verified findings from synthesis), and keeps
            # the task result authoritative. Otherwise the planner assesses (LLM).
            if fixed_plan:
                claims = "; ".join(str(f.get("claim", "")) for f in tverified)
                assess = {"solved": bool(tverified), "result": claims,
                          "reason": f"fixed-plan: {len(tverified)} verified finding(s) recorded",
                          "retry_task": ""}
            else:
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

        if early_ids and task["status"] == "done":
            have = {_entity_subj(r["finding"].get("claim", ""))
                    for r in records if r["verdict"]["consensus"] == "AGREE"}
            if early_ids <= have:
                print(f"── EARLY-EXIT: verified findings cover all {len(early_ids)} question ids ──")
                TR.note("EARLY_EXIT", {"ids": sorted(early_ids)})
                break

        # REVISE (planner appends new tasks). Off when fixed_plan, or via AGENTIC_REVISE=0.
        if not fixed_plan and _cap("revise", 1) == 1:
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

    # DOMAIN ORACLES (Ω) — task-specific deterministic certifiers, dispatched by the task's DECLARED
    # set only (AGENTIC_DOMAIN_ORACLES: names, or "auto" to select from the query shape). A generic
    # (non-type) task registers none, so the pipeline stays task-agnostic (G3). Oracles are tried in
    # declared order; the first to pin an entity wins, so list stronger certifiers first (ABI before
    # decompiler inference). For type recovery the harness registers "callee_signature,decompiler_pointer".
    oracle_facts: dict = {}                       # entity -> deterministically-certified value
    for _oname, _ofn in G.resolve_domain_oracles(L.cfg_get("domain_oracles", ""), question):
        try:
            for f in _ofn(main_ct, question):
                vid = f["vid"]
                if vid in oracle_facts:           # an earlier (stronger) oracle already pinned it
                    continue
                oracle_facts[vid] = (f["ctype"], _oname, bool(f.get("floor", False)))
                records.append({"finding": {
                    "claim": f["claim"], "confidence": 1.0, "source": f["source"],
                    "evidence_refs": [{"tool": "decompile", "args": {}}]},
                    "verdict": {"consensus": "AGREE", "reason": f["reason"]}})
                print(f"  + {_oname}: {vid} = {f['ctype']}")
        except Exception as e:  # noqa: BLE001
            print(f"  ({_oname} oracle skipped: {str(e)[:80]})")

    _sup = _supersede(records)
    if _sup:
        print(f"  + supersession: dropped {_sup} conflicting verified finding(s) "
              f"(consensus wins on the same entity; recency breaks ties)")
    verified = [r["finding"] for r in records
                if r["verdict"]["consensus"] == "AGREE" and not r.get("_superseded")]

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
    # authoritative per-task conclusions (the planner's own assessed answers) — later tasks last so
    # they win on conflict; synthesis must preserve these rather than re-derive from raw findings.
    task_results = [(t["id"], t["result"]) for t in plan
                    if t.get("status") == "done" and str(t.get("result", "")).strip()]
    with TR.span("synthesize: tiered answer", "CHAIN", f"{len(verified)} verified findings") as _s_out:
        answer = _synthesize(planner, question, verified, suspected, task_results)
        _s_out(answer)
    # A deterministic oracle is ABI-certain, so it is AUTHORITATIVE over the synthesis model's own
    # value for that entity (which can fork under decoding noise, or be dropped by an over-cautious
    # task assessment). Append a machine-readable, oracle-certified trailer that a consumer treats as
    # the top-priority answer for those entities. Task-agnostic: (entity, value) pairs only.
    if oracle_facts:
        # Floor semantics: a "floor" oracle fact (e.g. the runtime probe's representational `void *`)
        # asserts only a lower bound — the entity IS a pointer, pointee unknown. If synthesis already
        # produced a MORE SPECIFIC pointer for that entity, defer to it instead of flattening it; pin
        # the floor only to CORRECT a non-pointer answer. Non-floor facts (precise ABI types) always
        # override, exactly as before. Keeps the mechanism generic — any oracle may mark a fact floor.
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
        lines = []
        for vid, (ctype, _c, _floor) in sorted(oracle_facts.items(), key=lambda kv: kv[0]):
            if _floor and "*" in _synth_ty(vid):     # synthesis has a more specific pointer -> keep it
                print(f"  · floor deferral: {vid} keeps synthesized '{_synth_ty(vid)}' over {ctype}")
                continue
            lines.append(f"- {vid}: {ctype}")
        if lines:
            answer = (answer.rstrip()
                      + "\n\nORACLE-CERTIFIED (deterministic, authoritative — overrides the above):\n"
                      + "\n".join(lines) + "\n")
    TR.note("ANSWER", answer)
    print(f"── TOKENS: {L.USAGE['completion']:,} out / {L.USAGE['prompt']:,} in across "
          f"{L.USAGE['calls']} model calls ──")
    return answer
