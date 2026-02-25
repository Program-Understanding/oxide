"""
Agent runner and evaluation utilities for firmware file-identification tasks.

This plugin can:
- export eval tasks from comp_path/prompt_path,
- run an external agent command for each task,
- evaluate ranks + timing + token usage.
"""

import json
import subprocess
import time
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

from oxide.core import api

NAME = "agent_runner_eval"
DEFAULT_TOP_K_FILES = 100
DEFAULT_COMP_PATH = "fuse_data/openwrt-dataset/fuse_ground_truth.json"
DEFAULT_PROMPT_PATH = "fuse_data/descriptions/component_descriptions.json"
DEFAULT_OUTDIR = "out/agent_eval"
DEFAULT_RUNS_JSONL_CANDIDATES = [
    "out/agent_eval/agent_case_study_runs.jsonl",
    "out/agent_eval/agent_runs.jsonl",
    "out/agent_eval/runs.jsonl",
]
DEFAULT_BASELINE_METHODS = [
    "bm25_tool",
    "dense_tool",
    "func_emb_tool",
    "fuse_tool",
]


def _as_int(value: Any, default: int, *, min_value: Optional[int] = None) -> int:
    try:
        out = int(value)
    except Exception:
        out = int(default)
    if min_value is not None and out < min_value:
        out = min_value
    return out


def _as_bool(value: Any, default: bool = False) -> bool:
    if isinstance(value, bool):
        return value
    if value is None:
        return default
    s = str(value).strip().lower()
    if s in {"1", "true", "yes", "y", "on"}:
        return True
    if s in {"0", "false", "no", "n", "off"}:
        return False
    return default


def _write_artifact(outdir: str, filename: str, payload: Dict[str, Any]) -> Optional[str]:
    outdir = str(outdir or "").strip()
    if not outdir:
        return None
    p = Path(outdir)
    p.mkdir(parents=True, exist_ok=True)
    target = p / filename
    target.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    return str(target)


def _resolve_outdir(opts: Dict[str, Any]) -> str:
    outdir = str(opts.get("outdir", DEFAULT_OUTDIR) or DEFAULT_OUTDIR).strip()
    return outdir or DEFAULT_OUTDIR


def _resolve_runs_jsonl(opts: Dict[str, Any]) -> Tuple[Optional[str], List[str]]:
    explicit = str(opts.get("runs_jsonl", "") or "").strip()
    if explicit:
        return explicit, [explicit]

    outdir = Path(_resolve_outdir(opts))
    candidates: List[str] = []
    for name in (
        "agent_case_study_runs.jsonl",
        "agent_runs.jsonl",
        "runs.jsonl",
    ):
        candidates.append(str(outdir / name))
    for p in DEFAULT_RUNS_JSONL_CANDIDATES:
        if p not in candidates:
            candidates.append(p)

    for p in candidates:
        if Path(p).exists():
            return p, candidates
    return None, candidates


def _filter_executables(oids: List[str]) -> List[str]:
    exes: List[str] = []
    for oid in oids:
        cat = api.get_field("categorize", oid, oid)
        if cat != "executable":
            continue
        names = list(api.get_names_from_oid(oid))
        if any(
            Path(str(n)).name.endswith((".so", ".ko", ".ko.xz"))
            or ".so." in Path(str(n)).name
            or ".ko." in Path(str(n)).name
            for n in names
        ):
            continue
        exes.append(oid)
    return exes


def _build_col_gt(exes: Sequence[str], basename_map: Dict[str, str]) -> Dict[str, str]:
    col_gt: Dict[str, str] = {}
    for oid in exes:
        for name in api.get_names_from_oid(oid):
            base = Path(str(name)).name
            match = next((c for c, f in basename_map.items() if f == base), None)
            if match is not None:
                col_gt[match] = oid
                break
    return col_gt


def _create_ground_truth(comp_path: str) -> Dict[str, Dict[str, str]]:
    data = json.loads(Path(comp_path).read_text(encoding="utf-8"))
    ground_truth: Dict[str, Dict[str, str]] = {}

    cids = api.collection_cids()
    if not cids:
        return {}

    for cid in cids:
        colname = api.get_colname_from_oid(cid)
        if colname not in data:
            continue
        collection_data = data[colname]
        basename_map: Dict[str, str] = {}
        for component, paths in collection_data.items():
            candidates = paths if isinstance(paths, list) else [paths]
            for p in candidates:
                basename_map[component] = Path(str(p)).name

        exes = _filter_executables(list(api.expand_oids(cid)))
        ground_truth[cid] = _build_col_gt(exes, basename_map)

    return ground_truth


def _load_inputs(opts: Dict[str, Any]) -> Tuple[Optional[List[Dict[str, Any]]], Optional[str]]:
    comp_path = str(opts.get("comp_path", DEFAULT_COMP_PATH) or DEFAULT_COMP_PATH).strip()
    prompt_path = str(opts.get("prompt_path", DEFAULT_PROMPT_PATH) or DEFAULT_PROMPT_PATH).strip()
    if not comp_path or not prompt_path:
        return None, (
            "Provide comp_path and prompt_path (or rely on defaults: "
            f"{DEFAULT_COMP_PATH}, {DEFAULT_PROMPT_PATH})."
        )

    try:
        gt = _create_ground_truth(comp_path)
    except Exception as e:
        return None, f"Failed to build ground truth from comp_path='{comp_path}': {e}"

    try:
        prompt_map_raw = json.loads(Path(prompt_path).read_text(encoding="utf-8"))
    except Exception as e:
        return None, f"Failed to load prompt_path='{prompt_path}': {e}"

    if not isinstance(prompt_map_raw, dict):
        return None, "prompt_path must map component -> prompt string."

    prompt_map: Dict[str, str] = {}
    for k, v in prompt_map_raw.items():
        if isinstance(k, str) and isinstance(v, str) and v.strip():
            prompt_map[k] = v.strip()

    tasks: List[Dict[str, Any]] = []
    for cid in sorted(gt.keys(), key=lambda c: api.get_colname_from_oid(c)):
        colname = api.get_colname_from_oid(cid)
        for component, gold_oid in sorted(gt[cid].items(), key=lambda kv: kv[0]):
            prompt = prompt_map.get(component, "")
            if not prompt:
                continue
            tasks.append(
                {
                    "task_id": f"{cid}:{component}",
                    "cid": cid,
                    "collection": colname,
                    "component": component,
                    "prompt": prompt,
                    "gold_oid": gold_oid,
                }
            )

    return tasks, None


def _metrics_from_rank_values(ranks: Sequence[int]) -> Dict[str, float]:
    n = len(ranks)
    if n <= 0:
        return {"P@1": 0.0, "Hit@2": 0.0, "Hit@5": 0.0, "MRR": 0.0, "Mean": 0.0}
    return {
        "P@1": sum(1 for r in ranks if r == 1) / n,
        "Hit@2": sum(1 for r in ranks if r <= 2) / n,
        "Hit@5": sum(1 for r in ranks if r <= 5) / n,
        "MRR": sum((1.0 / r) for r in ranks) / n,
        "Mean": sum(ranks) / n,
    }


def _rank_from_oid_list(oid_list: Sequence[str], gold_oid: str) -> Optional[int]:
    try:
        return list(oid_list).index(gold_oid) + 1
    except ValueError:
        return None


def _parse_agent_json(text: str) -> Dict[str, Any]:
    s = text.strip()
    if not s:
        return {}

    try:
        return json.loads(s)
    except Exception:
        pass

    lines = [ln.strip() for ln in s.splitlines() if ln.strip()]
    for ln in reversed(lines):
        try:
            return json.loads(ln)
        except Exception:
            continue
    return {}


def _extract_ranked_oids(obj: Dict[str, Any]) -> List[str]:
    if not isinstance(obj, dict):
        return []

    direct = obj.get("top_k_oids") or obj.get("ranked_oids")
    if isinstance(direct, list):
        return [str(x) for x in direct if isinstance(x, str) and x]

    cands_direct = obj.get("candidates")
    if isinstance(cands_direct, list):
        out: List[str] = []
        for c in cands_direct:
            if isinstance(c, dict) and isinstance(c.get("oid"), str):
                out.append(c["oid"])
        if out:
            return out

    results = obj.get("results")
    if isinstance(results, dict):
        cands = results.get("candidates")
        if isinstance(cands, list):
            out: List[str] = []
            for c in cands:
                if isinstance(c, dict) and isinstance(c.get("oid"), str):
                    out.append(c["oid"])
            return out

    return []


def _extract_token_usage(obj: Dict[str, Any]) -> Tuple[int, int, int]:
    if not isinstance(obj, dict):
        return 0, 0, 0

    usage = obj.get("usage")
    usage_map: Dict[str, Any] = usage if isinstance(usage, dict) else {}
    prompt_tokens = _as_int(
        obj.get(
            "prompt_tokens",
            usage_map.get(
                "prompt_tokens",
                usage_map.get(
                    "input_tokens",
                    obj.get("prompt_eval_count", obj.get("input_tokens", 0)),
                ),
            ),
        ),
        0,
        min_value=0,
    )
    completion_tokens = _as_int(
        obj.get(
            "completion_tokens",
            usage_map.get(
                "completion_tokens",
                usage_map.get(
                    "output_tokens",
                    obj.get("eval_count", obj.get("output_tokens", 0)),
                ),
            ),
        ),
        0,
        min_value=0,
    )
    total_tokens = _as_int(
        obj.get(
            "total_tokens",
            usage_map.get("total_tokens", prompt_tokens + completion_tokens),
        ),
        prompt_tokens + completion_tokens,
        min_value=0,
    )
    return prompt_tokens, completion_tokens, total_tokens


def _normalize_method_name(value: Any) -> str:
    s = str(value or "").strip().lower()
    if not s:
        return ""
    aliases = {
        "bm25": "bm25_tool",
        "bm25_tool": "bm25_tool",
        "bm25_single": "bm25_tool",
        "bm25_onepass": "bm25_tool",
        "dense": "dense_tool",
        "dense_tool": "dense_tool",
        "func": "func_emb_tool",
        "func_emb": "func_emb_tool",
        "func_emb_tool": "func_emb_tool",
        "function_embeddings": "func_emb_tool",
        "fuse": "fuse_tool",
        "fuse_tool": "fuse_tool",
    }
    return aliases.get(s, s)


def _extract_method_name(obj: Dict[str, Any]) -> str:
    if not isinstance(obj, dict):
        return ""
    for key in ("method", "tool", "toolset", "baseline"):
        v = obj.get(key)
        if isinstance(v, str) and v.strip():
            return _normalize_method_name(v)
    return ""


def _parse_methods_opt(opts: Dict[str, Any]) -> List[str]:
    raw = opts.get("methods")
    if raw is None:
        return list(DEFAULT_BASELINE_METHODS)
    if isinstance(raw, str):
        items = [p.strip() for p in raw.split(",") if p.strip()]
    elif isinstance(raw, (list, tuple)):
        items = [str(x).strip() for x in raw if str(x).strip()]
    else:
        return list(DEFAULT_BASELINE_METHODS)
    out: List[str] = []
    for item in items:
        m = _normalize_method_name(item)
        if m and m not in out:
            out.append(m)
    return out or list(DEFAULT_BASELINE_METHODS)


def _format_cmd(template: str, task: Dict[str, Any], top_k: int) -> str:
    return template.format(
        task_id=task.get("task_id", ""),
        cid=task.get("cid", ""),
        collection=task.get("collection", ""),
        component=task.get("component", ""),
        prompt=task.get("prompt", ""),
        gold_oid=task.get("gold_oid", ""),
        top_k=top_k,
    )


def agent_export_tasks(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Export normalized eval tasks derived from comp_path and prompt_path.
    """
    tasks, err = _load_inputs(opts)
    if err:
        return {"error": err}
    if tasks is None:
        return {"error": "No tasks available."}

    payload = {
        "analysis": "agent_export_tasks",
        "comp_path": str(opts.get("comp_path", DEFAULT_COMP_PATH) or DEFAULT_COMP_PATH),
        "prompt_path": str(opts.get("prompt_path", DEFAULT_PROMPT_PATH) or DEFAULT_PROMPT_PATH),
        "task_count": len(tasks),
        "tasks": tasks,
    }
    artifact = _write_artifact(
        _resolve_outdir(opts), "agent_tasks.json", payload
    )
    if artifact:
        payload["artifact"] = artifact
    return payload


def agent_eval_from_jsonl(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Evaluate pre-recorded agent runs from JSONL.

    Expected per line keys:
      - task_id
      - optional method/tool/toolset (recommended when logs contain >1 baseline)
      - top_k_oids (or ranked_oids)
      - runtime_ms
      - prompt_tokens / completion_tokens / total_tokens (or Ollama equivalents)
    """
    tasks, err = _load_inputs(opts)
    if err:
        return {"error": err}
    if tasks is None:
        return {"error": "No tasks available."}

    run_path, run_candidates = _resolve_runs_jsonl(opts)
    if not run_path:
        return {
            "error": "Provide runs_jsonl.",
            "looked_in": run_candidates,
        }

    try:
        lines = Path(run_path).read_text(encoding="utf-8").splitlines()
    except Exception as e:
        return {"error": f"Failed to read runs_jsonl: {e}"}

    selected_method = _normalize_method_name(opts.get("method", ""))
    by_task: Dict[str, Dict[str, Any]] = {}
    for ln in lines:
        s = ln.strip()
        if not s:
            continue
        try:
            row = json.loads(s)
        except Exception:
            continue
        row_method = _extract_method_name(row)
        if selected_method and row_method and row_method != selected_method:
            continue
        tid = str(row.get("task_id", "") or "").strip()
        if tid:
            by_task[tid] = row

    top_k_files = _as_int(opts.get("top_k_files"), DEFAULT_TOP_K_FILES, min_value=1)
    per_query: List[Dict[str, Any]] = []
    for task in tasks:
        tid = str(task["task_id"])
        row = by_task.get(tid, {})
        ranked = _extract_ranked_oids(row)
        if top_k_files > 0:
            ranked = ranked[:top_k_files]

        rank = _rank_from_oid_list(ranked, str(task["gold_oid"]))
        if rank is None:
            rank = top_k_files + 1

        p_tok, c_tok, t_tok = _extract_token_usage(row)
        runtime_ms = float(row.get("runtime_ms", 0.0) or 0.0)

        per_query.append(
            {
                "task_id": tid,
                "cid": task["cid"],
                "collection": task["collection"],
                "component": task["component"],
                "query": task["prompt"],
                "gold_oid": task["gold_oid"],
                "rank": rank,
                "top_k_oids": ranked,
                "runtime_ms": float(f"{runtime_ms:.3f}"),
                "prompt_tokens": p_tok,
                "completion_tokens": c_tok,
                "total_tokens": t_tok,
            }
        )

    payload = _finalize_eval_payload(
        analysis="agent_eval_from_jsonl",
        per_query=per_query,
        top_k_files=top_k_files,
        outdir=_resolve_outdir(opts),
        artifact_name="agent_eval_from_jsonl.json",
    )
    payload["runs_jsonl"] = run_path
    if selected_method:
        payload["method"] = selected_method
    return payload


def agent_eval_case_study_from_jsonl(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Evaluate multi-baseline agent logs from one JSONL file.

    Expected per line keys:
      - task_id
      - method/tool/toolset (e.g., bm25_tool, dense_tool, func_emb_tool, fuse_tool)
      - top_k_oids (or ranked_oids / results.candidates[].oid)
      - runtime_ms
      - token usage fields (flat or usage.*)
    """
    tasks, err = _load_inputs(opts)
    if err:
        return {"error": err}
    if tasks is None:
        return {"error": "No tasks available."}

    run_path, run_candidates = _resolve_runs_jsonl(opts)
    if not run_path:
        return {
            "error": "Provide runs_jsonl.",
            "looked_in": run_candidates,
        }

    try:
        lines = Path(run_path).read_text(encoding="utf-8").splitlines()
    except Exception as e:
        return {"error": f"Failed to read runs_jsonl: {e}"}

    methods = _parse_methods_opt(opts)
    top_k_files = _as_int(opts.get("top_k_files"), DEFAULT_TOP_K_FILES, min_value=1)
    include_per_query = _as_bool(opts.get("include_per_query"), True)
    reference_method = _normalize_method_name(
        opts.get("reference_method", "fuse_tool")
    )
    if reference_method not in methods:
        reference_method = methods[0] if methods else ""

    by_method_task: Dict[str, Dict[str, Dict[str, Any]]] = defaultdict(dict)
    unknown_method_rows = 0
    rows_missing_method = 0
    parsed_rows = 0
    for ln in lines:
        s = ln.strip()
        if not s:
            continue
        try:
            row = json.loads(s)
        except Exception:
            continue
        parsed_rows += 1
        method = _extract_method_name(row)
        if not method:
            rows_missing_method += 1
            continue
        if method not in methods:
            unknown_method_rows += 1
            continue
        tid = str(row.get("task_id", "") or "").strip()
        if tid:
            by_method_task[method][tid] = row

    method_results: Dict[str, Any] = {}
    summary_rows: List[Dict[str, Any]] = []
    for method in methods:
        by_task = by_method_task.get(method, {})
        per_query: List[Dict[str, Any]] = []
        for task in tasks:
            tid = str(task["task_id"])
            row = by_task.get(tid, {})
            ranked = _extract_ranked_oids(row)
            if top_k_files > 0:
                ranked = ranked[:top_k_files]

            rank = _rank_from_oid_list(ranked, str(task["gold_oid"]))
            if rank is None:
                rank = top_k_files + 1

            p_tok, c_tok, t_tok = _extract_token_usage(row)
            runtime_ms = float(row.get("runtime_ms", 0.0) or 0.0)

            per_query.append(
                {
                    "task_id": tid,
                    "cid": task["cid"],
                    "collection": task["collection"],
                    "component": task["component"],
                    "query": task["prompt"],
                    "gold_oid": task["gold_oid"],
                    "rank": rank,
                    "top_k_oids": ranked,
                    "runtime_ms": float(f"{runtime_ms:.3f}"),
                    "prompt_tokens": p_tok,
                    "completion_tokens": c_tok,
                    "total_tokens": t_tok,
                    "missing_row": tid not in by_task,
                }
            )

        res = _finalize_eval_payload(
            analysis="agent_eval_case_study_from_jsonl",
            per_query=per_query,
            top_k_files=top_k_files,
            outdir="",
            artifact_name="",
        )
        if not include_per_query:
            res.pop("per_query", None)
        method_results[method] = res
        gm = res.get("global_metrics", {}) if isinstance(res, dict) else {}
        timing = res.get("timing", {}) if isinstance(res, dict) else {}
        usage = res.get("usage", {}) if isinstance(res, dict) else {}
        summary_rows.append(
            {
                "method": method,
                "attempted_queries": int(res.get("attempted_queries", 0) or 0),
                "MRR": float(gm.get("MRR", 0.0) or 0.0),
                "P@1": float(gm.get("P@1", 0.0) or 0.0),
                "Hit@2": float(gm.get("Hit@2", 0.0) or 0.0),
                "Hit@5": float(gm.get("Hit@5", 0.0) or 0.0),
                "Mean": float(gm.get("Mean", 0.0) or 0.0),
                "query_time_ms_avg": float(timing.get("query_time_ms_avg", 0.0) or 0.0),
                "tokens_per_query_avg": float(usage.get("tokens_per_query_avg", 0.0) or 0.0),
            }
        )

    summary_rows.sort(key=lambda r: (-r["MRR"], r["method"]))
    ref_summary = next((r for r in summary_rows if r["method"] == reference_method), None)
    pairwise_vs_reference: List[Dict[str, Any]] = []
    for row in summary_rows:
        if ref_summary is None:
            break
        pairwise_vs_reference.append(
            {
                "method": row["method"],
                "reference_method": reference_method,
                "delta_MRR": float(f"{(row['MRR'] - ref_summary['MRR']):.6f}"),
                "delta_P@1": float(f"{(row['P@1'] - ref_summary['P@1']):.6f}"),
                "delta_Hit@5": float(f"{(row['Hit@5'] - ref_summary['Hit@5']):.6f}"),
                "delta_Mean": float(f"{(row['Mean'] - ref_summary['Mean']):.6f}"),
            }
        )

    payload: Dict[str, Any] = {
        "analysis": "agent_eval_case_study_from_jsonl",
        "runs_jsonl": run_path,
        "methods": methods,
        "reference_method": reference_method,
        "top_k_files": top_k_files,
        "task_count": len(tasks),
        "parsed_rows": parsed_rows,
        "rows_missing_method": rows_missing_method,
        "unknown_method_rows": unknown_method_rows,
        "summary": summary_rows,
        "pairwise_vs_reference": pairwise_vs_reference,
        "method_results": method_results,
    }
    artifact = _write_artifact(
        _resolve_outdir(opts),
        "agent_case_study_eval.json",
        payload,
    )
    if artifact:
        payload["artifact"] = artifact
    return payload


def agent_run_and_eval(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Run an external agent command per task and evaluate.

    Required option:
      - agent_cmd_template: shell command with placeholders:
        {task_id} {cid} {collection} {component} {prompt} {gold_oid} {top_k}

    The command must print JSON containing at least ranked OIDs via one of:
      - top_k_oids: [oid, ...]
      - ranked_oids: [oid, ...]
      - results.candidates: [{"oid": ...}, ...]
    """
    tasks, err = _load_inputs(opts)
    if err:
        return {"error": err}
    if tasks is None:
        return {"error": "No tasks available."}

    template = str(opts.get("agent_cmd_template", "") or "").strip()
    if not template:
        return {"error": "Provide agent_cmd_template."}

    max_tasks = _as_int(opts.get("max_tasks"), 0, min_value=0)
    timeout_s = _as_int(opts.get("timeout_s"), 180, min_value=1)
    top_k_files = _as_int(opts.get("top_k_files"), DEFAULT_TOP_K_FILES, min_value=1)
    stop_on_error = _as_bool(opts.get("stop_on_error"), False)

    selected = tasks[:max_tasks] if max_tasks > 0 else tasks
    per_query: List[Dict[str, Any]] = []
    errors: List[Dict[str, Any]] = []

    for task in selected:
        cmd = _format_cmd(template, task, top_k_files)
        t0 = time.perf_counter_ns()
        try:
            proc = subprocess.run(
                cmd,
                shell=True,
                check=False,
                text=True,
                capture_output=True,
                timeout=timeout_s,
            )
            elapsed_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        except Exception as e:
            errors.append({"task_id": task["task_id"], "error": str(e)})
            if stop_on_error:
                return {"error": f"Agent run failed: {e}", "errors": errors}
            continue

        parsed = _parse_agent_json(proc.stdout or "")
        ranked = _extract_ranked_oids(parsed)
        if top_k_files > 0:
            ranked = ranked[:top_k_files]

        rank = _rank_from_oid_list(ranked, str(task["gold_oid"]))
        if rank is None:
            rank = top_k_files + 1

        p_tok, c_tok, t_tok = _extract_token_usage(parsed)
        runtime_ms = float(parsed.get("runtime_ms", elapsed_ms) or elapsed_ms)

        row = {
            "task_id": task["task_id"],
            "cid": task["cid"],
            "collection": task["collection"],
            "component": task["component"],
            "query": task["prompt"],
            "gold_oid": task["gold_oid"],
            "rank": rank,
            "top_k_oids": ranked,
            "runtime_ms": float(f"{runtime_ms:.3f}"),
            "prompt_tokens": p_tok,
            "completion_tokens": c_tok,
            "total_tokens": t_tok,
            "exit_code": int(proc.returncode),
        }
        per_query.append(row)

        if proc.returncode != 0:
            errors.append(
                {
                    "task_id": task["task_id"],
                    "error": "Non-zero exit code",
                    "exit_code": int(proc.returncode),
                    "stderr": (proc.stderr or "")[-2000:],
                }
            )
            if stop_on_error:
                break

    payload = _finalize_eval_payload(
        analysis="agent_run_and_eval",
        per_query=per_query,
        top_k_files=top_k_files,
        outdir=_resolve_outdir(opts),
        artifact_name="agent_run_eval.json",
    )
    if errors:
        payload["errors"] = errors
    payload["executed_tasks"] = len(selected)
    payload["completed_tasks"] = len(per_query)
    return payload


def _finalize_eval_payload(
    *,
    analysis: str,
    per_query: List[Dict[str, Any]],
    top_k_files: int,
    outdir: str,
    artifact_name: str,
) -> Dict[str, Any]:
    ranks = [int(q.get("rank", top_k_files + 1)) for q in per_query]
    metrics = _metrics_from_rank_values(ranks)

    total_runtime_ms = sum(float(q.get("runtime_ms", 0.0) or 0.0) for q in per_query)
    total_prompt_tokens = sum(int(q.get("prompt_tokens", 0) or 0) for q in per_query)
    total_completion_tokens = sum(
        int(q.get("completion_tokens", 0) or 0) for q in per_query
    )
    total_tokens = sum(int(q.get("total_tokens", 0) or 0) for q in per_query)

    per_collection_ranks: Dict[str, List[int]] = defaultdict(list)
    for q in per_query:
        per_collection_ranks[str(q.get("collection", ""))].append(int(q.get("rank", top_k_files + 1)))

    per_collection: Dict[str, Any] = {}
    for colname, col_ranks in per_collection_ranks.items():
        per_collection[colname] = {
            "attempted_queries": len(col_ranks),
            "metrics": _metrics_from_rank_values(col_ranks),
        }

    payload: Dict[str, Any] = {
        "analysis": analysis,
        "top_k_files": top_k_files,
        "attempted_queries": len(per_query),
        "global_metrics": metrics,
        "timing": {
            "query_time_ms_total": float(f"{total_runtime_ms:.3f}"),
            "query_time_ms_avg": float(f"{(total_runtime_ms / max(len(per_query), 1)):.3f}"),
        },
        "usage": {
            "prompt_tokens_total": total_prompt_tokens,
            "completion_tokens_total": total_completion_tokens,
            "total_tokens": total_tokens,
            "tokens_per_query_avg": float(f"{(total_tokens / max(len(per_query), 1)):.3f}"),
        },
        "per_collection": per_collection,
        "per_query": per_query,
    }

    artifact = _write_artifact(outdir, artifact_name, payload)
    if artifact:
        payload["artifact"] = artifact
    return payload


exports = [
    agent_export_tasks,
    agent_eval_from_jsonl,
    agent_eval_case_study_from_jsonl,
    agent_run_and_eval,
]
