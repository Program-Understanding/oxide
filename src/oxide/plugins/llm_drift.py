from __future__ import annotations

import json
import logging
import os
import re
import unicodedata
import time
from typing import Any, Dict, List, Optional, Tuple

from langchain_core.messages import HumanMessage, SystemMessage
from langchain_ollama import ChatOllama

from oxide.plugins.drift import compare_collections
from oxide.core import oxide as oxide

# --------------------------------------------------------------------------------------
# Logging
# --------------------------------------------------------------------------------------
NAME = "llm_drift"
logger = logging.getLogger(NAME)
if not logger.handlers:
    _h = logging.StreamHandler()
    _fmt = logging.Formatter("[%(asctime)s] %(levelname)s %(name)s: %(message)s", "%H:%M:%S")
    _h.setFormatter(_fmt)
    logger.addHandler(_h)
logger.setLevel(logging.INFO)

# --------------------------------------------------------------------------------------
# LLM config — keep a single instance
# --------------------------------------------------------------------------------------
LLM = ChatOllama(model="gpt-oss:20b", temperature=0.0, num_ctx=8192, keep_alive="10m")
logger.info("LLM ready: gpt-oss:20b (ctx=8192)")

ANALYST_SYS = (
    "You are an expert reverse engineer.\n"
    "Input is a unified diff of the decompiled C for ONE function (baseline vs target).\n\n"
    "TASK:\n"
    "Identify whether the modification adds a malicious backdoor or logic bomb.\n"
    "If it does, identify the specific condition in which the backdoor or logic bomb triggers.\n"
    "Output EXACT JSON ONLY:\n"
    "{\n"
    '  "label": "not_safe" | "safe",\n'
    '  "why": "1-3 sentences citing the specific + line(s) and the control/data-flow change"\n'
    "}\n"
)


def llm_filter(args: List[str], opts: Dict[str, Any]) -> None:
    """Run triage across a single target→baseline pair or a whole series.

    Expected calling patterns:
      • llm_filter([target, baseline], opts)
      • llm_filter([], {"series-file": path, ...}) with a plaintext file of CIDs/names
    """
    # --- determine pairs (target→baseline) ---
    pairs: List[Tuple[str, str]]
    series_file: Optional[str] = opts.get("entries")

    if series_file:
        versions = read_series_file(series_file)
        if len(versions) < 2:
            raise ValueError("series-file must list at least two versions (one per line)")
        # v[i] is newer target; v[i-1] is baseline
        pairs = [(versions[i], versions[i - 1]) for i in range(1, len(versions))]
        logger.info(f"Loaded {len(versions)} versions; constructed {len(pairs)} comparisons (target→baseline).")
    elif len(args) == 2:
        pairs = [(args[0], args[1])]
        logger.info(f"Single comparison: {args[0]} → {args[1]}")
    else:
        raise ValueError("Pass either [target, baseline] or --series-file with at least two lines.")

    annotate: bool = bool(opts.get("annotate", True))
    filter = opts.get("filter", None)
    outdir: str = opts.get("outdir", "./out_firmware_simple")

    makedirs(outdir)
    logger.info(f"Output directory: {outdir}")

    # ---- Cross-comparison aggregation ----
    comparison_rows: List[Dict[str, Any]] = []
    per_function_rows: List[Dict[str, Any]] = []

    total_pairs = len(pairs)
    logger.info(f"Starting {total_pairs} comparison(s)…")

    for idx, (target, baseline) in enumerate(pairs, 1):
        try:
            t_name = oxide.api.get_colname_from_oid(target)
        except Exception:
            t_name = str(target)
        try:
            b_name = oxide.api.get_colname_from_oid(baseline)
        except Exception:
            b_name = str(baseline)

        logger.info(f"[{idx}/{total_pairs}] {t_name} → {b_name}")
        pair_dir_name = f"cmp_{idx:03d}__{t_name}_to_{b_name}"
        pair_dir = os.path.join(outdir, pair_dir_name)

        res = run_one_comparison(target, baseline, pair_dir, annotate, filter)
        stats = res["stats"]

        comparison_rows.append({
            "index": idx,
            "target": target,
            "baseline": baseline,
            "pair_dir": pair_dir,
            **stats,
        })

        # Per-function rows (one observation per modified function in this comparison)
        file_pairs = res.get("file_pairs") or []
        flagged_lookup = {(ti["filepair_index"], ti["function_index"]) for ti in res.get("triage_index", [])}

        for fp_idx, fp in enumerate(file_pairs, 1):
            baseline_oid = fp.get("baseline_oid")
            target_oid = fp.get("target_oid")
            modified = fp.get("modified_functions", []) or []
            for func_idx, m in enumerate(modified, 1):
                baddr = ensure_decimal_str(m.get("baseline_func_addr"))
                taddr = ensure_decimal_str(m.get("target_func_addr"))
                key = f"pair{idx}_fp{fp_idx}_func{func_idx}"
                flagged = (fp_idx, func_idx) in flagged_lookup
                per_function_rows.append({
                    "key": key,
                    "comparison_index": idx,
                    "target_version": target,
                    "baseline_version": baseline,
                    "filepair_index": fp_idx,
                    "function_index": func_idx,
                    "target_addr": taddr,
                    "baseline_addr": baddr,
                    "target_oid": target_oid,
                    "baseline_oid": baseline_oid,
                    "flagged": bool(flagged),
                    "flagged_rate": 1.0 if flagged else 0.0,
                })

    # ---- Write cross-comparison summaries ----
    logger.info("Writing cross-comparison summaries…")

    # filtered-level sums
    agg_filtered_total = sum(r.get("total_modified_functions_filtered", 0) for r in comparison_rows)
    agg_filtered_flagged = sum(r.get("flagged_not_safe_filtered", 0) for r in comparison_rows)
    agg_filtered_safe = sum(r.get("safe_filtered", 0) for r in comparison_rows)

    # all-level sums
    agg_all_total = sum(r.get("total_modified_functions_all", 0) for r in comparison_rows)
    agg_all_safe = sum(r.get("safe_overall", 0) for r in comparison_rows)

    aggregate = {
        "comparisons": len(comparison_rows),
        "annotate": annotate,
        "filter": filter,
        # filtered-only metrics
        "total_modified_functions_filtered": agg_filtered_total,
        "flagged_filtered": agg_filtered_flagged,
        "safe_filtered": agg_filtered_safe,
        "flagged_rate_filtered": (agg_filtered_flagged / agg_filtered_total) if agg_filtered_total else 0.0,
        "safe_rate_filtered": (agg_filtered_safe / agg_filtered_total) if agg_filtered_total else 0.0,
        # overall metrics (all drift-modified)
        "total_modified_functions_all": agg_all_total,
        "safe_overall": agg_all_safe,
        "safe_rate_overall": (agg_all_safe / agg_all_total) if agg_all_total else 0.0,
        "flagged_rate_overall": (agg_filtered_flagged / agg_all_total) if agg_all_total else 0.0,
    }

    series_summary = {"comparisons": comparison_rows, "aggregate": aggregate}

    write_json(os.path.join(outdir, "comparisons_summary.json"), series_summary)
    write_json(os.path.join(outdir, "per_function_summary.json"), {"functions": per_function_rows})
    logger.info("✓ Summaries written (comparisons_summary.json, per_function_summary.json). ")
    return series_summary


# keep plugin export shape
exports = [llm_filter]


# --------------------------------------------------------------------------------------
# Core pipeline
# --------------------------------------------------------------------------------------

def run_one_comparison(target: str, baseline: str, outdir: str, annotate: bool, filter: str) -> Dict[str, Any]:
    makedirs(outdir)
    logger.info(f"→ Invoking drift (target='{target}', baseline='{baseline}')")
    t0 = time.perf_counter()

    drift_res = run_drift(target, baseline, filter)
    drift_json = coerce_json_like(getattr(drift_res, "content", drift_res)) or {}
    write_json(os.path.join(outdir, "drift_raw.json"), dump_json_safe(drift_json))

    file_pairs: List[Dict[str, Any]] = drift_json.get("file_pairs", []) or []

    report_lines: List[str] = []
    report_lines.append(f"# Firmware Triage Report (binary suspicion)")
    report_lines.append(f"Target CID:   {target}")
    try:
        report_lines.append(f"Target Name:  {oxide.api.get_colname_from_oid(target)}")
    except Exception:
        report_lines.append("Target Name:  <unavailable>")
    report_lines.append(f"Baseline CID: {baseline}")
    try:
        report_lines.append(f"Baseline Name:{oxide.api.get_colname_from_oid(baseline)}")
    except Exception:
        report_lines.append("Baseline Name:<unavailable>")
    if filter:
        report_lines.append(f"Filter:       {filter}")
    report_lines.append("")

    triage_index: List[Dict[str, Any]] = []

    # NEW: we track both “all modified” and “filtered modified”
    total_modified_all = 0              # every function drift said was modified
    total_modified_filtered = 0         # only the ones we actually ran through LLM
    n_flagged_filtered = 0
    n_safe_filtered = 0

    if not file_pairs:
        report_lines.append("No file pairs or modifications were reported by drift.")
        logger.info("• No file pairs / modifications.")
    else:
        report_lines.append(f"Found {len(file_pairs)} file pair(s).\n")
        logger.info(f"• Processing {len(file_pairs)} file pair(s)…")

    for fp_idx, fp in enumerate(file_pairs, 1):
        baseline_oid = fp.get("baseline_oid")
        target_oid = fp.get("target_oid")
        filtered_mods = fp.get("modified_functions", [])
        excluded_mods = fp.get("excluded_functions", [])

        # count all drift-reported modifications (filtered + excluded)
        total_modified_all += len(filtered_mods) + len(excluded_mods)
        total_modified_filtered += len(filtered_mods)

        report_lines.append(f"## File Pair {fp_idx}")
        report_lines.append(f"- target_oid:   {target_oid}")
        report_lines.append(f"- baseline_oid: {baseline_oid}")
        report_lines.append(f"- modified functions (filtered): {len(filtered_mods)}")
        if excluded_mods:
            report_lines.append(f"- modified functions (excluded by filter): {len(excluded_mods)}")
        report_lines.append("")
        logger.info(
            f"   [fp {fp_idx}/{len(file_pairs)}] filtered={len(filtered_mods)}, "
            f"excluded={len(excluded_mods)}"
        )

        # only filtered_mods go to the LLM
        for func_idx, m in enumerate(filtered_mods, 1):
            features = m.get("features") or {}
            baddr = ensure_decimal_str(m.get("baseline_func_addr"))
            taddr = ensure_decimal_str(m.get("target_func_addr"))

            res = analyze_function_pair(
                baseline_oid, target_oid, baddr, taddr, features,
                annotate, outdir, fp_idx, func_idx
            )

            if res["flagged"]:
                n_flagged_filtered += 1
                triage_index.append({
                    "filepair_index": fp_idx,
                    "function_index": func_idx,
                    "baseline_addr": baddr,
                    "target_addr": taddr,
                    "label": res["label"],
                    "why": res["why"],
                    "verdict": res["verdict"],
                    "dir": res["func_dir"],
                    "baseline_oid": baseline_oid,
                    "target_oid": target_oid,
                    "flagged": res["flagged"],
                })
            else:
                n_safe_filtered += 1

            logger.info(f"      functions processed: {func_idx}/{len(filtered_mods)}")

        logger.info(f"   [fp {fp_idx}] done")

    # rates for filtered functions
    filtered_flagged_rate = (
        n_flagged_filtered / total_modified_filtered
        if total_modified_filtered else 0.0
    )
    filtered_safe_rate = (
        n_safe_filtered / total_modified_filtered
        if total_modified_filtered else 0.0
    )

    # overall: everything drift said was modified
    # we did not LLM the excluded funcs, so we count them as “implicitly safe”
    overall_safe = n_safe_filtered + (total_modified_all - total_modified_filtered)
    overall_safe_rate = (
        overall_safe / total_modified_all
        if total_modified_all else 0.0
    )

    dt = time.perf_counter() - t0
    logger.info(
        f"Drift + triage finished in {dt:.1f}s: "
        f"all_modified={total_modified_all}, filtered={total_modified_filtered}, "
        f"flagged_filtered={n_flagged_filtered}, safe_filtered={n_safe_filtered}"
    )

    report_lines.append("")
    report_lines.append("## Summary statistics")
    report_lines.append(f"- Total modified functions (ALL): {total_modified_all}")
    report_lines.append(f"- Total modified functions (FILTERED): {total_modified_filtered}")
    report_lines.append(f"- Flagged (filtered): {n_flagged_filtered} ({filtered_flagged_rate:.2%})")
    report_lines.append(f"- Safe (filtered): {n_safe_filtered} ({filtered_safe_rate:.2%})")
    if total_modified_all != total_modified_filtered:
        report_lines.append(
            f"- Overall safe rate (assuming excluded functions are safe): {overall_safe_rate:.2%}"
        )

    stats = {
        "target": target,
        "baseline": baseline,
        # all drift mods
        "total_modified_functions_all": total_modified_all,
        "safe_overall": overall_safe,
        "safe_rate_overall": overall_safe_rate,
        # filtered-only (the LLM work)
        "total_modified_functions_filtered": total_modified_filtered,
        "flagged_not_safe_filtered": n_flagged_filtered,
        "safe_filtered": n_safe_filtered,
        "flagged_rate_filtered": filtered_flagged_rate,
        "safe_rate_filtered": filtered_safe_rate,
    }

    write_text(os.path.join(outdir, "final_report.txt"), "\n".join(report_lines))
    write_json(os.path.join(outdir, "triage_index.json"), triage_index)
    write_json(os.path.join(outdir, "stats.json"), stats)
    logger.info(
        f"✓ Wrote reports to {outdir} "
        f"(all={total_modified_all}, filtered={total_modified_filtered}, "
        f"flagged={n_flagged_filtered}, safe={n_safe_filtered})"
    )

    return {
        "target": target,
        "baseline": baseline,
        "stats": stats,
        "triage_index": triage_index,
        "file_pairs": file_pairs,
    }



def analyze_function_pair(
    baseline_oid: str,
    target_oid: str,
    baddr: str,
    taddr: str,
    features: Dict[str, Any],
    annotate: bool,
    out_dir: str,
    fp_idx: int,
    func_idx: int,
) -> Dict[str, Any]:
    func_dir = os.path.join(out_dir, f"filepair_{fp_idx:02d}", f"func_{func_idx:02d}__b{baddr}__t{taddr}")
    makedirs(func_dir)

    notes_path = os.path.join(func_dir, "notes.json")
    notes: Dict[str, Any] = {"observations": [], "artifacts": []}

    diff_raw = oxide.retrieve(
        "function_decomp_diff",
        [target_oid, baseline_oid],
        {"target": taddr, "baseline": baddr, "annotate": annotate},
    )

    # NOTE: This fails because there is a mismatch in funcs provided my ghidra_disasm and bindiff. Need to figure out how to handle it
    if isinstance(diff_raw, dict) and "error" in diff_raw:
        notes["observations"].append("diff tool failed")
        # Save and return safe verdict if we can't diff
        write_json(notes_path, notes)
        write_text(os.path.join(func_dir, "diff.txt"), "")
        verdict = "Label: safe — no diff available (tool error)"
        write_json(os.path.join(func_dir, "analysis.json"),
                   {"label": "safe", "why": "no diff available", "flagged": False, "verdict": verdict})
        write_text(os.path.join(func_dir, "verdict.txt"), verdict)
        return {"label": "safe", "why": "no diff available", "flagged": False,
                "verdict": verdict, "func_dir": func_dir}

    diff_text = extract_content(diff_raw) or ""
    write_text(os.path.join(func_dir, "diff.txt"), diff_text)

    unified = ""
    parsed = coerce_json_like(diff_text)
    if isinstance(parsed, dict) and "unified" in parsed:
        unified = parsed.get("unified") or ""
    else:
        unified = diff_text

    # Defaults
    label = "safe"
    why = ""
    flagged = False
    verdict = "Label: safe — model provided no reason"

    # 2) LLM triage (binary)
    if unified.strip():
        # Prepare combined user content with features at top
        features_text = json.dumps(features, indent=2, ensure_ascii=False)
        # user_content = (
        #     "FUNCTION FEATURES:\n" f"{features_text}\n\n" "FUNCTION UNIFIED DIFF:\n\n" f"{ascii_sanitize(unified)}"
        # )
        user_content = (
            "FUNCTION UNIFIED DIFF:\n\n" f"{ascii_sanitize(unified)}"
        )

        # Use sync .invoke to avoid async misuse
        try:
            resp = LLM.invoke([SystemMessage(content=ANALYST_SYS), HumanMessage(content=user_content)])
            text = ascii_sanitize((getattr(resp, "content", "") or "").strip())
        except Exception as e:
            notes["observations"].append(f"LLM error: {e}")
            text = ""

        data = parse_llm_json(text)
        if isinstance(data, dict):
            label_raw = (str(data.get("label", "safe"))).strip().lower().replace("-", "_")
            label = label_raw if label_raw in ("safe", "not_safe") else "safe"
            why = (data.get("why") or "").strip()

    flagged = (label == "not_safe")
    verdict = f"Label: {'needs further inspection' if flagged else 'safe'} — {why or 'model provided no reason'}"

    # Save outputs
    write_json(notes_path, notes)
    write_json(os.path.join(func_dir, "analysis.json"),
               {"label": label, "why": why, "flagged": flagged, "verdict": verdict})
    write_text(os.path.join(func_dir, "verdict.txt"), verdict)

    return {"label": label, "why": why, "flagged": flagged, "verdict": verdict, "func_dir": func_dir}


# --------------------------------------------------------------------------------------
# Drift helpers
# --------------------------------------------------------------------------------------

def run_drift(target_cid: str, baseline_cid: str, filter: str = None) -> Dict[str, Any]:
    out: Dict[str, Any] = {"file_pairs": []}
    try:
        if filter:
            drift = compare_collections([target_cid, baseline_cid], {"filter": filter}) or {}
        else:
            drift = compare_collections([target_cid, baseline_cid], {}) or {}
    except Exception as e:
        logger.error(f"compare_collections failed: {e}")
        return out

    per_file = (drift.get("FUNCTION_CLASSIFICATION", {}) or {}).get("PER_FILE", {}) or {}

    for file_key, file_entry in per_file.items():
        # file_key shape is (target_oid, baseline_oid) by Oxide convention in this view
        if not isinstance(file_key, (tuple, list)) or len(file_key) != 2:
            continue
        target_oid, baseline_oid = file_key[0], file_key[1]

        if filter:
            search_space = file_entry.get(filter)
            excluded_functions = file_entry.get("modified")
        else:
            search_space = file_entry.get("modified")
            excluded_functions = {}

        search_space_out: List[Dict[str, Any]] = []

        for m in search_space:
            feats = m.get("features", {}) if isinstance(m, dict) else {}

            # The drift “pair” gives (target_addr, baseline_addr) (by convention here).
            pair = m.get("pair", [None, None])
            t_addr_str = _dec_str(pair[0]) if pair and len(pair) > 0 else None
            b_addr_str = _dec_str(pair[1]) if pair and len(pair) > 1 else None

            search_space_out.append({
                "baseline_func_addr": b_addr_str,
                "target_func_addr": t_addr_str,
                "features": {
                    "# of Added Assembly Instructions": feats.get("added_instr"),
                    "# of Removed Assembly Instructions": feats.get("removed_instr"),
                    "+/- # of Control-Flow Graph Nodes": feats.get("bb_nodes"),
                    "+/- # of Control-Flow Graph Edges": feats.get("bb_edges"),
                    "+/- # of Added Function Calls to Existing Code": feats.get("fc_add_existing"),
                    "+/- # of Added Function Calls to New Code": feats.get("fc_add_new"),
                    "+/- # of Removed Function Calls to Removed Code": feats.get("fc_removed_deleted"),
                    "+/- # of Removed Function Calls to Existing Code": feats.get("fc_removed_existing"),
                },
            })

        out["file_pairs"].append({
            "baseline_oid": baseline_oid,
            "target_oid": target_oid,
            "modified_functions": search_space_out,
            "excluded_functions": excluded_functions
        })

    return out


# --------------------------------------------------------------------------------------
# Utilities
# --------------------------------------------------------------------------------------

def read_series_file(path: str) -> List[str]:
    with open(path, "r", encoding="utf-8") as f:
        lines = [ln.strip() for ln in f.readlines()]
    return [oxide.api.get_cid_from_name(ln) for ln in lines if ln and not ln.startswith("#")]


def makedirs(p: str) -> None:
    os.makedirs(p, exist_ok=True)

def write_text(path: str, text: str) -> None:
    with open(path, "w", encoding="utf-8") as f:
        f.write(text if text is not None else "")


def write_json(path: str, data: Any) -> None:
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)


def read_json(path: str) -> Any:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def ensure_decimal_str(addr: Any) -> str:
    if isinstance(addr, int):
        return str(addr)
    if isinstance(addr, str):
        s = addr.strip().lower()
        if s.startswith("0x"):
            try:
                return str(int(s, 16))
            except Exception:
                return s
        if re.fullmatch(r"\d+", s):
            return s
    try:
        return str(int(addr))
    except Exception:
        return str(addr)


def dump_json_safe(x: Any) -> Any:
    try:
        json.dumps(x)
        return x
    except Exception:
        return str(x)


def _extract_first_balanced_json_object(s: str) -> Optional[dict]:
    """Return the first top-level {...} JSON object parsed with brace counting."""
    start = s.find("{")
    if start == -1:
        return None
    depth = 0
    for i in range(start, len(s)):
        ch = s[i]
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                blob = s[start : i + 1]
                try:
                    return json.loads(blob)
                except Exception:
                    return None
    return None


def coerce_json_like(x: Any) -> Optional[dict]:
    """Return JSON/dict if `x` is JSON or JSON-like text (grabs first balanced {...})."""
    if isinstance(x, dict):
        return x
    if isinstance(x, str):
        try:
            return json.loads(x)
        except Exception:
            pass
        # try balanced object extraction
        return _extract_first_balanced_json_object(x)
    return None


def extract_content(resp: Any) -> Optional[str]:
    """Best-effort to get textual payload from a tool response."""
    data = getattr(resp, "content", resp)
    if data is None or data is False:
        return None
    if isinstance(data, str):
        s = data.strip()
        if not s or s.lower() in ("false", "null", "none", "{}", "[]"):
            return None
        return s
    if isinstance(data, (list, dict)):
        try:
            s = json.dumps(data, ensure_ascii=False)
        except Exception:
            return None
        s = (s or "").strip()
        if not s or s in ("{}", "[]"):
            return None
        return s
    try:
        s = str(data).strip()
    except Exception:
        return None
    return s or None


_ASCII_MAP = {
    ord("–"): "-",
    ord("—"): "-",
    ord("…"): "...",
    ord("“"): '"',
    ord("”"): '"',
    ord("‘"): "'",
    ord("’"): "'",
    ord("\u00A0"): 32,
    ord("\u202F"): 32,
}


def ascii_sanitize(s: str) -> str:
    return unicodedata.normalize("NFKC", s).translate(_ASCII_MAP)


def parse_llm_json(text: str) -> Optional[dict]:
    """Parse model output which *should* be JSON but sometimes isn't.

    Strategy: json.loads → balanced-object extraction → return None.
    """
    if not text:
        return None
    try:
        return json.loads(text)
    except Exception:
        pass
    return _extract_first_balanced_json_object(text)


def _dec_str(v: Any) -> Optional[str]:
    """Return a decimal string for an int or decimal-string input; else None."""
    if isinstance(v, int):
        return str(v)
    if isinstance(v, str):
        s = v.strip()
        try:
            return str(int(s, 10))
        except Exception:
            return None
    return None
