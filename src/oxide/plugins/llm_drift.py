import json
import logging
import os
import re
import unicodedata
import time
from typing import Any, Dict, List, Optional, Tuple

from typing_extensions import TypedDict
from langgraph.graph import StateGraph, START, END

from langchain_core.messages import HumanMessage, SystemMessage
from langchain_ollama import ChatOllama
from IPython.display import Image, display

from oxide.plugins.drift import compare_collections
from oxide.core import oxide as oxide

# --------------------------------------------------------------------------------------
# Logging
# --------------------------------------------------------------------------------------
NAME = "llm_drift"
logger = logging.getLogger(NAME)
if not logger.handlers:
    _h = logging.StreamHandler()
    _fmt = logging.Formatter(
        "[%(asctime)s] %(levelname)s %(name)s: %(message)s", "%H:%M:%S"
    )
    _h.setFormatter(_fmt)
    logger.addHandler(_h)
logger.setLevel(logging.INFO)

# --------------------------------------------------------------------------------------
# LLM config — keep a single instance
# --------------------------------------------------------------------------------------
LLM = ChatOllama(
    model="gpt-oss:20b",
    temperature=0.0,
    num_ctx=8192,
    keep_alive="10m",
    request_timeout=60.0,
    model_kwargs={"num_predict": 128},
)
FORMAT_LLM = ChatOllama(model="llama3.1:8b-instruct-q4_K_M", temperature=0.5)
NORMALIZE_LLM = ChatOllama(model="llama3.1:8b-instruct-q4_K_M", temperature=0.0)
# Second-stage skeptic / reviewer model
SKEPTIC_LLM = ChatOllama(
    model="gpt-oss:20b",
    temperature=0.0,
    num_ctx=8192,
    keep_alive="10m",
    request_timeout=60.0,
    model_kwargs={"num_predict": 128},
)


logger.info("LLM ready: gpt-oss:20b (ctx=8192)")

# Warm-up the main model so first call isn't slow
try:
    resp = LLM.invoke("Warm up.")
    logger.info("LLM warm-up complete.")
except Exception as e:
    logger.warning(f"Warm-up failed: {e}")

ANALYST_SYS = (
    "You are an expert reverse engineer analyzing code that is expected to be safe.\n"
    "Input is a unified diff of the decompiled C for ONE function (baseline vs target).\n\n"
    "TASK:\n"
    "Decide if the change introduces a malicious backdoor or logic bomb in THIS function.\n"
    'Only label it "not_safe" if you can state a concrete condition over inputs or state\n'
    "that triggers newly introduced alternate functionality, based solely on conditions\n"
    "visible in the diff.\n"
    "You must explicitly quote the triggering condition from the diff in the `trigger`\n"
    "field by copying the exact new comparison or conditional expression (for example,\n"
    "`if (buf[i] == ':' && buf[i+1] == ')')` or `if (magic == 0xdeadbeef)`).\n"
    "If the new behavior runs on every call with no new conditional checks in this\n"
    'function, or you cannot identify such a trigger, label it "safe".\n\n'
    "Output EXACT JSON ONLY:\n"
    "{\n"
    '  "label": "not_safe" | "safe",\n'
    '  "trigger": "short description of the trigger condition, or empty string if none",\n'
    '  "why": "1-3 sentences citing the specific changed lines and the behavior difference"\n'
    "}\n"
)

SKEPTIC_SYS = (
    "You are a skeptical security reviewer.\n"
    "You are given:\n"
    "- A unified diff of one function (baseline vs target).\n"
    "- An earlier JSON assessment that claims the change may add a malicious backdoor or logic bomb.\n\n"
    "ASSUMPTION:\n"
    "The overall codebase is expected to be safe. Your job is to REFUTE false accusations whenever possible.\n\n"
    "TASK:\n"
    "1. Read the diff and earlier assessment.\n"
    "2. Decide whether the earlier 'not_safe' label is clearly justified based ONLY on the diff.\n"
    "3. Specifically, check whether:\n"
    "   - There is clearly new behavior vs the baseline, AND\n"
    "   - There is a CONCRETE trigger condition (a specific value, flag, or input combination) visible in the diff\n"
    "     that activates the new behavior, AND\n"
    "   - The new behavior is more permissive, covert, or dangerous.\n\n"
    "OUTPUT:\n"
    "Return EXACT JSON ONLY:\n"
    "{\n"
    '  "verdict": "confirm_not_safe" | "refute",\n'
    '  "reason": "1-3 sentences explaining why you confirm or refute",\n'
    '  "trigger_ok": true | false,\n'
    '  "concrete_trigger": "your own short description of the trigger condition, or empty string if you cannot state one"\n'
    "}\n\n"
    "Guidelines:\n"
    "- Use 'confirm_not_safe' ONLY if you can independently state a concrete trigger and see dangerous new behavior.\n"
    "- Use 'refute' if the change appears to be benign (error handling, logging, validation, etc.), or if you are unsure.\n"
)

# --------------------------------------------------------------------------------------
# Top-level entrypoints / exports
# --------------------------------------------------------------------------------------


def run_all(args, opts):
    results: Dict[str, Any] = {}

    base_outdir = opts.get("outdir", "outputs")
    filters = [
        # None,
        # "Control_Call_Modified",
        "Call_OR_Control_Modified",
    ]

    for flt in filters:
        filter_name = flt if flt is not None else "None"
        results[filter_name] = {}

        # fresh opts per run so we don't leak state
        cfg = dict(opts)

        if flt is None:
            cfg.pop("filter", None)
        else:
            cfg["filter"] = flt

        # give each config its own output directory
        cfg["outdir"] = os.path.join(base_outdir, f"{filter_name}")

        logger.info(f"run_all: filter={filter_name}" f"→ outdir={cfg['outdir']}")

        results[filter_name] = llm_filter(args, cfg)

    # Optional but handy: write to one JSON blob for post-processing
    aggregated_path = os.path.join(base_outdir, "run_all_results.json")
    write_json(aggregated_path, results)
    logger.info(f"✓ Aggregated run_all results written to {aggregated_path}")

    return results


def llm_filter(args: List[str], opts: Dict[str, Any]) -> None:
    """Run triage across a single target→baseline pair or a whole series.

    Expected calling patterns:
      • llm_filter([target, baseline], opts)
      • llm_filter([], {\"entries\": path, ...}) with a plaintext file of CIDs/names
    """
    # --- determine pairs (target→baseline) ---
    pairs: List[Tuple[str, str]]
    series_file: Optional[str] = opts.get("entries")

    if series_file:
        pairs = read_series_file(series_file)
        if len(pairs) < 2:
            raise ValueError(
                "entries file must list at least two versions (one per line)"
            )
    elif len(args) == 2:
        pairs = [(args[0], args[1])]
        logger.info(f"Single comparison: {args[0]} → {args[1]}")
    else:
        raise ValueError(
            "Pass either [target, baseline] or --entries with at least two lines."
        )

    outdir: str = opts.get("outdir", "out_firmware_simple")

    os.makedirs(outdir, exist_ok=True)
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

        res = run_one_comparison(target, baseline, pair_dir, opts)
        stats = res["stats"]

        comparison_rows.append(
            {
                "index": idx,
                "target": target,
                "baseline": baseline,
                "pair_dir": pair_dir,
                **stats,
            }
        )

        # Per-function rows (one observation per modified function in this comparison)
        file_pairs = res.get("file_pairs") or []
        flagged_lookup = {
            (ti["filepair_index"], ti["function_index"])
            for ti in res.get("triage_index", [])
        }

        for fp_idx, fp in enumerate(file_pairs, 1):
            baseline_oid = fp.get("baseline_oid")
            target_oid = fp.get("target_oid")
            modified = fp.get("modified_functions", []) or []
            for func_idx, m in enumerate(modified, 1):
                baddr = ensure_decimal_str(m.get("baseline_func_addr"))
                taddr = ensure_decimal_str(m.get("target_func_addr"))
                key = f"pair{idx}_fp{fp_idx}_func{func_idx}"
                flagged = (fp_idx, func_idx) in flagged_lookup
                per_function_rows.append(
                    {
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
                    }
                )

    # ---- Write cross-comparison summaries ----
    logger.info("Writing cross-comparison summaries…")

    series_summary = {"comparisons": comparison_rows}

    write_json(os.path.join(outdir, "comparisons_summary.json"), series_summary)
    write_json(
        os.path.join(outdir, "per_function_summary.json"),
        {"functions": per_function_rows},
    )
    logger.info(
        "✓ Summaries written (comparisons_summary.json, per_function_summary.json). "
    )
    return series_summary


def import_rosarum_samples(args: List[str], opts: Dict[str, Any]) -> None:
    """
    Import all ROSARUM samples from the outputs directory into Oxide and
    create a collection for each.

    Args (via opts):
        dir_path: Path to the outputs root (OUT_BASE in your copy script),
                  e.g. "/root/rosarum/outputs"

    Returns:
        Dict mapping collection_name -> collection_id (or whatever
        create_collection returns).
    """

    # Map collection names to their directory paths relative to dir_path.
    # These paths are based on your copy script (note: 'synethetic' typo kept).
    layout = {
        # synthetic
        "libxml2-backdoored": "synethetic/libxml2/backdoored",
        "libxml2-safe": "synethetic/libxml2/safe",
        "libxml2-prev-safe": "synethetic/libxml2/prev-safe",
        "libsndfile-backdoored": "synethetic/libsndfile/backdoored",
        "libsndfile-safe": "synethetic/libsndfile/safe",
        "libsndfile-prev-safe": "synethetic/libsndfile/prev-safe",
        "libpng-backdoored": "synethetic/libpng/backdoored",
        "libpng-safe": "synethetic/libpng/safe",
        "libpng-prev-safe": "synethetic/libpng/prev-safe",
        "lua-backdoored": "synethetic/lua/backdoored",
        "lua-safe": "synethetic/lua/safe",
        "lua-prev-safe": "synethetic/lua/prev-safe",
        "php-syn-backdoored": "synethetic/php/backdoored",
        "php-syn-safe": "synethetic/php/safe",
        "php-syn-prev-safe": "synethetic/php/prev-safe",
        "poppler-backdoored": "synethetic/poppler/backdoored",
        "poppler-safe": "synethetic/poppler/safe",
        "poppler-prev-safe": "synethetic/poppler/prev-safe",
        "sudo-backdoored": "synethetic/sudo/backdoored",
        "sudo-safe": "synethetic/sudo/safe",
        "sudo-prev-safe": "synethetic/sudo/prev-safe",
        # authentic
        "proftpd-backdoored": "authentic/proftpd/backdoored",
        "proftpd-safe": "authentic/proftpd/safe",
        "proftpd-prev-safe": "authentic/proftpd/prev-safe",
        "php-auth-backdoored": "authentic/php/backdoored",
        "php-auth-safe": "authentic/php/safe",
        "php-auth-prev-safe": "authentic/php/prev-safe",
        "vsftpd-backdoored": "authentic/vsftpd/backdoored",
        "vsftpd-safe": "authentic/vsftpd/safe",
        "vsftpd-prev-safe": "authentic/vsftpd/prev-safe",
    }

    created: Dict[str, str] = {}
    base_dir = opts["dir_path"]

    for collection_name, rel_dir in layout.items():
        dir_path = os.path.join(base_dir, rel_dir)

        if not os.path.isdir(dir_path):
            print(f"[WARN] Directory does not exist, skipping: {dir_path}")
            continue

        print(f"[INFO] Importing {collection_name} from {dir_path}")
        oids: List[str] = oxide.api.import_directory(dir_path)[0]
        if not oids:
            print(
                f"[WARN] No objects found in {dir_path}, skipping collection creation."
            )
            continue

        cid = oxide.api.create_collection(collection_name, oids)
        created[collection_name] = cid
        print(f"[OK] Created collection {collection_name} -> {cid}")

    return created


# keep plugin export shape
exports = [llm_filter, import_rosarum_samples, run_all]

# --------------------------------------------------------------------------------------
# Core pipeline
# --------------------------------------------------------------------------------------


def run_one_comparison(target: str, baseline: str, outdir: str, opts) -> Dict[str, Any]:
    os.makedirs(outdir, exist_ok=True)
    filter_val = opts.get("filter", None)
    logger.info(
        f"→ Invoking drift (target='{target}', baseline='{baseline}', filter='{filter_val}')"
    )
    t0 = time.perf_counter()

    drift_res = run_drift(target, baseline, filter_val)
    drift_json = coerce_json_like(getattr(drift_res, "content", drift_res)) or {}
    write_json(os.path.join(outdir, "drift_raw.json"), dump_json_safe(drift_json))

    file_pairs: List[Dict[str, Any]] = drift_json.get("file_pairs", []) or []

    report_lines: List[str] = []
    report_lines.append("# Firmware Triage Report (binary suspicion)")
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
    if filter_val:
        report_lines.append(f"Filter:       {filter_val}")
    report_lines.append("")

    triage_index: List[Dict[str, Any]] = []

    # “all modified” vs “filtered modified”
    total_modified_all = 0  # every function drift said was modified
    total_modified_filtered = 0  # only the ones we actually ran through LLM
    n_flagged_filtered = 0
    n_safe_filtered = 0

    # Skeptic-related metrics (filtered functions only)
    n_stage1_not_safe_filtered = 0
    n_skeptic_confirmed = 0
    n_skeptic_refuted = 0

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
        excluded_mods = fp.get("excluded_functions", []) or []

        # count all drift-reported modifications (filtered + excluded)
        total_modified_all += len(filtered_mods) + len(excluded_mods)
        total_modified_filtered += len(filtered_mods)

        report_lines.append(f"## File Pair {fp_idx}")
        report_lines.append(f"- target_oid:   {target_oid}")
        report_lines.append(f"- baseline_oid: {baseline_oid}")
        report_lines.append(f"- modified functions (filtered): {len(filtered_mods)}")
        if excluded_mods:
            report_lines.append(
                f"- modified functions (excluded by filter): {len(excluded_mods)}"
            )
        report_lines.append("")
        logger.info(
            f"   [fp {fp_idx}/{len(file_pairs)}] filtered={len(filtered_mods)}, "
            f"excluded={len(excluded_mods)}"
        )

        # only filtered_mods go to the LLM
        for func_idx, m in enumerate(filtered_mods, 1):
            baddr = ensure_decimal_str(m.get("baseline_func_addr"))
            taddr = ensure_decimal_str(m.get("target_func_addr"))

            res = analyze_function_pair(
                baseline_oid, target_oid, baddr, taddr, fp_idx, func_idx, outdir, opts
            )

            # --- Skeptic metrics ---
            if res.get("stage1_label") == "not_safe":
                n_stage1_not_safe_filtered += 1
                if res.get("refuted_by_skeptic"):
                    n_skeptic_refuted += 1
                if res.get("confirmed_by_skeptic"):
                    n_skeptic_confirmed += 1

            if res["flagged"]:
                n_flagged_filtered += 1
                triage_index.append(
                    {
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
                    }
                )
            else:
                n_safe_filtered += 1

            logger.info(f"      functions processed: {func_idx}/{len(filtered_mods)}")

        logger.info(f"   [fp {fp_idx}] done")

    # overall: everything drift said was modified
    # we did not LLM the excluded funcs, so we count them as “implicitly safe”
    overall_safe = n_safe_filtered + (total_modified_all - total_modified_filtered)
    overall_safe_rate = overall_safe / total_modified_all if total_modified_all else 0.0

    dt = time.perf_counter() - t0
    logger.info(
        f"Drift + triage finished in {dt:.1f}s: "
        f"all_modified={total_modified_all}, filtered={total_modified_filtered}, "
        f"flagged_filtered={n_flagged_filtered}, safe_filtered={n_safe_filtered}"
    )

    report_lines.append("")
    report_lines.append("## Summary statistics")
    report_lines.append(f"- Total modified functions (ALL): {total_modified_all}")
    report_lines.append(
        f"- Total modified functions (FILTERED): {total_modified_filtered}"
    )
    report_lines.append(f"- Flagged (filtered, final): {n_flagged_filtered}")
    report_lines.append(f"- Safe (filtered, final): {n_safe_filtered} ")
    report_lines.append(
        f"- Stage1 not_safe (before skeptic, filtered): {n_stage1_not_safe_filtered}"
    )
    report_lines.append(f"- Skeptic confirmed not_safe: {n_skeptic_confirmed}")
    report_lines.append(f"- Skeptic refuted (downgraded to safe): {n_skeptic_refuted}")
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
        # filtered-only (the LLM work)
        "total_modified_functions_filtered": total_modified_filtered,
        "flagged_not_safe_filtered": n_flagged_filtered,
        "safe_filtered": n_safe_filtered,
        # skeptic metrics
        "stage1_not_safe_filtered": n_stage1_not_safe_filtered,
        "skeptic_confirmed_filtered": n_skeptic_confirmed,
        "skeptic_refuted_filtered": n_skeptic_refuted,
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
    fp_idx: int,
    func_idx: int,
    outdir,
    opts,
) -> Dict[str, Any]:
    func_dir = os.path.join(
        outdir,
        f"filepair_{fp_idx:02d}",
        f"func_{func_idx:02d}__b{baddr}__t{taddr}",
    )

    os.makedirs(func_dir, exist_ok=True)
    notes_path = os.path.join(func_dir, "notes.json")
    notes: Dict[str, Any] = {"observations": [], "artifacts": []}

    diff_raw = oxide.retrieve(
        "function_decomp_diff",
        [target_oid, baseline_oid],
        {"target": taddr, "baseline": baddr},
    )

    if isinstance(diff_raw, dict) and "error" in diff_raw:
        notes["observations"].append("diff tool failed")
        # Save and return safe verdict if we can't diff
        write_json(notes_path, notes)
        write_text(os.path.join(func_dir, "diff.txt"), "")
        verdict = "Label: safe — no diff available (tool error)"
        write_json(
            os.path.join(func_dir, "analysis.json"),
            {
                "label": "safe",
                "why": "no diff available",
                "flagged": False,
                "verdict": verdict,
                "stage1": None,
                "skeptic": None,
            },
        )
        write_text(os.path.join(func_dir, "verdict.txt"), verdict)
        return {
            "label": "safe",
            "why": "no diff available",
            "flagged": False,
            "verdict": verdict,
            "func_dir": func_dir,
            "skeptic": None,
        }

    diff_text = extract_content(diff_raw) or ""
    write_text(os.path.join(func_dir, "diff.txt"), diff_text)

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

    label_stage1 = "safe"
    trigger_stage1 = ""
    why_stage1 = ""
    skeptic_result: Optional[Dict[str, Any]] = None

    # ------------------------
    # 2) LLM triage via LangGraph (+ skeptic)
    # ------------------------
    if unified.strip():
        triage = run_triage_langgraph(
            unified_diff=unified,
            fp_idx=fp_idx,
            func_idx=func_idx,
            notes=notes,
        )

        triage_trace = triage.get("trace") or []

        # Final decision from graph (after skeptic)
        label = triage.get("label", "safe")
        why = (triage.get("why") or "").strip()

        # Stage1 result (before skeptic) for metrics
        label_stage1 = triage.get("stage1_label", label)
        trigger_stage1 = (triage.get("stage1_trigger") or "").strip()
        why_stage1 = (triage.get("stage1_why") or "").strip()

        skeptic_result = triage.get("skeptic")

        # Persist LangGraph + skeptic trace
        trace_payload = {
            "fp_index": fp_idx,
            "func_index": func_idx,
            "baseline_addr": baddr,
            "target_addr": taddr,
            "diff_chars": len(unified),
            "trace": triage_trace,
        }
        write_json(os.path.join(func_dir, "triage_trace.json"), trace_payload)
        notes["artifacts"].append(
            {
                "kind": "triage_trace",
                "path": "triage_trace.json",
            }
        )

    # Did the skeptic overturn or confirm a stage1 "not_safe"?
    refuted_by_skeptic = bool(label_stage1 == "not_safe" and label == "safe")
    confirmed_by_skeptic = bool(
        label_stage1 == "not_safe"
        and label == "not_safe"
        and skeptic_result
        and skeptic_result.get("verdict") == "confirm_not_safe"
        and skeptic_result.get("trigger_ok")
    )

    flagged = label == "not_safe"
    verdict = (
        f"Label: {'needs further inspection' if flagged else 'safe'} — "
        f"{why or 'model provided no reason'}"
    )

    # Save outputs
    write_json(notes_path, notes)
    write_json(
        os.path.join(func_dir, "analysis.json"),
        {
            "label": label,
            "why": why,
            "flagged": flagged,
            "verdict": verdict,
            "stage1": {
                "label": label_stage1,
                "trigger": trigger_stage1,
                "why": why_stage1,
            },
            "skeptic": skeptic_result,
            "refuted_by_skeptic": refuted_by_skeptic,
            "confirmed_by_skeptic": confirmed_by_skeptic,
        },
    )
    write_text(os.path.join(func_dir, "verdict.txt"), verdict)

    return {
        "label": label,
        "why": why,
        "flagged": flagged,
        "verdict": verdict,
        "func_dir": func_dir,
        "skeptic": skeptic_result,
        "stage1_label": label_stage1,
        "refuted_by_skeptic": refuted_by_skeptic,
        "confirmed_by_skeptic": confirmed_by_skeptic,
    }


# --------------------------------------------------------------------------------------
# Drift helpers
# --------------------------------------------------------------------------------------


def run_drift(
    target_cid: str, baseline_cid: str, filter_val: Optional[str] = None
) -> Dict[str, Any]:
    out: Dict[str, Any] = {"file_pairs": []}
    try:
        if filter_val:
            drift = (
                compare_collections([target_cid, baseline_cid], {"filter": filter_val})
                or {}
            )
        else:
            drift = compare_collections([target_cid, baseline_cid], {}) or {}
    except Exception as e:
        logger.error(f"compare_collections failed: {e}")
        return out

    per_file = (drift.get("FUNCTION_CLASSIFICATION", {}) or {}).get(
        "PER_FILE", {}
    ) or {}

    for file_key, file_entry in per_file.items():
        # file_key shape is (target_oid, baseline_oid) by Oxide convention in this view
        if not isinstance(file_key, (tuple, list)) or len(file_key) != 2:
            continue
        target_oid, baseline_oid = file_key[0], file_key[1]

        if filter_val:
            search_space = file_entry.get(filter_val) or []
            excluded_functions = file_entry.get("modified") or []
        else:
            search_space = file_entry.get("modified") or []
            excluded_functions = {}

        search_space_out: List[Dict[str, Any]] = []

        for m in search_space:
            feats = m.get("features", {}) if isinstance(m, dict) else {}

            # The drift “pair” gives (target_addr, baseline_addr) (by convention here).
            pair = m.get("pair", [None, None])
            t_addr_str = _dec_str(pair[0]) if pair and len(pair) > 0 else None
            b_addr_str = _dec_str(pair[1]) if pair and len(pair) > 1 else None

            search_space_out.append(
                {
                    "baseline_func_addr": b_addr_str,
                    "target_func_addr": t_addr_str,
                    "features": feats,
                },
            )

        out["file_pairs"].append(
            {
                "baseline_oid": baseline_oid,
                "target_oid": target_oid,
                "modified_functions": search_space_out,
                "excluded_functions": excluded_functions,
            }
        )

    return out


# --------------------------------------------------------------------------------------
# LLM helper functions
# --------------------------------------------------------------------------------------


def call_analyst_llm(
    user_content: str, fp_idx: int, func_idx: int, notes: Dict[str, Any]
) -> str:
    """
    Primary analysis model (deterministic).
    Returns JSON text on success, or a fallback JSON string marking the
    function as not_safe with an error explanation on failure.
    """
    t_llm = time.perf_counter()
    try:
        resp = LLM.invoke(
            [
                SystemMessage(content=ANALYST_SYS),
                HumanMessage(content=user_content),
            ]
        )
        text_local = ascii_sanitize((getattr(resp, "content", "") or "")).strip()
        dt_llm = time.perf_counter() - t_llm

        if not text_local:
            logger.error(
                f"LLM ANALYST EMPTY fp={fp_idx} func={func_idx} "
                f"after {dt_llm:.2f}s (diff_chars={len(user_content)})"
            )
            raise ValueError("LLM (analyst) returned empty content")

        logger.info(
            f"LLM ANALYST OK fp={fp_idx} func={func_idx} "
            f"took {dt_llm:.2f}s (diff_chars={len(user_content)})"
        )

        return text_local

    except Exception as e:
        dt_llm = time.perf_counter() - t_llm
        err_msg = f"LLM analyst failed fp={fp_idx} func={func_idx}: {e}"

        logger.error(
            f"LLM ANALYST ERROR fp={fp_idx} func={func_idx} "
            f"after {dt_llm:.2f}s: {e}"
        )

        notes["observations"].append(err_msg)

        # Return a valid JSON string that marks the function unsafe.
        fallback_json = json.dumps(
            {
                "label": "not_safe",
                "trigger": "",
                "why": f"LLM analyst failed: {str(e)}",
            }
        )
        return fallback_json


def call_format_llm(
    raw_output: str, fp_idx: int, func_idx: int, notes: Dict[str, Any]
) -> str:
    """
    Second model: takes arbitrary text from the analyst model and
    turns it into valid JSON in the required schema.
    Returns JSON text on success, or a fallback JSON string marking the
    function as not_safe with an error explanation on failure.
    """
    t_llm = time.perf_counter()
    format_sys = (
        "You are a strict JSON formatter.\n"
        "You receive the *intended meaning* of a model's answer but possibly "
        "with wrong formatting.\n"
        "Your ONLY job is to output VALID JSON matching this schema:\n"
        "{\n"
        '  "label": "not_safe" | "safe",\n'
        '  "trigger": "short description of the trigger condition, or empty string if none",\n'
        '  "why": "1-3 sentences citing the specific + line(s) and the control/data-flow change"\n'
        "}\n"
        "Do not change the meaning, only fix the formatting.\n"
        "Do NOT include code fences, explanations, or any text outside of the JSON."
    )

    repair_prompt = (
        "Here is the previous model output that may not be valid JSON.\n"
        "Rewrite it as valid JSON in the required schema.\n\n"
        "Previous output:\n"
        f"{raw_output}"
    )

    try:
        resp = FORMAT_LLM.invoke(
            [
                SystemMessage(content=format_sys),
                HumanMessage(content=repair_prompt),
            ]
        )
        fixed = ascii_sanitize((getattr(resp, "content", "") or "")).strip()
        dt_llm = time.perf_counter() - t_llm

        logger.info(
            f"LLM FORMAT OK fp={fp_idx} func={func_idx} "
            f"took {dt_llm:.2f}s (len(raw_output)={len(raw_output)})"
        )

        if not fixed:
            raise ValueError("LLM (format) returned empty content")

        return fixed

    except Exception as e:
        dt_llm = time.perf_counter() - t_llm
        logger.error(
            f"LLM FORMAT ERROR fp={fp_idx} func={func_idx} " f"after {dt_llm:.2f}s: {e}"
        )
        notes["observations"].append(f"LLM format error: {e}")

        # Return a valid JSON string that marks the function unsafe.
        fallback_json = json.dumps(
            {
                "label": "not_safe",
                "trigger": "",
                "why": f"LLM format failed: {str(e)}",
            }
        )
        return fallback_json


def call_normalize_llm(
    raw_json_like: str, fp_idx: int, func_idx: int, notes: Dict[str, Any]
) -> str:
    """
    Third model: normalizes any synonyms in the JSON into the strict label
    vocabulary {\"safe\", \"not_safe\"}.

    Returns JSON text on success or a fallback JSON string marking it not_safe
    on failure.
    """
    t_llm = time.perf_counter()
    norm_sys = (
        "You are a strict JSON normalizer.\n"
        "You receive JSON (or JSON-like text) describing whether a code change\n"
        "is malicious or benign.\n\n"
        "Your ONLY job is to output VALID JSON matching this schema:\n"
        "{\n"
        '  "label": "not_safe" | "safe",\n'
        '  "trigger": "short description of the trigger condition, or empty string if none",\n'
        '  "why": "1-3 sentences citing the specific + line(s) and the control/data-flow change"\n'
        "}\n\n"
        "If the input uses synonyms (e.g., 'malicious', 'benign', 'unsafe', "
        "'harmless', 'backdoor present', booleans, etc.), you MUST map them\n"
        "onto 'not_safe' or 'safe' for the label.\n"
        "Do NOT include code fences, explanations, or any text outside of the JSON."
    )

    norm_prompt = (
        "Here is a previous model output which may already be JSON but may use\n"
        "synonyms or an inconsistent schema.\n"
        "Rewrite it as JSON in the required schema, using ONLY 'safe' or "
        "'not_safe' for the label.\n\n"
        "Previous output:\n"
        f"{raw_json_like}"
    )

    try:
        resp = NORMALIZE_LLM.invoke(
            [
                SystemMessage(content=norm_sys),
                HumanMessage(content=norm_prompt),
            ]
        )
        fixed = ascii_sanitize((getattr(resp, "content", "") or "")).strip()
        dt_llm = time.perf_counter() - t_llm

        logger.info(
            f"LLM NORMALIZE OK fp={fp_idx} func={func_idx} "
            f"took {dt_llm:.2f}s (len(raw_json_like)={len(raw_json_like)})"
        )

        if not fixed:
            raise ValueError("LLM (normalize) returned empty content")

        return fixed

    except Exception as e:
        dt_llm = time.perf_counter() - t_llm
        logger.error(
            f"LLM NORMALIZE ERROR fp={fp_idx} func={func_idx} "
            f"after {dt_llm:.2f}s: {e}"
        )
        notes["observations"].append(f"LLM normalize error: {e}")

        # Fail closed: mark as not_safe if the normalizer fails.
        fallback_json = json.dumps(
            {
                "label": "not_safe",
                "trigger": "",
                "why": f"LLM normalize failed: {str(e)}",
            }
        )
        return fallback_json


def call_skeptic_llm(
    diff_text: str,
    stage1_result: Dict[str, Any],
    fp_idx: int,
    func_idx: int,
    notes: Dict[str, Any],
) -> str:
    """
    Second-stage skeptic: tries to refute 'not_safe' labels.
    Returns JSON text (verdict/refute) or a fallback JSON on failure.
    """
    t_llm = time.perf_counter()

    skeptic_prompt = (
        "You will review an earlier backdoor assessment.\n\n"
        "=== FUNCTION UNIFIED DIFF ===\n"
        f"{diff_text}\n\n"
        "=== EARLIER ASSESSMENT JSON ===\n"
        f"{json.dumps(stage1_result, indent=2)}\n"
    )

    try:
        resp = SKEPTIC_LLM.invoke(
            [
                SystemMessage(content=SKEPTIC_SYS),
                HumanMessage(content=ascii_sanitize(skeptic_prompt)),
            ]
        )
        text_local = ascii_sanitize((getattr(resp, "content", "") or "")).strip()
        dt_llm = time.perf_counter() - t_llm

        logger.info(
            f"LLM SKEPTIC OK fp={fp_idx} func={func_idx} "
            f"took {dt_llm:.2f}s (diff_chars={len(diff_text)})"
        )

        if not text_local:
            raise ValueError("LLM (skeptic) returned empty content")

        return text_local

    except Exception as e:
        dt_llm = time.perf_counter() - t_llm
        err_msg = f"LLM skeptic failed fp={fp_idx} func={func_idx}: {e}"
        logger.error(
            f"LLM SKEPTIC ERROR fp={fp_idx} func={func_idx} "
            f"after {dt_llm:.2f}s: {e}"
        )
        notes["observations"].append(err_msg)

        # Fallback: fail-closed and keep the alert.
        fallback_json = json.dumps(
            {
                "verdict": "confirm_not_safe",
                "reason": f"Skeptic LLM failed: {str(e)}",
                "trigger_ok": True,
                "concrete_trigger": "",
            }
        )
        return fallback_json


def run_skeptic_review(
    unified_diff: str,
    stage1_result: Dict[str, Any],
    fp_idx: int,
    func_idx: int,
    notes: Dict[str, Any],
) -> Dict[str, Any]:
    """
    Run the skeptic LLM and normalize its output into:
      {verdict, reason, trigger_ok, concrete_trigger}
    """
    text = call_skeptic_llm(
        diff_text=unified_diff,
        stage1_result=stage1_result,
        fp_idx=fp_idx,
        func_idx=func_idx,
        notes=notes,
    )

    data = parse_llm_json(text)
    if not isinstance(data, dict):
        msg = "Skeptic LLM output was not valid JSON; keeping stage1 not_safe label."
        notes["observations"].append(msg)
        return {
            "verdict": "confirm_not_safe",
            "reason": msg,
            "trigger_ok": True,
            "concrete_trigger": "",
        }

    verdict_raw = str(data.get("verdict", "refute")).strip().lower()

    if verdict_raw in {"confirm_not_safe", "confirm", "not_safe", "unsafe"}:
        verdict = "confirm_not_safe"
    else:
        # Anything else (including garbage) => refute
        verdict = "refute"

    trigger_ok = bool(data.get("trigger_ok", False))

    concrete_trigger_raw = data.get("concrete_trigger", "")
    try:
        concrete_trigger = str(concrete_trigger_raw).strip()
    except Exception:
        concrete_trigger = ""

    reason_raw = data.get("reason", "")
    try:
        reason = str(reason_raw).strip()
    except Exception:
        reason = ""

    return {
        "verdict": verdict,
        "reason": reason,
        "trigger_ok": trigger_ok,
        "concrete_trigger": concrete_trigger,
    }


# --------------------------------------------------------------------------------------
# LangGraph state + graph
# --------------------------------------------------------------------------------------


class TriageState(TypedDict, total=False):
    # Inputs
    diff: str
    fp_idx: int
    func_idx: int
    notes: Dict[str, Any]

    # Intermediate text stages
    raw_output: Optional[str]
    formatted_output: Optional[str]
    normalized_output: Optional[str]

    # Final parsed JSON
    final_json: Optional[Dict[str, Any]]

    # NEW: keep stage1 (pre-skeptic) + skeptic result
    stage1_json: Optional[Dict[str, Any]]
    skeptic_json: Optional[Dict[str, Any]]

    # Trace of each node's activity
    trace: List[Dict[str, Any]]


def _build_triage_graph():
    """
    Build a tiny LangGraph pipeline:

        START
          ↓
       analyst  (gpt-oss:20b)
         │
         ├── valid JSON + correct label -> finalize
         ├── valid JSON but synonyms    -> normalize
         └── not JSON                   -> format -> normalize -> finalize
    """
    graph = StateGraph(TriageState)

    # --- Nodes --------------------------------------------------------------

    def analyst_node(state: TriageState) -> TriageState:
        diff = state["diff"]
        fp_idx = state["fp_idx"]
        func_idx = state["func_idx"]
        notes = state["notes"]

        user_content = f"FUNCTION UNIFIED DIFF:\n\n{diff}"

        t0 = time.perf_counter()
        text = call_analyst_llm(
            user_content=user_content,
            fp_idx=fp_idx,
            func_idx=func_idx,
            notes=notes,
        )
        dt = time.perf_counter() - t0

        trace = list(state.get("trace", []))
        trace.append(
            {
                "node": "analyst",
                "duration_s": dt,
                "input_diff_chars": len(diff),
                "output_len": len(text),
                "output_preview": text[:400],
            }
        )

        return {"raw_output": text, "trace": trace}

    def format_node(state: TriageState) -> TriageState:
        raw = state.get("raw_output") or ""
        fp_idx = state["fp_idx"]
        func_idx = state["func_idx"]
        notes = state["notes"]

        t0 = time.perf_counter()
        fixed = call_format_llm(
            raw_output=raw,
            fp_idx=fp_idx,
            func_idx=func_idx,
            notes=notes,
        )
        dt = time.perf_counter() - t0

        trace = list(state.get("trace", []))
        trace.append(
            {
                "node": "format",
                "duration_s": dt,
                "input_len": len(raw),
                "output_len": len(fixed),
                "output_preview": fixed[:400],
            }
        )

        return {"formatted_output": fixed, "trace": trace}

    def normalize_node(state: TriageState) -> TriageState:
        # Prefer formatted JSON if we have it, otherwise fall back to raw.
        text_in = state.get("formatted_output") or state.get("raw_output") or ""
        fp_idx = state["fp_idx"]
        func_idx = state["func_idx"]
        notes = state["notes"]

        t0 = time.perf_counter()
        normalized = call_normalize_llm(
            raw_json_like=text_in,
            fp_idx=fp_idx,
            func_idx=func_idx,
            notes=notes,
        )
        dt = time.perf_counter() - t0

        trace = list(state.get("trace", []))
        trace.append(
            {
                "node": "normalize",
                "duration_s": dt,
                "input_len": len(text_in),
                "output_len": len(normalized),
                "output_preview": normalized[:400],
            }
        )

        return {"normalized_output": normalized, "trace": trace}

    def finalize_node(state: TriageState) -> TriageState:
        """
        Choose the best candidate text, parse JSON, and apply a final
        Python-side normalization + fail-closed semantics.
        """
        notes = state["notes"]
        text = (
            state.get("normalized_output")
            or state.get("formatted_output")
            or state.get("raw_output")
            or ""
        )

        data = parse_llm_json(text)
        from_json = bool(isinstance(data, dict))

        if not isinstance(data, dict):
            # Hard fail-closed: if we still can't parse JSON at this point,
            # mark as not_safe.
            msg = (
                "Final JSON parse failed even after formatting/normalization; "
                "marking as not_safe."
            )
            notes["observations"].append(msg)
            final = {
                "label": "not_safe",
                "trigger": "",
                "why": msg,
            }
        else:
            # --- Label normalization (Python fallback) ----------------------
            label_raw = str(data.get("label", "")).strip().lower().replace("-", "_")

            # Map common synonyms onto the strict vocabulary.
            if label_raw in {
                "not_safe",
                "unsafe",
                "malicious",
                "evil",
                "suspicious",
                "backdoor",
                "backdoored",
                "logic_bomb",
                "logicbomb",
                "vulnerable",
            }:
                label = "not_safe"
            elif label_raw in {
                "safe",
                "benign",
                "harmless",
                "clean",
                "ok",
                "no_backdoor",
                "no_issue",
                "no_issues",
                "non_malicious",
            }:
                label = "safe"
            elif isinstance(data.get("label"), bool):
                label = "not_safe" if data["label"] else "safe"
            else:
                # Fail-closed: unrecognized label -> not_safe.
                label = "not_safe"

            why = (data.get("why") or "").strip() or "model provided no reason"

            raw_trigger = data.get("trigger", "")
            if raw_trigger is None:
                trigger = ""
            else:
                try:
                    trigger = str(raw_trigger).strip()
                except Exception:
                    trigger = ""

            final = {"label": label, "trigger": trigger, "why": why}

        trace = list(state.get("trace", []))
        trace.append(
            {
                "node": "finalize",
                "from_valid_json": from_json,
                "final_label": final["label"],
                "final_trigger_preview": (final.get("trigger") or "")[:200],
                "final_why_preview": final["why"][:400],
            }
        )

        return {"final_json": final, "stage1_json": final, "trace": trace}

    def skeptic_node(state: TriageState) -> TriageState:
        diff = state["diff"]
        fp_idx = state["fp_idx"]
        func_idx = state["func_idx"]
        notes = state["notes"]

        stage1 = state.get("stage1_json") or state.get("final_json") or {}

        t0 = time.perf_counter()
        skeptic = run_skeptic_review(
            unified_diff=diff,
            stage1_result={
                "label": stage1.get("label", ""),
                "trigger": stage1.get("trigger", ""),
                "why": stage1.get("why", ""),
            },
            fp_idx=fp_idx,
            func_idx=func_idx,
            notes=notes,
        )
        dt = time.perf_counter() - t0

        verdict_s = skeptic.get("verdict", "refute")
        trigger_ok = bool(skeptic.get("trigger_ok", False))

        # Normalize stage1 label
        stage1_label_raw = (
            str(stage1.get("label", "safe")).strip().lower().replace("-", "_")
        )
        stage1_label = "not_safe" if stage1_label_raw == "not_safe" else "safe"

        final_label = stage1_label
        final_why = (stage1.get("why") or "").strip()
        trigger = (stage1.get("trigger") or "").strip()

        if stage1_label == "not_safe":
            if verdict_s == "confirm_not_safe" and trigger_ok:
                reason_extra = (skeptic.get("reason") or "").strip()
                if reason_extra:
                    final_why = (
                        f"{final_why} | Skeptic: {reason_extra}"
                        if final_why
                        else f"Skeptic: {reason_extra}"
                    )
            else:
                final_label = "safe"
                final_why = (
                    skeptic.get("reason")
                    or "Second-stage skeptic did not confirm the backdoor; treating as safe."
                )

        final = {
            "label": final_label,
            "trigger": trigger,
            "why": final_why,
        }

        trace = list(state.get("trace", []))
        trace.append(
            {
                "node": "skeptic",
                "duration_s": dt,
                "verdict": verdict_s,
                "trigger_ok": trigger_ok,
                "reason_preview": (skeptic.get("reason") or "")[:400],
                "concrete_trigger_preview": (skeptic.get("concrete_trigger") or "")[
                    :200
                ],
            }
        )

        return {
            "final_json": final,
            "stage1_json": stage1,
            "skeptic_json": skeptic,
            "trace": trace,
        }

    # --- Routing / condition logic -----------------------------------------

    def route_after_analyst(state: TriageState) -> str:
        """
        Decide where to go after the analyzer LLM:

            - If output isn't JSON -> 'format'
            - If JSON and label in {safe, not_safe} -> 'finalize'
            - If JSON but synonyms / weird label -> 'normalize'
        """
        raw = state.get("raw_output") or ""
        data = parse_llm_json(raw)

        if not isinstance(data, dict):
            return "format"  # not JSON, go to formatter

        label_raw = str(data.get("label", "")).strip().lower().replace("-", "_")
        if label_raw in ("safe", "not_safe"):
            return "finalize"

        # JSON but label is wrong / synonym -> use normalizer
        return "normalize"

    def route_after_finalize(state: TriageState) -> str:
        final = state.get("final_json") or {}
        label_raw = (
            str(final.get("label", "not_safe")).strip().lower().replace("-", "_")
        )
        if label_raw == "not_safe":
            return "needs_skeptic"
        return "end"

    # --- Wire up the graph -------------------------------------------------

    graph.add_node("analyst", analyst_node)
    graph.add_node("format", format_node)
    graph.add_node("normalize", normalize_node)
    graph.add_node("finalize", finalize_node)
    graph.add_node("skeptic", skeptic_node)

    graph.add_edge(START, "analyst")
    graph.add_conditional_edges(
        "analyst",
        route_after_analyst,
        {
            "format": "format",
            "normalize": "normalize",
            "finalize": "finalize",
        },
    )
    graph.add_edge("format", "normalize")
    graph.add_edge("normalize", "finalize")

    # NEW: finalize -> (skeptic | END)
    graph.add_conditional_edges(
        "finalize",
        route_after_finalize,
        {
            "needs_skeptic": "skeptic",
            "end": END,
        },
    )

    # Skeptic always ends
    graph.add_edge("skeptic", END)

    return graph.compile()


def show_and_save_triage_graph_png(path: str = "triage_graph.png") -> None:
    # TRIAGE_GRAPH is the compiled app from _build_triage_graph()
    g = TRIAGE_GRAPH.get_graph()

    try:
        png_bytes = g.draw_mermaid_png()
    except Exception as e:
        print(f"Failed to render mermaid PNG: {e}")
        return

    # 1) Display in a notebook (if you're in IPython/Jupyter)
    try:
        display(Image(png_bytes))
    except Exception as e:
        print(f"Display failed (not in a notebook?): {e}")

    # 2) Save to a PNG file in the current directory
    with open(path, "wb") as f:
        f.write(png_bytes)
    print(f"Saved triage graph PNG to {path}")


# Single compiled instance, like the LLM objects above
TRIAGE_GRAPH = _build_triage_graph()
show_and_save_triage_graph_png()


def run_triage_langgraph(
    unified_diff: str, fp_idx: int, func_idx: int, notes: Dict[str, Any]
) -> Dict[str, Any]:
    """
    Entry point for the LangGraph-backed triage pipeline.
    Returns a dict with at least
      {"label", "trigger", "why", "trace", "stage1_label", "stage1_trigger",
       "stage1_why", "skeptic"}.
    """
    initial_state: TriageState = {
        "diff": ascii_sanitize(unified_diff),
        "fp_idx": fp_idx,
        "func_idx": func_idx,
        "notes": notes,
        "trace": [],
    }

    # Fail-closed if the graph itself blows up
    try:
        result_state = TRIAGE_GRAPH.invoke(initial_state)
    except Exception as e:
        msg = f"LangGraph invoke failed: {e}; marking function as not_safe."
        notes["observations"].append(msg)
        return {
            "label": "not_safe",
            "trigger": "",
            "why": "LangGraph triage pipeline failed; treating change as not_safe.",
            "trace": [
                {
                    "node": "graph_invoke",
                    "error": str(e),
                }
            ],
            "stage1_label": "not_safe",
            "stage1_trigger": "",
            "stage1_why": "LangGraph triage pipeline failed.",
            "skeptic": None,
        }

    final = result_state.get("final_json") or {}
    stage1 = result_state.get("stage1_json") or final
    skeptic = result_state.get("skeptic_json")
    trace = result_state.get("trace") or []

    if not isinstance(final, dict):
        final = {
            "label": "not_safe",
            "trigger": "",
            "why": f"internal error: unexpected graph output {final!r}",
        }

    # Final label (after skeptic), fail-closed
    label_raw = str(final.get("label", "not_safe")).strip().lower().replace("-", "_")
    if label_raw not in ("safe", "not_safe"):
        label = "not_safe"
    else:
        label = label_raw

    why = (final.get("why") or "").strip()
    trigger = (final.get("trigger") or "").strip()

    # Stage1 (pre-skeptic) normalization, also fail-closed
    if not isinstance(stage1, dict):
        stage1 = {"label": "not_safe", "trigger": "", "why": "missing stage1_json"}

    s_label_raw = str(stage1.get("label", "not_safe")).strip().lower().replace("-", "_")
    if s_label_raw not in ("safe", "not_safe"):
        stage1_label = "not_safe"
    else:
        stage1_label = s_label_raw

    stage1_trigger = (stage1.get("trigger") or "").strip()
    stage1_why = (stage1.get("why") or "").strip()

    return {
        "label": label,
        "trigger": trigger,
        "why": why,
        "trace": trace,
        "stage1_label": stage1_label,
        "stage1_trigger": stage1_trigger,
        "stage1_why": stage1_why,
        "skeptic": skeptic,
    }


# --------------------------------------------------------------------------------------
# Utilities
# --------------------------------------------------------------------------------------


def read_series_file(path: str, sep: str = ",") -> List[Tuple[str, str]]:
    """
    Read a series file where each non-comment line defines a pair of collections.

    Example line format (default sep=","):
        coll_old, coll_new

    Returns:
        List of (cid_left, cid_right) tuples.
    """
    pairs: List[Tuple[str, str]] = []

    with open(path, "r", encoding="utf-8") as f:
        for raw_ln in f:
            ln = raw_ln.strip()
            if not ln or ln.startswith("#"):
                continue

            parts = [p.strip() for p in ln.split(sep)]
            if len(parts) != 2:
                raise ValueError(
                    f"Line {raw_ln!r} does not contain exactly two collections "
                    f"separated by {sep!r}"
                )

            left_name, right_name = parts
            cid_left = oxide.api.get_cid_from_name(left_name)
            cid_right = oxide.api.get_cid_from_name(right_name)
            pairs.append((cid_left, cid_right))

    return pairs


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
    ord("\u00a0"): 32,
    ord("\u202f"): 32,
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
