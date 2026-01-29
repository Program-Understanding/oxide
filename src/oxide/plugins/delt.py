import json
import logging
import os
import re
import unicodedata
import time
from typing import Any, Dict, Optional, List, Set, Tuple
import time

from typing_extensions import TypedDict
from langgraph.graph import StateGraph, START, END

from langchain_core.messages import HumanMessage, SystemMessage
from langchain_ollama import ChatOllama

from oxide.plugins.drift import compare_collections
from oxide.core import oxide as oxide
from oxide.core.oxide import api, progress

logging.getLogger("httpx").setLevel(logging.WARNING)

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
ANALYST_SCHEMA = {
  "type": "object",
  "properties": {
    "label":   {"type": "string", "enum": ["safe", "not_safe"]},
    "trigger": {"type": "string"},
    "why":     {"type": "string"}
  },
  "required": ["label", "trigger", "why"],
  "additionalProperties": False
}

REVIEWER_SCHEMA = {
  "type": "object",
  "properties": {
    "verdict": {"type": "string", "enum": ["confirm_not_safe", "refute"]},
    "reason":  {"type": "string"}
  },
  "required": ["verdict", "reason"],
  "additionalProperties": False
}

LLM = ChatOllama(
    model="gpt-oss:120b",
    temperature=0.0,
    num_ctx=8192,
    keep_alive="10m",
    request_timeout=180.0,
    format=ANALYST_SCHEMA,
    model_kwargs={"num_predict": 512},
)

REVIEWER_LLM = ChatOllama(
    model="gpt-oss:120b",
    temperature=0.0,
    num_ctx=8192,
    keep_alive="10m",
    request_timeout=180.0,
    format=REVIEWER_SCHEMA,
    model_kwargs={"num_predict": 256},
)

ANALYST_SYS = (
    "You are an expert reverse engineer analyzing code that is expected to be safe.\n"
    "Input is a unified diff of the decompiled C for ONE function (baseline vs target).\n\n"
    "TASK:\n"
    "Decide if the change introduces a malicious backdoor in THIS function.\n"
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

ANALYST_SYS_VULN = (
    "You are an expert reverse engineer analyzing code that is expected to be safe.\n"
    "Input is a unified diff of the decompiled C for ONE function (baseline vs target).\n\n"
    "TASK:\n"
    "Decide if the change plausibly introduces a security-relevant vulnerability or weakens a security property in THIS function.\n"
    'Only label it "not_safe" if you can state a concrete exploit condition over inputs or state\n'
    "that becomes possible or more likely due to the change, based solely on evidence visible in the diff.\n"
    "Your exploit condition can be a trigger-like predicate, a missing check, a widened acceptance condition,\n"
    "a new dangerous call on attacker-controlled data, a bounds/length mistake, or an authorization/logic regression.\n\n"
    "If you label \"not_safe\", you must quote the specific changed expression(s) that support your claim in the `trigger`\n"
    "field by copying the exact new comparison, removed check, or new dangerous call argument.\n"
    "If you cannot tie the risk to specific changed lines, label it \"safe\".\n\n"
    "Output EXACT JSON ONLY:\n"
    "{\n"
    '  "label": "not_safe" | "safe",\n'
    '  "trigger": "exact quoted expression(s) from the diff that enable the risk, or empty string if none",\n'
    '  "why": "1-3 sentences describing the security impact and citing the specific changed lines"\n'
    "}\n"
)

REVIEWER_SYS = (
    "You are a security reviewer.\n"
    "You are given:\n"
    "- A unified diff of one function (baseline vs target) that may be trimmed for size.\n"
    "- An earlier assessment that claims the change may add a potentially malicious backdoor as well as the potential trigger.\n\n"
    "Your job is to refute clearly false accusations.\n\n"
    "TASK:\n"
    "1. Read the diff and previous assessment.\n"
    "2. Decide whether the previous 'not_safe' label is justified.\n"
    "3. Specifically, check whether:\n"
    "   - There is a trigger condition visible in the diff that activates newly added behavior\n"
    "- Do NOT refute only because a variable appears to be uninitialized or its origin is unclear, or because you do not\n"
    "  see the full control flow; the unified diff may omit parts of the function.\n\n"
    "OUTPUT:\n"
    "Return EXACT JSON ONLY:\n"
    "{\n"
    '  "verdict": "confirm_not_safe" | "refute",\n'
    '  "reason": "1-3 sentences explaining why you confirm or refute",\n'
    "}\n\n"
    "Guidelines:\n"
    "- Use 'confirm_not_safe' if you can verify a trigger leading to potentially dangerous new behavior.\n"
    "- Use 'refute' if the change appears to be standard benign updates (error handling, logging, validation, etc.).\n"
)

REVIEWER_SYS_VULN = (
    "You are a security reviewer.\n"
    "You are given:\n"
    "- A unified diff of one function (baseline vs target) that may be trimmed for size.\n"
    "- An earlier assessment that claims the change may introduce a security-relevant vulnerability or security regression\n"
    "  as well as the supporting evidence quoted from the diff.\n\n"
    "Your job is to refute clearly false accusations.\n\n"
    "TASK:\n"
    "1. Read the diff and previous assessment.\n"
    "2. Decide whether the previous 'not_safe' label is justified.\n"
    "3. Specifically, check whether:\n"
    "   - There is supporting evidence visible in the diff that enables the claimed risk.\n"
    "- Do NOT refute only because a variable appears to be uninitialized or its origin is unclear, or because you do not\n"
    "  see the full control flow; the unified diff may omit parts of the function.\n\n"
    "OUTPUT:\n"
    "Return EXACT JSON ONLY:\n"
    "{\n"
    '  "verdict": "confirm_not_safe" | "refute",\n'
    '  "reason": "1-3 sentences explaining why you confirm or refute",\n'
    "}\n\n"
    "Guidelines:\n"
    "- Use 'confirm_not_safe' if you can verify evidence in the diff supporting potentially dangerous new behavior or a security regression.\n"
    "- Use 'refute' if the change appears to be standard benign updates (error handling, logging, validation, etc.).\n"
)



# --------------------------------------------------------------------------------------
# Top-level entrypoints / exports
# --------------------------------------------------------------------------------------

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

    # Ground truth (optional)
    gt_path = opts.get("ground_truth")
    opts["_ground_truth"] = load_ground_truth_file(gt_path)
    if gt_path:
        logger.info(f"Loaded ground truth: {gt_path}")

    os.makedirs(outdir, exist_ok=True)

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
        pair_dir_name = f"{t_name}_to_{b_name}"
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
    # These paths are based on your copy script (note: 'synthetic' typo kept).
    layout = {
        # synthetic
        "s-libtiff-backdoored": "synthetic/libtiff-4.3.0/backdoored",
        "s-libtiff-safe": "synthetic/libtiff-4.3.0/safe",
        "s-libtiff-prev-safe": "synthetic/libtiff-4.3.0/prev-safe",
        "s-libxml2-backdoored": "synthetic/libxml2/backdoored",
        "s-libxml2-safe": "synthetic/libxml2/safe",
        "s-libxml2-prev-safe": "synthetic/libxml2/prev-safe",
        "s-libsndfile-backdoored": "synthetic/libsndfile/backdoored",
        "s-libsndfile-safe": "synthetic/libsndfile/safe",
        "s-libsndfile-prev-safe": "synthetic/libsndfile/prev-safe",
        "s-libpng-backdoored": "synthetic/libpng/backdoored",
        "s-libpng-safe": "synthetic/libpng/safe",
        "s-libpng-prev-safe": "synthetic/libpng/prev-safe",
        "s-lua-backdoored": "synthetic/lua/backdoored",
        "s-lua-safe": "synthetic/lua/safe",
        "s-lua-prev-safe": "synthetic/lua/prev-safe",
        "s-php-syn-backdoored": "synthetic/php/backdoored",
        "s-php-syn-safe": "synthetic/php/safe",
        "s-php-syn-prev-safe": "synthetic/php/prev-safe",
        "s-poppler-backdoored": "synthetic/poppler/backdoored",
        "s-poppler-safe": "synthetic/poppler/safe",
        "s-poppler-prev-safe": "synthetic/poppler/prev-safe",
        "s-sudo-backdoored": "synthetic/sudo/backdoored",
        "s-sudo-safe": "synthetic/sudo/safe",
        "s-sudo-prev-safe": "synthetic/sudo/prev-safe",
        "s-dropbear-backdoored": "synthetic/dropbear2024-86/backdoored",
        "s-dropbear-safe": "synthetic/dropbear2024-86/safe",
        "s-dropbear-prev-safe": "synthetic/dropbear2024-86/prev-safe",
        "s-openssl-backdoored": "synthetic/openssl-3.0.0/backdoored",
        "s-openssl-safe": "synthetic/openssl-3.0.0/safe",
        "s-openssl-prev-safe": "synthetic/openssl-3.0.0/prev-safe",
        "s-sqlite3-backdoored": "synthetic/sqlite3-3.37.0/backdoored",
        "s-sqlite3-safe": "synthetic/sqlite3-3.37.0/safe",
        "s-sqlite3-prev-safe": "synthetic/sqlite3-3.37.0/prev-safe",
        # authentic
        "s-proftpd-backdoored": "authentic/proftpd/backdoored",
        "s-proftpd-safe": "authentic/proftpd/safe",
        "s-proftpd-prev-safe": "authentic/proftpd/prev-safe",
        "s-php-auth-backdoored": "authentic/php/backdoored",
        "s-php-auth-safe": "authentic/php/safe",
        "s-php-auth-prev-safe": "authentic/php/prev-safe",
        "s-vsftpd-backdoored": "authentic/vsftpd/backdoored",
        "s-vsftpd-safe": "authentic/vsftpd/safe",
        "s-vsftpd-prev-safe": "authentic/vsftpd/prev-safe",
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
exports = [llm_filter, import_rosarum_samples]

# --------------------------------------------------------------------------------------
# Core pipeline
# --------------------------------------------------------------------------------------

def run_one_comparison(target: str, baseline: str, outdir: str, opts) -> Dict[str, Any]:
    """
    Run DRIFT for one target→baseline pair, triage all filtered modified functions,
    and compute ground-truth Hit metrics if a ground truth map is present in opts.
    """
    os.makedirs(outdir, exist_ok=True)

    filter_val = opts.get("filter", None)
    logger.info(
        f"→ Invoking drift (target='{target}', baseline='{baseline}', filter='{filter_val}')"
    )

    # Timer for this comparison (total)
    t_total0 = time.perf_counter()

    # -------------------------------------------------------------------------
    # 1) DRIFT (timed)
    # -------------------------------------------------------------------------
    t_drift0 = time.perf_counter()
    drift_res = run_drift(target, baseline, filter_val)
    drift_elapsed_s = time.perf_counter() - t_drift0

    drift_json = coerce_json_like(getattr(drift_res, "content", drift_res)) or {}
    write_json(os.path.join(outdir, "drift_raw.json"), dump_json_safe(drift_json))

    file_pairs: List[Dict[str, Any]] = drift_json.get("file_pairs", []) or []

    # -------------------------------------------------------------------------
    # 2) Human-readable report header
    # -------------------------------------------------------------------------
    report_lines: List[str] = []
    report_lines.append("# Firmware Triage Report (binary suspicion)")
    report_lines.append(f"Target CID:   {target}")
    try:
        t_name = oxide.api.get_colname_from_oid(target)
        report_lines.append(f"Target Name:  {t_name}")
    except Exception:
        t_name = str(target)
        report_lines.append("Target Name:  <unavailable>")

    report_lines.append(f"Baseline CID: {baseline}")
    try:
        b_name = oxide.api.get_colname_from_oid(baseline)
        report_lines.append(f"Baseline Name:{b_name}")
    except Exception:
        b_name = str(baseline)
        report_lines.append("Baseline Name:<unavailable>")

    if filter_val:
        report_lines.append(f"Filter:       {filter_val}")
    report_lines.append("")

    # -------------------------------------------------------------------------
    # 3) Aggregation containers
    # -------------------------------------------------------------------------
    triage_index: List[Dict[str, Any]] = []              # only final not_safe
    per_function_results: List[Dict[str, Any]] = []      # every filtered function

    total_modified_all = 0
    total_modified_filtered = 0

    n_flagged_filtered = 0
    n_safe_filtered = 0

    # stage1 vs reviewer bookkeeping (filtered only)
    analyst_identified = 0
    n_reviewer_refuted = 0
    n_reviewer_confirmed = 0

    # Timing breakdown accumulators (filtered functions only)
    sum_diff_elapsed_s = 0.0
    sum_stage1_elapsed_s = 0.0
    sum_reviewer_elapsed_s = 0.0
    sum_llm_elapsed_s = 0.0
    sum_stage1_attempts = 0
    sum_reviewer_attempts = 0

    if not file_pairs:
        report_lines.append("No file pairs or modifications were reported by drift.")
        logger.info("• No file pairs / modifications.")
    else:
        report_lines.append(f"Found {len(file_pairs)} file pair(s).\n")
        logger.info(f"• Processing {len(file_pairs)} file pair(s)…")

    # -------------------------------------------------------------------------
    # 4) Per-filepair triage
    # -------------------------------------------------------------------------
    for fp_idx, fp in enumerate(file_pairs, 1):
        baseline_oid = fp.get("baseline_oid")
        target_oid = fp.get("target_oid")
        filtered_mods = fp.get("modified_functions", []) or []
        excluded_mods = fp.get("excluded_functions", []) or []

        # Count all drift-reported modifications, including excluded by filter
        try:
            total_modified_all += len(filtered_mods) + len(excluded_mods)
        except Exception:
            # If excluded_mods is not sized, treat as 0
            total_modified_all += len(filtered_mods)

        total_modified_filtered += len(filtered_mods)

        report_lines.append(f"## File Pair {fp_idx}")
        report_lines.append(f"- target_oid:   {target_oid}")
        report_lines.append(f"- baseline_oid: {baseline_oid}")
        report_lines.append(f"- modified functions (filtered): {len(filtered_mods)}")
        if excluded_mods:
            try:
                report_lines.append(
                    f"- modified functions (excluded by filter): {len(excluded_mods)}"
                )
            except Exception:
                report_lines.append("- modified functions (excluded by filter): <unknown>")
        report_lines.append("")

        logger.info(
            f"   [fp {fp_idx}/{len(file_pairs)}] filtered={len(filtered_mods)}, "
            f"excluded={(len(excluded_mods) if hasattr(excluded_mods, '__len__') else 'unknown')}"
        )

        p = progress.Progress(len(filtered_mods))

        for func_idx, m in enumerate(filtered_mods, 1):
            baddr = ensure_decimal_str(m.get("baseline_func_addr"))
            taddr = ensure_decimal_str(m.get("target_func_addr"))

            res = analyze_function_pair(
                baseline_oid=baseline_oid,
                target_oid=target_oid,
                baddr=baddr,
                taddr=taddr,
                fp_idx=fp_idx,
                func_idx=func_idx,
                outdir=outdir,
                opts=opts,
            )

            # --- timing accumulation (requires analyze_function_pair to return these) ---
            sum_diff_elapsed_s += float(res.get("diff_elapsed_s") or 0.0)
            sum_stage1_elapsed_s += float(res.get("stage1_elapsed_s") or 0.0)
            sum_reviewer_elapsed_s += float(res.get("reviewer_elapsed_s") or 0.0)
            sum_llm_elapsed_s += float(res.get("llm_elapsed_s") or 0.0)
            sum_stage1_attempts += int(res.get("stage1_attempts") or 0)
            sum_reviewer_attempts += int(res.get("reviewer_attempts") or 0)

            # Record per-function row for evaluation and debugging
            per_function_results.append(
                {
                    "filepair_index": fp_idx,
                    "function_index": func_idx,
                    "baseline_oid": baseline_oid,
                    "target_oid": target_oid,
                    "baseline_addr": baddr,
                    "target_addr": taddr,

                    "final_label": res.get("label"),
                    "flagged_final": bool(res.get("flagged")),
                    "stage1_label": res.get("stage1_label"),
                    "refuted_by_reviewer": bool(res.get("refuted_by_reviewer")),
                    "confirmed_by_reviewer": bool(res.get("confirmed_by_reviewer")),

                    # OPTIONAL BUT RECOMMENDED: per-function timings
                    "diff_elapsed_s": float(res.get("diff_elapsed_s") or 0.0),
                    "stage1_elapsed_s": float(res.get("stage1_elapsed_s") or 0.0),
                    "reviewer_elapsed_s": float(res.get("reviewer_elapsed_s") or 0.0),
                    "llm_elapsed_s": float(res.get("llm_elapsed_s") or 0.0),
                    "stage1_attempts": int(res.get("stage1_attempts") or 0),
                    "reviewer_attempts": int(res.get("reviewer_attempts") or 0),

                    "triage_ran": bool(res.get("triage_ran")),
                    "failure_reason": res.get("failure_reason"),
                }
            )

            # Reviewer metrics (only meaningful when stage1 claimed not_safe)
            if res.get("stage1_label") == "not_safe":
                analyst_identified += 1
                if res.get("refuted_by_reviewer"):
                    n_reviewer_refuted += 1
                if res.get("confirmed_by_reviewer"):
                    n_reviewer_confirmed += 1

            # Final decision index (only include final not_safe)
            if res.get("flagged"):
                n_flagged_filtered += 1
                triage_index.append(
                    {
                        "filepair_index": fp_idx,
                        "function_index": func_idx,
                        "baseline_addr": baddr,
                        "target_addr": taddr,
                        "label": res.get("label"),
                        "why": res.get("why"),
                        "verdict": res.get("verdict"),
                        "dir": res.get("func_dir"),
                        "baseline_oid": baseline_oid,
                        "target_oid": target_oid,
                        "flagged": bool(res.get("flagged")),
                    }
                )
            else:
                n_safe_filtered += 1

            p.tick()

    # Treat excluded-by-filter functions as safe for "overall safe"
    overall_safe = n_safe_filtered + (total_modified_all - total_modified_filtered)

    # Total elapsed (includes drift + triage + I/O)
    elapsed_s = time.perf_counter() - t_total0

    # Derived breakdown: incremental triage time excluding DRIFT
    triage_elapsed_s_excluding_drift = max(0.0, elapsed_s - drift_elapsed_s)

    # Optional: "other overhead" not captured in diff + llm (parsing/writes/bookkeeping)
    other_elapsed_s = max(
        0.0,
        triage_elapsed_s_excluding_drift - (sum_diff_elapsed_s + sum_llm_elapsed_s),
    )

    # -------------------------------------------------------------------------
    # 5) Ground truth computation (optional, multi-function)
    # -------------------------------------------------------------------------
    gt = opts.get("_ground_truth") or {}
    gt_norm = get_ground_truth_for_target(gt, t_name)

    hit_final = None
    hit_stage1 = None
    gt_in_filtered = None

    gt_targets = None
    gt_compromised_count = None

    # Counts (only defined if gt provided)
    tp_final = None
    fp_final = None
    tp_stage1 = None
    fp_stage1 = None

    if gt_norm:
        gt_targets = gt_norm.get("targets", [])
        gt_compromised_count = len(gt_targets)

        # Whether any GT function appears in the filtered set we actually analyzed
        gt_in_filtered = any(gt_row_matches_any(r, gt_norm) for r in per_function_results)

        # Hit: at least one compromised function is identified
        hit_final = any(
            r.get("flagged_final") and gt_row_matches_any(r, gt_norm)
            for r in per_function_results
        )
        hit_stage1 = any(
            (r.get("stage1_label") == "not_safe") and gt_row_matches_any(r, gt_norm)
            for r in per_function_results
        )

        # TP/FP counts under multi-function ground truth:
        #   TP = flagged ∩ GT
        #   FP = flagged \ GT
        tp_final = sum(
            1 for r in per_function_results
            if r.get("flagged_final") and gt_row_matches_any(r, gt_norm)
        )
        fp_final = sum(
            1 for r in per_function_results
            if r.get("flagged_final") and not gt_row_matches_any(r, gt_norm)
        )

        tp_stage1 = sum(
            1 for r in per_function_results
            if (r.get("stage1_label") == "not_safe") and gt_row_matches_any(r, gt_norm)
        )
        fp_stage1 = sum(
            1 for r in per_function_results
            if (r.get("stage1_label") == "not_safe") and not gt_row_matches_any(r, gt_norm)
        )

    # -------------------------------------------------------------------------
    # 6) Stats (+ optional FP rate using multi-function GT)
    # -------------------------------------------------------------------------
    identified = len(triage_index)

    fp_rate_final = None
    fp_rate_stage1 = None

    if gt_norm and total_modified_all:
        # multi-function FP rates
        fp_rate_final = float(fp_final) / float(total_modified_all) if fp_final is not None else None
        fp_rate_stage1 = float(fp_stage1) / float(total_modified_all) if fp_stage1 is not None else None

    stats = {
        "target": target,
        "baseline": baseline,

        "total_modified_functions": total_modified_all,
        "filtered_functions": total_modified_filtered,
        "safe_overall": overall_safe,

        # Final labels (filtered only)
        "identified": identified,
        "final_not_safe_filtered": n_flagged_filtered,
        "final_safe_filtered": n_safe_filtered,

        # Stage1 vs reviewer bookkeeping (filtered only)
        "analyst_identified": analyst_identified,
        "reviewer_refuted": n_reviewer_refuted,
        "reviewer_confirmed": n_reviewer_confirmed,

        # ---- Timing (new) ----
        "elapsed_s": elapsed_s,                               # total wall time
        "drift_elapsed_s": drift_elapsed_s,                   # DRIFT only
        "triage_elapsed_s_excluding_drift": triage_elapsed_s_excluding_drift,

        # Aggregated triage-stage components (filtered functions only)
        "diff_elapsed_s": sum_diff_elapsed_s,                 # function_decomp_diff retrieve time
        "stage1_elapsed_s": sum_stage1_elapsed_s,             # analyst LLM time
        "reviewer_elapsed_s": sum_reviewer_elapsed_s,         # reviewer LLM time
        "llm_elapsed_s": sum_llm_elapsed_s,                   # stage1 + reviewer
        "other_elapsed_s": other_elapsed_s,                   # parsing/writes/etc.
        "stage1_attempts": sum_stage1_attempts,
        "reviewer_attempts": sum_reviewer_attempts,

        # ---- GT summary ----
        "gt_compromised_count": gt_compromised_count,
        "gt_targets": gt_targets,
        "gt_in_filtered": gt_in_filtered,

        "hit_final": hit_final,
        "hit_stage1": hit_stage1,

        "tp_final": tp_final,
        "fp_final": fp_final,
        "tp_stage1": tp_stage1,
        "fp_stage1": fp_stage1,

        # Rates (optional, but usually useful)
        "fp_rate_final": fp_rate_final,
        "fp_rate_stage1": fp_rate_stage1,
    }


    # -------------------------------------------------------------------------
    # 7) Write outputs
    # -------------------------------------------------------------------------
    write_text(os.path.join(outdir, "final_report.txt"), "\n".join(report_lines))
    write_json(os.path.join(outdir, "triage_index.json"), triage_index)
    write_json(os.path.join(outdir, "per_function_results.json"), per_function_results)
    write_json(os.path.join(outdir, "stats.json"), stats)

    logger.info(
        f"✓ Done {t_name} → {b_name}: "
        f"modified_all={total_modified_all}, filtered={total_modified_filtered}, "
        f"identified={identified}, hit_final={hit_final}, elapsed={elapsed_s:.2f}s "
        f"(drift={drift_elapsed_s:.2f}s, llm={sum_llm_elapsed_s:.2f}s)"
    )

    return {
        "target": target,
        "baseline": baseline,
        "stats": stats,
        "triage_index": triage_index,
        "per_function_results": per_function_results,
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

    # Track whether we actually ran the LLM triage graph, and why we didn't (if not).
    triage_ran = False
    failure_reason: Optional[str] = None

    diff_t0 = time.perf_counter()
    diff = oxide.retrieve(
        "function_decomp_diff",
        [target_oid, baseline_oid],
        {"target": taddr, "baseline": baddr, "raw": True},
    )
    diff_elapsed_s = time.perf_counter() - diff_t0

    # -------------------------------------------------------------------------
    # FAIL-CLOSED: if diff tool fails, label not_safe (do NOT silently mark safe)
    # -------------------------------------------------------------------------
    if isinstance(diff, dict) and "error" in diff:
        failure_reason = "diff_tool_error"
        notes["observations"].append(f"diff tool failed: {diff.get('error')!r}")
        write_json(notes_path, notes)
        write_text(os.path.join(func_dir, "diff.txt"), "")

        verdict = "Label: needs further inspection — diff generation failed (tool error)"
        write_json(
            os.path.join(func_dir, "analysis.json"),
            {
                "label": "not_safe",
                "why": "Diff generation failed (tool error); fail-closed to not_safe.",
                "flagged": True,
                "verdict": verdict,
                "stage1": {
                    "label": "not_safe",
                    "trigger": "",
                    "why": "Stage1 did not run because diff generation failed; fail-closed.",
                },
                "reviewer": None,
                "refuted_by_reviewer": False,
                "confirmed_by_reviewer": False,
                "triage_ran": False,
                "failure_reason": failure_reason,
                "timing": {
                    "diff_elapsed_s": diff_elapsed_s,
                    "stage1_elapsed_s": 0.0,
                    "reviewer_elapsed_s": 0.0,
                    "llm_elapsed_s": 0.0,
                    "stage1_attempts": 0,
                    "reviewer_attempts": 0,
                },
            },
        )
        write_text(os.path.join(func_dir, "verdict.txt"), verdict)

        return {
            "label": "not_safe",
            "why": "Diff generation failed (tool error); fail-closed to not_safe.",
            "flagged": True,
            "verdict": verdict,
            "func_dir": func_dir,
            "reviewer": None,
            "stage1_label": "not_safe",
            "refuted_by_reviewer": False,
            "confirmed_by_reviewer": False,
            "triage_ran": False,
            "failure_reason": failure_reason,
            "diff_elapsed_s": diff_elapsed_s,
            "stage1_elapsed_s": 0.0,
            "reviewer_elapsed_s": 0.0,
            "llm_elapsed_s": 0.0,
            "stage1_attempts": 0,
            "reviewer_attempts": 0,
        }

    diff_text = extract_content(diff) or ""
    write_text(os.path.join(func_dir, "diff.txt"), diff_text)

    parsed = coerce_json_like(diff_text)
    if isinstance(parsed, dict) and "unified" in parsed:
        unified = parsed.get("unified") or ""
    else:
        unified = diff_text

    # -------------------------------------------------------------------------
    # FAIL-CLOSED defaults: if triage is skipped (empty diff) we keep not_safe
    # -------------------------------------------------------------------------
    label = "not_safe"
    why = "Triage did not run or produced no usable diff; fail-closed to not_safe."
    flagged = True
    verdict = "Label: needs further inspection — triage did not run or produced no usable diff"

    label_stage1 = "not_safe"
    trigger_stage1 = ""
    why_stage1 = "Stage1 did not run; fail-closed to not_safe."
    reviewer_result: Optional[Dict[str, Any]] = None

    # timing defaults
    stage1_elapsed_s = 0.0
    reviewer_elapsed_s = 0.0
    llm_elapsed_s = 0.0
    stage1_attempts = 0
    reviewer_attempts = 0

    if unified.strip():
        triage_ran = True
        triage = run_triage_langgraph(
            unified_diff=unified,
            fp_idx=fp_idx,
            func_idx=func_idx,
            notes=notes,
        )

        triage_trace = triage.get("trace") or []

        # Extract LLM timings from trace
        timing = extract_llm_timings_from_trace(triage_trace)
        stage1_elapsed_s = float(timing["stage1_elapsed_s"])
        reviewer_elapsed_s = float(timing["reviewer_elapsed_s"])
        llm_elapsed_s = float(timing["llm_elapsed_s"])
        stage1_attempts = int(timing["stage1_attempts"])
        reviewer_attempts = int(timing["reviewer_attempts"])

        label = triage.get("label", "not_safe")
        why = (triage.get("why") or "").strip()

        # Stage1 result (before reviewer) for metrics
        label_stage1 = triage.get("stage1_label", label)
        trigger_stage1 = (triage.get("stage1_trigger") or "").strip()
        why_stage1 = (triage.get("stage1_why") or "").strip()

        reviewer_result = triage.get("reviewer")

        # Persist LangGraph + reviewer trace
        trace_payload = {
            "fp_index": fp_idx,
            "func_index": func_idx,
            "baseline_addr": baddr,
            "target_addr": taddr,
            "diff_chars": len(unified),
            "trace": triage_trace,
        }
        write_json(os.path.join(func_dir, "triage_trace.json"), trace_payload)
        notes["artifacts"].append({"kind": "triage_trace", "path": "triage_trace.json"})
    else:
        # FAIL-CLOSED: empty unified diff => keep not_safe defaults
        failure_reason = "empty_unified_diff"
        notes["observations"].append("empty unified diff; fail-closed to not_safe")

        trace_payload = {
            "fp_index": fp_idx,
            "func_index": func_idx,
            "baseline_addr": baddr,
            "target_addr": taddr,
            "diff_chars": len(unified or ""),
            "trace": [{"node": "triage_skipped", "reason": "empty unified diff"}],
        }
        write_json(os.path.join(func_dir, "triage_trace.json"), trace_payload)
        notes["artifacts"].append({"kind": "triage_trace", "path": "triage_trace.json"})

    # Did the reviewer overturn or confirm a stage1 "not_safe"?
    refuted_by_reviewer = bool(label_stage1 == "not_safe" and label == "safe")
    confirmed_by_reviewer = bool(
        label_stage1 == "not_safe"
        and label == "not_safe"
        and reviewer_result
        and reviewer_result.get("verdict") == "confirm_not_safe"
    )

    flagged = (label == "not_safe")
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
            "stage1": {"label": label_stage1, "trigger": trigger_stage1, "why": why_stage1},
            "reviewer": reviewer_result,
            "refuted_by_reviewer": refuted_by_reviewer,
            "confirmed_by_reviewer": confirmed_by_reviewer,
            "triage_ran": triage_ran,
            "failure_reason": failure_reason,
            "timing": {
                "diff_elapsed_s": diff_elapsed_s,
                "stage1_elapsed_s": stage1_elapsed_s,
                "reviewer_elapsed_s": reviewer_elapsed_s,
                "llm_elapsed_s": llm_elapsed_s,
                "stage1_attempts": stage1_attempts,
                "reviewer_attempts": reviewer_attempts,
            },
        },
    )
    write_text(os.path.join(func_dir, "verdict.txt"), verdict)

    return {
        "label": label,
        "why": why,
        "flagged": flagged,
        "verdict": verdict,
        "func_dir": func_dir,
        "reviewer": reviewer_result,
        "stage1_label": label_stage1,
        "refuted_by_reviewer": refuted_by_reviewer,
        "confirmed_by_reviewer": confirmed_by_reviewer,
        "triage_ran": triage_ran,
        "failure_reason": failure_reason,
        "diff_elapsed_s": diff_elapsed_s,
        "stage1_elapsed_s": stage1_elapsed_s,
        "reviewer_elapsed_s": reviewer_elapsed_s,
        "llm_elapsed_s": llm_elapsed_s,
        "stage1_attempts": stage1_attempts,
        "reviewer_attempts": reviewer_attempts,
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

def _invoke_llm_text(llm: ChatOllama, system_text: str, human_text: str) -> Tuple[str, float]:
    t0 = time.perf_counter()
    resp = llm.invoke(
        [
            SystemMessage(content=system_text),
            HumanMessage(content=human_text),
        ]
    )
    dt = time.perf_counter() - t0
    text = ascii_sanitize((getattr(resp, "content", "") or "")).strip()
    return text, dt


def _coerce_label(x: Any) -> str:
    return _coerce_str(x).lower().replace("-", "_")


def _analyst_output_complete(d: Dict[str, Any]) -> bool:
    label = _coerce_label(d.get("label"))
    trigger = _coerce_str(d.get("trigger"))
    why = _coerce_str(d.get("why"))

    if label not in {"safe", "not_safe"}:
        return False
    if not why:
        return False
    # If the analyst says not_safe, require a concrete trigger
    if label == "not_safe" and not trigger:
        return False
    return True


def call_analyst_llm_json(
    diff_text: str, fp_idx: int, func_idx: int, notes: Dict[str, Any]
) -> Tuple[str, Dict[str, Any], Dict[str, Any]]:
    """
    Returns: (raw_text, stage1_dict, meta)

    Fail-closed behavior:
      - If we cannot obtain valid/complete JSON after one retry, return not_safe.
    """
    meta: Dict[str, Any] = {"attempts": 0, "parsed_ok": False, "repaired": False}

    # Attempt 1
    meta["attempts"] += 1
    raw1, dt1 = _invoke_llm_text(
        LLM,
        ANALYST_SYS,
        f"FUNCTION UNIFIED DIFF:\n{diff_text}",
    )
    if not raw1:
        notes["observations"].append("LLM analyst returned empty content; retrying once.")
    d1 = parse_llm_json(raw1)
    if isinstance(d1, dict) and _analyst_output_complete(d1):
        meta["parsed_ok"] = True
        meta["duration_s"] = dt1
        return raw1, {
            "label": _coerce_label(d1.get("label")),
            "trigger": _coerce_str(d1.get("trigger")),
            "why": _coerce_str(d1.get("why")),
        }, meta

    # Attempt 2 (repair / retry)
    meta["attempts"] += 1
    meta["repaired"] = True
    notes["observations"].append("Analyst output invalid/incomplete; retrying once (repair).")

    repair_sys = (
        ANALYST_SYS
        + "\nConstraints:\n"
          "- Output must be a single JSON object.\n"
          "- Field 'why' must be non-empty.\n"
          "- If label is 'not_safe', field 'trigger' must be a non-empty exact condition copied from the diff.\n"
          "- If you cannot provide a trigger, label must be 'safe'.\n"
    )
    repair_human = (
        "You must produce valid JSON that satisfies the constraints.\n"
        "Return JSON only.\n\n"
        "FUNCTION UNIFIED DIFF:\n"
        f"{diff_text}\n\n"
        "PRIOR (possibly invalid) OUTPUT:\n"
        f"{raw1}\n"
    )

    raw2, dt2 = _invoke_llm_text(LLM, repair_sys, repair_human)
    d2 = parse_llm_json(raw2)
    if isinstance(d2, dict) and _analyst_output_complete(d2):
        meta["parsed_ok"] = True
        meta["duration_s"] = dt1 + dt2
        return raw2, {
            "label": _coerce_label(d2.get("label")),
            "trigger": _coerce_str(d2.get("trigger")),
            "why": _coerce_str(d2.get("why")),
        }, meta

    # Fail closed
    meta["parsed_ok"] = False
    meta["duration_s"] = dt1 + dt2
    notes["observations"].append("Analyst JSON parse/validation failed twice; fail-closed to not_safe.")
    fallback = {
        "label": "not_safe",
        "trigger": "",
        "why": "Analyst JSON parse/validation failed; fail-closed to not_safe.",
    }
    return (raw2 or raw1), fallback, meta


def _reviewer_output_complete(d: Dict[str, Any]) -> bool:
    verdict = _coerce_str(d.get("verdict")).lower()
    reason = _coerce_str(d.get("reason"))
    if verdict not in {"confirm_not_safe", "refute"}:
        return False
    if not reason:
        return False
    return True


def run_reviewer_review(
    unified_diff: str,
    stage1_result: Dict[str, Any],
    fp_idx: int,
    func_idx: int,
    notes: Dict[str, Any],
) -> Tuple[str, Dict[str, Any], Dict[str, Any]]:
    """
    Returns: (raw_text, reviewer_dict, meta)

    Fail-closed behavior:
      - If reviewer output is invalid after one retry, keep not_safe (confirm_not_safe).
    """
    meta: Dict[str, Any] = {"attempts": 0, "parsed_ok": False, "repaired": False}

    reviewer_prompt = (
        "=== FUNCTION UNIFIED DIFF ===\n"
        f"{unified_diff}\n\n"
        "=== EARLIER ASSESSMENT JSON ===\n"
        f"{json.dumps(stage1_result, indent=2)}\n"
    )

    # Attempt 1
    meta["attempts"] += 1
    raw1, dt1 = _invoke_llm_text(REVIEWER_LLM, REVIEWER_SYS, reviewer_prompt)
    d1 = parse_llm_json(raw1)
    if isinstance(d1, dict) and _reviewer_output_complete(d1):
        meta["parsed_ok"] = True
        meta["duration_s"] = dt1
        return raw1, {"verdict": _coerce_str(d1.get("verdict")).lower(), "reason": _coerce_str(d1.get("reason"))}, meta

    # Attempt 2 (repair)
    meta["attempts"] += 1
    meta["repaired"] = True
    notes["observations"].append("Reviewer output invalid/incomplete; retrying once (repair).")

    repair_sys = (
        REVIEWER_SYS
        + "\nConstraints:\n"
          "- Output must be a single JSON object.\n"
          "- 'reason' must be non-empty.\n"
    )
    repair_human = (
        "Return JSON only.\n\n"
        + reviewer_prompt
        + "\nPRIOR (possibly invalid) OUTPUT:\n"
        + raw1
        + "\n"
    )
    raw2, dt2 = _invoke_llm_text(REVIEWER_LLM, repair_sys, repair_human)
    d2 = parse_llm_json(raw2)
    if isinstance(d2, dict) and _reviewer_output_complete(d2):
        meta["parsed_ok"] = True
        meta["duration_s"] = dt1 + dt2
        return raw2, {"verdict": _coerce_str(d2.get("verdict")).lower(), "reason": _coerce_str(d2.get("reason"))}, meta

    # Fail closed: keep the alert
    meta["parsed_ok"] = False
    meta["duration_s"] = dt1 + dt2
    notes["observations"].append("Reviewer JSON parse/validation failed twice; keeping not_safe (fail-closed).")
    fallback = {
        "verdict": "confirm_not_safe",
        "reason": "Reviewer JSON parse/validation failed; keeping not_safe (fail-closed).",
    }
    return (raw2 or raw1), fallback, meta


# --------------------------------------------------------------------------------------
# LangGraph state + graph
# --------------------------------------------------------------------------------------


class TriageState(TypedDict, total=False):
    # Inputs
    diff: str
    fp_idx: int
    func_idx: int
    notes: Dict[str, Any]

    # Raw model outputs (optional, for debugging)
    analyst_raw: Optional[str]
    reviewer_raw: Optional[str]

    # Parsed JSON artifacts
    stage1_json: Optional[Dict[str, Any]]   # analyst result (strict, fail-closed)
    reviewer_json: Optional[Dict[str, Any]] # reviewer result (strict, fail-open)
    final_json: Optional[Dict[str, Any]]    # final decision after reviewer gate

    # Trace
    trace: List[Dict[str, Any]]


def _coerce_str(x: Any) -> str:
    if x is None:
        return ""
    try:
        return str(x).strip()
    except Exception:
        return ""


def _build_triage_graph():
    """
    Two-node LangGraph:

        START -> analyst -> (END if safe, reviewer if not_safe) -> END

    No formatting/normalization steps.
    Strict parsing:
      - Analyst: if JSON invalid or label not exactly {"safe","not_safe"}, fail-closed to not_safe.
      - Reviewer: if JSON invalid or verdict not exactly "confirm_not_safe", treat as refute.
    """
    graph = StateGraph(TriageState)

    def analyst_node(state: TriageState) -> TriageState:
        diff = state["diff"]
        fp_idx = state["fp_idx"]
        func_idx = state["func_idx"]
        notes = state["notes"]

        raw_text, stage1, meta = call_analyst_llm_json(
            diff_text=diff,
            fp_idx=fp_idx,
            func_idx=func_idx,
            notes=notes,
        )

        trace = list(state.get("trace", []))
        trace.append(
            {
                "node": "analyst",
                "attempts": meta.get("attempts"),
                "parsed_ok": meta.get("parsed_ok"),
                "repaired": meta.get("repaired"),
                "duration_s": meta.get("duration_s"),
                "input_diff_chars": len(diff),
                "output_len": len(raw_text or ""),
                "stage1_label": stage1.get("label"),
                "stage1_trigger_preview": (stage1.get("trigger") or "")[:200],
                "stage1_why_preview": (stage1.get("why") or "")[:400],
                "output_preview": (raw_text or "")[:400],
            }
        )

        return {
            "analyst_raw": raw_text,
            "stage1_json": stage1,
            "final_json": dict(stage1),  # provisional until reviewer (if invoked)
            "trace": trace,
        }


    def reviewer_node(state: TriageState) -> TriageState:
        diff = state["diff"]
        fp_idx = state["fp_idx"]
        func_idx = state["func_idx"]
        notes = state["notes"]

        stage1 = state.get("stage1_json") or state.get("final_json") or {}
        stage1_label = _coerce_label(stage1.get("label"))

        if stage1_label != "not_safe":
            return {}

        reviewer_raw, reviewer_json, meta = run_reviewer_review(
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

        verdict = _coerce_str(reviewer_json.get("verdict")).lower()
        reason = _coerce_str(reviewer_json.get("reason"))

        # Strict fail-closed gate: only explicit 'refute' makes it safe.
        if verdict == "refute":
            final = {
                "label": "safe",
                "trigger": "",
                "why": reason or "Reviewer refuted not_safe; treating as safe.",
            }
            reviewer_json_norm = {"verdict": "refute", "reason": reason}
        else:
            final = {
                "label": "not_safe",
                "trigger": _coerce_str(stage1.get("trigger")),
                "why": (
                    f"{_coerce_str(stage1.get('why'))} | Reviewer: {reason}"
                    if reason
                    else (_coerce_str(stage1.get("why")) or "Reviewer confirmed not_safe.")
                ),
            }
            reviewer_json_norm = {"verdict": "confirm_not_safe", "reason": reason}

        trace = list(state.get("trace", []))
        trace.append(
            {
                "node": "reviewer",
                "attempts": meta.get("attempts"),
                "parsed_ok": meta.get("parsed_ok"),
                "repaired": meta.get("repaired"),
                "duration_s": meta.get("duration_s"),
                "verdict": reviewer_json_norm["verdict"],
                "reason_preview": (reviewer_json_norm.get("reason") or "")[:400],
                "output_preview": (reviewer_raw or "")[:400],
            }
        )

        return {
            "reviewer_raw": reviewer_raw,
            "reviewer_json": reviewer_json_norm,
            "final_json": final,
            "trace": trace,
        }


    def route_after_analyst(state: TriageState) -> str:
        stage1 = state.get("stage1_json") or {}
        label = _coerce_str(stage1.get("label")).lower()
        return "reviewer" if label == "not_safe" else "end"

    graph.add_node("analyst", analyst_node)
    graph.add_node("reviewer", reviewer_node)

    graph.add_edge(START, "analyst")
    graph.add_conditional_edges(
        "analyst",
        route_after_analyst,
        {"reviewer": "reviewer", "end": END},
    )
    graph.add_edge("reviewer", END)

    return graph.compile()

def show_and_save_triage_graph_png(path: str = "triage_graph.png") -> None:
    # TRIAGE_GRAPH is the compiled app from _build_triage_graph()
    g = TRIAGE_GRAPH.get_graph()

    try:
        png_bytes = g.draw_mermaid_png()
    except Exception as e:
        print(f"Failed to render mermaid PNG: {e}")
        return

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
       "stage1_why", "reviewer"}.
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
            "reviewer": None,
        }

    final = result_state.get("final_json") or {}
    stage1 = result_state.get("stage1_json") or final
    reviewer = result_state.get("reviewer_json")
    trace = result_state.get("trace") or []

    if not isinstance(final, dict):
        final = {
            "label": "not_safe",
            "trigger": "",
            "why": f"internal error: unexpected graph output {final!r}",
        }

    # Final label (after reviewer), fail-closed
    label_raw = str(final.get("label", "not_safe")).strip().lower().replace("-", "_")
    if label_raw not in ("safe", "not_safe"):
        label = "not_safe"
    else:
        label = label_raw

    why = (final.get("why") or "").strip()
    trigger = (final.get("trigger") or "").strip()

    # Stage1 (pre-reviewer) normalization, also fail-closed
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
        "reviewer": reviewer,
    }


# --------------------------------------------------------------------------------------
# Utilities
# --------------------------------------------------------------------------------------

def extract_llm_timings_from_trace(trace: List[Dict[str, Any]]) -> Dict[str, Any]:
    """
    Extract stage timings from LangGraph trace entries.
    Returns:
      {
        "stage1_elapsed_s": float,
        "reviewer_elapsed_s": float,
        "llm_elapsed_s": float,
        "stage1_attempts": int,
        "reviewer_attempts": int,
      }
    """
    stage1_s = 0.0
    reviewer_s = 0.0
    stage1_attempts = 0
    reviewer_attempts = 0

    for ev in (trace or []):
        node = (ev.get("node") or "").strip().lower()
        if node == "analyst":
            stage1_s = float(ev.get("duration_s") or 0.0)
            stage1_attempts = int(ev.get("attempts") or 0)
        elif node == "reviewer":
            reviewer_s = float(ev.get("duration_s") or 0.0)
            reviewer_attempts = int(ev.get("attempts") or 0)

    return {
        "stage1_elapsed_s": stage1_s,
        "reviewer_elapsed_s": reviewer_s,
        "llm_elapsed_s": stage1_s + reviewer_s,
        "stage1_attempts": stage1_attempts,
        "reviewer_attempts": reviewer_attempts,
    }


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

_CODE_FENCE_START_RE = re.compile(r"^\s*```[a-zA-Z0-9_-]*\s*\n?")
_CODE_FENCE_END_RE = re.compile(r"\n?\s*```\s*$")

def strip_code_fences(s: str) -> str:
    s = (s or "").strip()
    if s.startswith("```"):
        s = _CODE_FENCE_START_RE.sub("", s)
        s = _CODE_FENCE_END_RE.sub("", s)
    return s.strip()

def parse_llm_json(text: str) -> Optional[dict]:
    """Parse model output which should be JSON.

    Strategy: strip code fences -> json.loads -> balanced-object extraction -> None.
    """
    if not text:
        return None
    text = strip_code_fences(text)
    try:
        return json.loads(text)
    except Exception:
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

def load_ground_truth_file(path: Optional[str]) -> Dict[str, Any]:
    """
    Loads ground truth JSON shaped like:
      { "samples": { "<target_collection_name>": { "backdoor": { "target_addr": "...", "target_oid": ... }}}}
    Returns the parsed dict or {}.
    """
    if not path:
        return {}
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception as e:
        logger.error(f"Failed to load ground truth file '{path}': {e}")
        return {}


def get_ground_truth_for_target(gt: Dict[str, Any], target_name: str) -> Optional[Dict[str, Any]]:
    """
    New convention:
      { "samples": { "<target_name>": { "backdoor": { "targets": [ {target_addr, target_oid?}, ... ]}}}}

    Returns a normalized object for fast membership checks:
      {
        "targets": [{"target_addr_dec": str, "target_oid": Optional[str]}, ...],
        "addr_set": set([addr_dec, ...]),
        "addr_oid_set": set([(addr_dec, oid_norm), ...])
      }
    """
    if not isinstance(gt, dict) or not target_name:
        return None

    samples = gt.get("samples")
    if not isinstance(samples, dict):
        return None

    entry = samples.get(target_name)
    if not isinstance(entry, dict):
        return None

    backdoor = entry.get("backdoor")
    if not isinstance(backdoor, dict):
        return None

    targets_raw = backdoor.get("targets")
    if not isinstance(targets_raw, list) or not targets_raw:
        return None

    targets: List[Dict[str, Any]] = []
    addr_set: Set[str] = set()
    addr_oid_set: Set[Tuple[str, Optional[str]]] = set()

    for t in targets_raw:
        if not isinstance(t, dict):
            continue
        addr = t.get("target_addr")
        if addr is None:
            continue

        addr_dec = ensure_decimal_str(addr)

        oid = t.get("target_oid", None)
        oid_norm = str(oid) if oid is not None else None

        targets.append({"target_addr_dec": addr_dec, "target_oid": oid_norm})
        addr_set.add(addr_dec)
        addr_oid_set.add((addr_dec, oid_norm))

    if not targets:
        return None

    return {"targets": targets, "addr_set": addr_set, "addr_oid_set": addr_oid_set}


def gt_row_matches_any(row: Dict[str, Any], gt_norm: Dict[str, Any]) -> bool:
    """
    True iff this per-function row matches ANY GT target function for the sample.
    Requires row contains: target_addr, target_oid (target_oid may be None).
    """
    if not gt_norm:
        return False

    row_addr = ensure_decimal_str(row.get("target_addr"))
    if row_addr not in gt_norm["addr_set"]:
        return False

    # If you don't store OIDs in GT, this becomes an addr-only match.
    row_oid = row.get("target_oid", None)
    row_oid_norm = str(row_oid) if row_oid is not None else None

    # exact match if present
    if (row_addr, row_oid_norm) in gt_norm["addr_oid_set"]:
        return True

    if (row_addr, None) in gt_norm["addr_oid_set"]:
        return True

    return False