import json
import logging
import os
import re
import unicodedata
import time
from typing import Any, Dict, List, Optional, Tuple
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
LLM = ChatOllama(
    model="gpt-oss:120b",
    temperature=0.0,
    num_ctx=8192,
    keep_alive="10m",
    request_timeout=60.0,
    model_kwargs={"num_predict": 128},
)
FORMAT_LLM = ChatOllama(model="llama3.1:8b-instruct-q4_K_M", temperature=0.0)
NORMALIZE_LLM = ChatOllama(model="llama3.1:8b-instruct-q4_K_M", temperature=0.0)
# Second-stage reviewer / reviewer model
REVIEWER_LLM = ChatOllama(
    model="gpt-oss:120b",
    temperature=0.0,
    num_ctx=8192,
    keep_alive="10m",
    request_timeout=60.0,
    model_kwargs={"num_predict": 128},
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
    return series_summary


def test_diff(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Evaluate the function_decomp_diff module with normalize set to True/False.

    For each modified function reported by DRIFT, we:
      - request a unified diff without normalization
      - request a unified diff with normalization
      - measure the size (chars/lines) of each
      - record per-function and aggregate reduction statistics

    Expected calling patterns:
      • test_diff([target, baseline], opts)
      • test_diff([], {"entries": path, ...}) with a plaintext file of CIDs/names
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
        logger.info(f"[test_diff] Single comparison: {args[0]} → {args[1]}")
    else:
        raise ValueError(
            "test_diff: pass either [target, baseline] or --entries with at least two lines."
        )

    outdir: str = opts.get("outdir", "out_test_diff")
    os.makedirs(outdir, exist_ok=True)

    filter_val = opts.get("filter", None)
    annotate = bool(opts.get("annotate", False))

    per_function_rows: List[Dict[str, Any]] = []
    comparison_rows: List[Dict[str, Any]] = []

    total_pairs = len(pairs)
    logger.info(f"[test_diff] Starting {total_pairs} comparison(s)…")

    for idx, (target, baseline) in enumerate(pairs, 1):
        try:
            t_name = oxide.api.get_colname_from_oid(target)
        except Exception:
            t_name = str(target)
        try:
            b_name = oxide.api.get_colname_from_oid(baseline)
        except Exception:
            b_name = str(baseline)

        logger.info(f"[test_diff] [{idx}/{total_pairs}] {t_name} → {b_name}")

        pair_dir_name = f"testdiff_{idx:03d}__{t_name}_to_{b_name}"
        pair_dir = os.path.join(outdir, pair_dir_name)
        os.makedirs(pair_dir, exist_ok=True)

        t0 = time.perf_counter()
        drift_json = run_drift(target, baseline, filter_val) or {}
        file_pairs: List[Dict[str, Any]] = drift_json.get("file_pairs", []) or []

        if not file_pairs:
            logger.info(
                f"[test_diff] [{idx}] No file pairs / modifications reported by drift."
            )

        pair_total_plain_chars = 0
        pair_total_norm_chars = 0
        pair_total_plain_lines = 0
        pair_total_norm_lines = 0
        pair_func_count = 0

        for fp_idx, fp in enumerate(file_pairs, 1):
            baseline_oid = fp.get("baseline_oid")
            target_oid = fp.get("target_oid")
            modified = fp.get("modified_functions", []) or []

            logger.info(
                f"[test_diff]   [fp {fp_idx}/{len(file_pairs)}] "
                f"modified={len(modified)}"
            )

            for func_idx, m in enumerate(modified, 1):
                baddr = ensure_decimal_str(m.get("baseline_func_addr"))
                taddr = ensure_decimal_str(m.get("target_func_addr"))

                error_msgs: List[str] = []

                # --- plain (unnormalized) diff ---
                plain_unified = ""
                try:
                    raw_plain = oxide.retrieve(
                        "function_decomp_diff",
                        [target_oid, baseline_oid],
                        {
                            "target": taddr,
                            "baseline": baddr,
                            "annotate": annotate,
                            "normalize": False,
                        },
                    )
                    plain_text = extract_content(raw_plain) or ""
                    parsed_plain = coerce_json_like(plain_text)
                    if isinstance(parsed_plain, dict) and "unified" in parsed_plain:
                        plain_unified = parsed_plain.get("unified") or ""
                    else:
                        plain_unified = plain_text
                except Exception as e:
                    msg = f"plain diff error: {e}"
                    logger.error(
                        f"[test_diff] plain diff failed "
                        f"(pair={idx}, fp={fp_idx}, func={func_idx}): {e}"
                    )
                    error_msgs.append(msg)

                # --- normalized diff ---
                norm_unified = ""
                try:
                    raw_norm = oxide.retrieve(
                        "function_decomp_diff",
                        [target_oid, baseline_oid],
                        {
                            "target": taddr,
                            "baseline": baddr,
                            "annotate": annotate,
                            "normalize": True,
                        },
                    )
                    norm_text = extract_content(raw_norm) or ""
                    parsed_norm = coerce_json_like(norm_text)
                    if isinstance(parsed_norm, dict) and "unified" in parsed_norm:
                        norm_unified = parsed_norm.get("unified") or ""
                    else:
                        norm_unified = norm_text
                except Exception as e:
                    msg = f"normalized diff error: {e}"
                    logger.error(
                        f"[test_diff] normalized diff failed "
                        f"(pair={idx}, fp={fp_idx}, func={func_idx}): {e}"
                    )
                    error_msgs.append(msg)

                # If both failed, skip this function.
                if not plain_unified and not norm_unified:
                    per_function_rows.append(
                        {
                            "comparison_index": idx,
                            "filepair_index": fp_idx,
                            "function_index": func_idx,
                            "target": target,
                            "baseline": baseline,
                            "target_oid": target_oid,
                            "baseline_oid": baseline_oid,
                            "target_addr": taddr,
                            "baseline_addr": baddr,
                            "error": "; ".join(error_msgs) if error_msgs else None,
                        }
                    )
                    continue

                plain_chars = len(plain_unified)
                norm_chars = len(norm_unified)

                plain_lines = plain_unified.count("\n") + (1 if plain_unified else 0)
                norm_lines = norm_unified.count("\n") + (1 if norm_unified else 0)

                pair_total_plain_chars += plain_chars
                pair_total_norm_chars += norm_chars
                pair_total_plain_lines += plain_lines
                pair_total_norm_lines += norm_lines
                pair_func_count += 1

                char_delta = plain_chars - norm_chars
                char_fraction = (norm_chars / plain_chars) if plain_chars else None

                line_delta = plain_lines - norm_lines
                line_fraction = (norm_lines / plain_lines) if plain_lines else None

                per_function_rows.append(
                    {
                        "comparison_index": idx,
                        "filepair_index": fp_idx,
                        "function_index": func_idx,
                        "target": target,
                        "baseline": baseline,
                        "target_oid": target_oid,
                        "baseline_oid": baseline_oid,
                        "target_addr": taddr,
                        "baseline_addr": baddr,
                        "plain_chars": plain_chars,
                        "normalized_chars": norm_chars,
                        "char_delta": char_delta,
                        "char_fraction": char_fraction,
                        "plain_lines": plain_lines,
                        "normalized_lines": norm_lines,
                        "line_delta": line_delta,
                        "line_fraction": line_fraction,
                        "error": "; ".join(error_msgs) if error_msgs else None,
                    }
                )

        dt = time.perf_counter() - t0

        comp_summary = {
            "index": idx,
            "target": target,
            "baseline": baseline,
            "target_name": t_name,
            "baseline_name": b_name,
            "n_file_pairs": len(file_pairs),
            "n_modified_functions": pair_func_count,
            "total_plain_chars": pair_total_plain_chars,
            "total_normalized_chars": pair_total_norm_chars,
            "total_plain_lines": pair_total_plain_lines,
            "total_normalized_lines": pair_total_norm_lines,
            "avg_plain_chars": (
                pair_total_plain_chars / pair_func_count if pair_func_count else 0.0
            ),
            "avg_normalized_chars": (
                pair_total_norm_chars / pair_func_count if pair_func_count else 0.0
            ),
            "avg_plain_lines": (
                pair_total_plain_lines / pair_func_count if pair_func_count else 0.0
            ),
            "avg_normalized_lines": (
                pair_total_norm_lines / pair_func_count if pair_func_count else 0.0
            ),
            "overall_char_fraction": (
                (pair_total_norm_chars / pair_total_plain_chars)
                if pair_total_plain_chars
                else None
            ),
            "overall_line_fraction": (
                (pair_total_norm_lines / pair_total_plain_lines)
                if pair_total_plain_lines
                else None
            ),
            "elapsed_s": dt,
        }

        comparison_rows.append(comp_summary)
        write_json(os.path.join(pair_dir, "test_diff_pair_summary.json"), comp_summary)

        logger.info(
            f"[test_diff] [{idx}] functions={pair_func_count}, "
            f"chars: {pair_total_plain_chars}→{pair_total_norm_chars}, "
            f"lines: {pair_total_plain_lines}→{pair_total_norm_lines}, "
            f"time={dt:.2f}s"
        )

    # ---- global summary ----
    total_plain_chars = sum(c["total_plain_chars"] for c in comparison_rows)
    total_norm_chars = sum(c["total_normalized_chars"] for c in comparison_rows)
    total_plain_lines = sum(c["total_plain_lines"] for c in comparison_rows)
    total_norm_lines = sum(c["total_normalized_lines"] for c in comparison_rows)
    total_funcs = sum(c["n_modified_functions"] for c in comparison_rows)

    global_summary: Dict[str, Any] = {
        "total_pairs": len(comparison_rows),
        "total_functions": total_funcs,
        "total_plain_chars": total_plain_chars,
        "total_normalized_chars": total_norm_chars,
        "total_plain_lines": total_plain_lines,
        "total_normalized_lines": total_norm_lines,
        "overall_char_fraction": (
            (total_norm_chars / total_plain_chars) if total_plain_chars else None
        ),
        "overall_line_fraction": (
            (total_norm_lines / total_plain_lines) if total_plain_lines else None
        ),
        "comparisons": comparison_rows,
    }

    write_json(os.path.join(outdir, "test_diff_summary.json"), global_summary)
    write_json(
        os.path.join(outdir, "test_diff_per_function.json"),
        {"functions": per_function_rows},
    )

    if total_plain_chars:
        logger.info(
            "[test_diff] DONE: %d functions, chars %d→%d (%.2f%%), lines %d→%d (%.2f%%)",
            total_funcs,
            total_plain_chars,
            total_norm_chars,
            100.0 * (total_norm_chars / total_plain_chars),
            total_plain_lines,
            total_norm_lines,
            (
                100.0 * (total_norm_lines / total_plain_lines)
                if total_plain_lines
                else 0.0
            ),
        )
    else:
        logger.info("[test_diff] DONE: no modified functions found.")

    return global_summary


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
exports = [llm_filter, import_rosarum_samples, test_diff]

# --------------------------------------------------------------------------------------
# Core pipeline
# --------------------------------------------------------------------------------------

def run_one_comparison(target: str, baseline: str, outdir: str, opts) -> Dict[str, Any]:
    """
    Run DRIFT for one target→baseline pair, triage all filtered modified functions,
    and compute ground-truth Hit metrics if a ground truth map is present in opts.

    Expects (optional):
      opts["_ground_truth"] loaded from your ground_truth.json
      helpers: get_ground_truth_for_target(gt, target_name) and gt_row_matches(row, addr_dec, oid)
    """
    os.makedirs(outdir, exist_ok=True)

    filter_val = opts.get("filter", None)
    logger.info(
        f"→ Invoking drift (target='{target}', baseline='{baseline}', filter='{filter_val}')"
    )

    # Timer for this comparison
    t0 = time.perf_counter()

    # -------------------------------------------------------------------------
    # 1) DRIFT
    # -------------------------------------------------------------------------
    drift_res = run_drift(target, baseline, filter_val)
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

    elapsed_s = time.perf_counter() - t0

    # -------------------------------------------------------------------------
    # 5) Ground truth hit computation (optional)
    # -------------------------------------------------------------------------
    gt = opts.get("_ground_truth") or {}
    gt_norm = get_ground_truth_for_target(gt, t_name)

    hit_final = None
    hit_stage1 = None
    gt_in_filtered = None
    gt_target_addr = None
    gt_target_oid = None

    if gt_norm:
        gt_target_addr = gt_norm.get("target_addr_dec")
        gt_target_oid = gt_norm.get("target_oid")

        gt_in_filtered = any(
            gt_row_matches(r, gt_target_addr, gt_target_oid)
            for r in per_function_results
        )

        hit_final = any(
            gt_row_matches(r, gt_target_addr, gt_target_oid) and r.get("flagged_final")
            for r in per_function_results
        )

        hit_stage1 = any(
            gt_row_matches(r, gt_target_addr, gt_target_oid)
            and (r.get("stage1_label") == "not_safe")
            for r in per_function_results
        )

    # -------------------------------------------------------------------------
    # 6) Stats (+ optional BF rate)
    # -------------------------------------------------------------------------
    identified = len(triage_index)
    bf_rate = None
    if gt_norm is not None and gt_norm and total_modified_all:
        hit_int = 1 if hit_final else 0
        bf_rate = (identified - hit_int) / float(total_modified_all)

    stats = {
        "target": target,
        "baseline": baseline,

        "total_modified_functions": total_modified_all,
        "filtered_functions": total_modified_filtered,
        "safe_overall": overall_safe,

        # Counts from final labels (filtered only)
        "identified": identified,
        "final_not_safe_filtered": n_flagged_filtered,
        "final_safe_filtered": n_safe_filtered,

        # Stage1 vs reviewer bookkeeping (filtered only)
        "analyst_identified": analyst_identified,
        "reviewer_refuted": n_reviewer_refuted,
        "reviewer_confirmed": n_reviewer_confirmed,

        # Timing
        "elapsed_s": elapsed_s,

        # Ground truth fields (if present)
        "gt_target_addr": gt_target_addr,
        "gt_target_oid": gt_target_oid,
        "gt_in_filtered": gt_in_filtered,
        "hit_final": hit_final,
        "hit_stage1": hit_stage1,
        "bf_rate": bf_rate,
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
        f"identified={identified}, hit_final={hit_final}, elapsed={elapsed_s:.2f}s"
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

    diff_raw = oxide.retrieve(
        "function_decomp_diff_test",
        [target_oid, baseline_oid],
        {"target": taddr, "baseline": baddr, "raw": False},
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
                "reviewer": None,
            },
        )
        write_text(os.path.join(func_dir, "verdict.txt"), verdict)
        return {
            "label": "safe",
            "why": "no diff available",
            "flagged": False,
            "verdict": verdict,
            "func_dir": func_dir,
            "reviewer": None,
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
    reviewer_result: Optional[Dict[str, Any]] = None

    # ------------------------
    # 2) LLM triage via LangGraph (+ reviewer)
    # ------------------------
    if unified.strip():
        triage = run_triage_langgraph(
            unified_diff=unified,
            fp_idx=fp_idx,
            func_idx=func_idx,
            notes=notes,
        )

        triage_trace = triage.get("trace") or []

        # Final decision from graph (after reviewer)
        label = triage.get("label", "safe")
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
        notes["artifacts"].append(
            {
                "kind": "triage_trace",
                "path": "triage_trace.json",
            }
        )

    # Did the reviewer overturn or confirm a stage1 "not_safe"?
    refuted_by_reviewer = bool(label_stage1 == "not_safe" and label == "safe")
    confirmed_by_reviewer = bool(
        label_stage1 == "not_safe"
        and label == "not_safe"
        and reviewer_result
        and reviewer_result.get("verdict") == "confirm_not_safe"
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
            "reviewer": reviewer_result,
            "refuted_by_reviewer": refuted_by_reviewer,
            "confirmed_by_reviewer": confirmed_by_reviewer,
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

        logger.debug(
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

        logger.debug(
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

        logger.debug(
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


def call_reviewer_llm(
    diff_text: str,
    stage1_result: Dict[str, Any],
    fp_idx: int,
    func_idx: int,
    notes: Dict[str, Any],
) -> str:
    """
    Second-stage reviewer: tries to refute 'not_safe' labels.
    Returns JSON text (verdict/refute) or a fallback JSON on failure.
    """
    t_llm = time.perf_counter()

    reviewer_prompt = (
        "=== FUNCTION UNIFIED DIFF ===\n"
        f"{diff_text}\n\n"
        "=== EARLIER ASSESSMENT JSON ===\n"
        f"{json.dumps(stage1_result, indent=2)}\n"
    )

    try:
        resp = REVIEWER_LLM.invoke(
            [
                SystemMessage(content=REVIEWER_SYS),
                HumanMessage(content=ascii_sanitize(reviewer_prompt)),
            ]
        )
        text_local = ascii_sanitize((getattr(resp, "content", "") or "")).strip()
        dt_llm = time.perf_counter() - t_llm

        logger.debug(
            f"LLM REVIEWER OK fp={fp_idx} func={func_idx} "
            f"took {dt_llm:.2f}s (diff_chars={len(diff_text)})"
        )

        if not text_local:
            raise ValueError("LLM (reviewer) returned empty content")

        return text_local

    except Exception as e:
        dt_llm = time.perf_counter() - t_llm
        err_msg = f"LLM REVIEWER failed fp={fp_idx} func={func_idx}: {e}"
        logger.error(
            f"LLM REVIEWER ERROR fp={fp_idx} func={func_idx} "
            f"after {dt_llm:.2f}s: {e}"
        )
        notes["observations"].append(err_msg)

        # Fallback: fail-closed and keep the alert.
        fallback_json = json.dumps(
            {
                "verdict": "confirm_not_safe",
                "reason": f"Reviewer LLM failed: {str(e)}",
            }
        )
        return fallback_json


def run_reviewer_review(
    unified_diff: str,
    stage1_result: Dict[str, Any],
    fp_idx: int,
    func_idx: int,
    notes: Dict[str, Any],
) -> Dict[str, Any]:
    """
    Run the reviewer LLM and normalize its output into:
      {verdict, reason}
    """
    text = call_reviewer_llm(
        diff_text=unified_diff,
        stage1_result=stage1_result,
        fp_idx=fp_idx,
        func_idx=func_idx,
        notes=notes,
    )

    data = parse_llm_json(text)
    if not isinstance(data, dict):
        msg = "Reviewer LLM output was not valid JSON; keeping stage1 not_safe label."
        notes["observations"].append(msg)
        return {
            "verdict": "confirm_not_safe",
            "reason": msg,
        }

    verdict_raw = str(data.get("verdict", "confirm_not_safe")).strip().lower()

    if verdict_raw in {"confirm_not_safe", "confirm", "not_safe", "unsafe"}:
        verdict = "confirm_not_safe"
    else:
        verdict = "confirm_not_safe"

    reason_raw = data.get("reason", "")
    try:
        reason = str(reason_raw).strip()
    except Exception:
        reason = ""

    return {
        "verdict": verdict,
        "reason": reason,
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

    # NEW: keep stage1 (pre-reviewer) + reviewer result
    stage1_json: Optional[Dict[str, Any]]
    reviewer_json: Optional[Dict[str, Any]]

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

    def reviewer_node(state: TriageState) -> TriageState:
        diff = state["diff"]
        fp_idx = state["fp_idx"]
        func_idx = state["func_idx"]
        notes = state["notes"]

        stage1 = state.get("stage1_json") or state.get("final_json") or {}

        t0 = time.perf_counter()
        reviewer = run_reviewer_review(
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

        verdict_s = reviewer.get("verdict", "refute")

        # Normalize stage1 label
        stage1_label_raw = (
            str(stage1.get("label", "safe")).strip().lower().replace("-", "_")
        )
        stage1_label = "not_safe" if stage1_label_raw == "not_safe" else "safe"

        final_label = stage1_label
        final_why = (stage1.get("why") or "").strip()
        trigger = (stage1.get("trigger") or "").strip()

        if stage1_label == "not_safe":
            if verdict_s == "confirm_not_safe":
                reason_extra = (reviewer.get("reason") or "").strip()
                if reason_extra:
                    final_why = (
                        f"{final_why} | Reviewer: {reason_extra}"
                        if final_why
                        else f"Reviewer: {reason_extra}"
                    )
            else:
                final_label = "safe"
                final_why = (
                    reviewer.get("reason")
                    or "Second-stage reviewer did not confirm the backdoor; treating as safe."
                )

        final = {
            "label": final_label,
            "trigger": trigger,
            "why": final_why,
        }

        trace = list(state.get("trace", []))
        trace.append(
            {
                "node": "reviewer",
                "duration_s": dt,
                "verdict": verdict_s,
                "reason_preview": (reviewer.get("reason") or "")[:400],
            }
        )

        return {
            "final_json": final,
            "stage1_json": stage1,
            "reviewer_json": reviewer,
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
            return "needs_reviewer"
        return "end"

    # --- Wire up the graph -------------------------------------------------

    graph.add_node("analyst", analyst_node)
    graph.add_node("format", format_node)
    graph.add_node("normalize", normalize_node)
    graph.add_node("finalize", finalize_node)
    graph.add_node("reviewer", reviewer_node)

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

    # NEW: finalize -> (reviewer | END)
    graph.add_conditional_edges(
        "finalize",
        route_after_finalize,
        {
            "needs_reviewer": "reviewer",
            "end": END,
        },
    )

    # Reviewer always ends
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
    Returns a normalized dict:
      {"target_addr_dec": "<decimal str>", "target_oid": Optional[str]}
    or None if no ground truth for this target_name.
    """
    if not gt or not target_name:
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

    addr = backdoor.get("target_addr")
    if addr is None:
        return None

    target_addr_dec = ensure_decimal_str(addr)

    oid = backdoor.get("target_oid", None)
    target_oid = str(oid) if oid is not None else None

    return {"target_addr_dec": target_addr_dec, "target_oid": target_oid}


def gt_row_matches(
    row: Dict[str, Any],
    gt_target_addr: str,
    gt_target_oid: Optional[str],
) -> bool:
    """
    row is a per-function record containing at least: target_addr, target_oid
    """
    if ensure_decimal_str(row.get("target_addr")) != gt_target_addr:
        return False
    if gt_target_oid and str(row.get("target_oid")) != str(gt_target_oid):
        return False
    return True
