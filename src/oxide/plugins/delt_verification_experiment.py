from __future__ import annotations

import ast
import configparser
import glob
import hashlib
import importlib.metadata
import json
import logging
import os
import platform
import queue
import re
import socket
import subprocess
import threading
import time
import urllib.error
import urllib.request
from collections import Counter
from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Optional, Tuple

from oxide.core import oxide as oxide
from oxide.core.oxide import api

from oxide.modules.analyzers.delt_verification.pipeline.utils.ground_truth import (
    get_ground_truth_for_target,
    gt_row_matches_any,
    load_ground_truth_file,
)
from oxide.modules.analyzers.delt_verification.pipeline.utils.text_utils import comparison_dir_name

NAME = "delt_verification_experiment"
logger = logging.getLogger(NAME)
logging.getLogger("httpx").setLevel(logging.WARNING)

FP_BINS: Tuple[Tuple[str, int, Optional[int]], ...] = (
    ("0", 0, 0),
    ("1", 1, 1),
    ("2-5", 2, 5),
    ("6-10", 6, 10),
    ("11-25", 11, 25),
    (">25", 26, None),
)


EXPERIMENT_CONFIGS: Tuple[Tuple[str, str, Optional[str], Dict[str, Any]], ...] = (
    ("bounded", "processed", "Call_OR_Control_Modified", {"skip_unbounded": True}),
    ("bounded_all", "processed", "none", {"skip_unbounded": True}),
    ("bounded_raw", "raw", "Call_OR_Control_Modified", {"skip_unbounded": True}),
    ("unbounded", "processed", "Call_OR_Control_Modified", {"skip_bounded": True}),
)


def _read_json(path: str) -> Any:
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def _write_json(path: str, data: Any) -> None:
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(data, handle, indent=2, ensure_ascii=False, default=str)


def _read_series_file(path: str, sep: str = ",") -> List[Tuple[str, str]]:
    """Read a series file where each non-comment line is `coll_old, coll_new`.

    Returns a list of (cid_left, cid_right) tuples, resolving collection names to
    collection IDs. Copied from the `drift` plugin so this experiment has no
    dependency on it.
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
            cid_left = api.get_cid_from_name(left_name)
            cid_right = api.get_cid_from_name(right_name)
            if not cid_left:
                raise ValueError(
                    f"Unknown target collection {left_name!r} in {path}."
                )
            if not cid_right:
                raise ValueError(
                    f"Unknown baseline collection {right_name!r} in {path}."
                )
            pairs.append((cid_left, cid_right))

    return pairs


def _comparison_dir(target: str, baseline: str) -> str:
    return comparison_dir_name(str(target), str(baseline))


def _parse_models_file(path: str) -> List[Tuple[str, int]]:
    """Parse a models file. Each non-comment line is `model_tag [sample_workers]`
    (whitespace- or comma-separated); sample_workers defaults to 1."""
    specs: List[Tuple[str, int]] = []
    with open(path, "r", encoding="utf-8") as handle:
        for raw_line in handle:
            line = raw_line.split("#", 1)[0].strip()
            if not line:
                continue
            parts = line.replace(",", " ").split()
            model = parts[0]
            sample_workers = int(parts[1]) if len(parts) > 1 else 1
            if sample_workers < 1:
                raise ValueError(f"sample_workers must be >= 1 for model '{model}' (got {sample_workers}).")
            specs.append((model, sample_workers))
    if not specs:
        raise ValueError(f"Models file '{path}' contained no models.")
    return specs


def _model_slug(model: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]+", "_", str(model)).strip("_") or "model"


def _resolve_model_specs(opts: Dict[str, Any]) -> Tuple[List[Tuple[str, int]], bool, bool]:
    """Return (model_specs, nested, dry_run). Each spec is (model, sample_workers).
    `nested` is True when results should live under a per-model subdirectory (multi-model
    runs); False keeps the flat single-model layout. `dry_run` is True when no model was
    given: the pipeline then produces every bounded input (unified diffs + added-callee
    context) without running the agent, for ground-truth authoring."""
    models_path = opts.get("models")
    if models_path:
        return _parse_models_file(models_path), True, False
    model = opts.get("model")
    if not model:
        # No model -> dry run: produce bounded inputs only, no LLM.
        return [("dry_run", 1)], False, True
    sample_workers = int(opts.get("sample_workers") or 1)
    if sample_workers < 1:
        raise ValueError(f"--sample_workers must be >= 1 (got {sample_workers}).")
    return [(str(model), sample_workers)], False, False


def _run_one_comparison(target: str, baseline: str, outdir: str, opts: Dict[str, Any]) -> Dict[str, Any]:
    call_opts = dict(opts)
    call_opts["outdir"] = outdir
    return api.retrieve("delt_verification", [target, baseline], call_opts) or {}


GT_ONLY_MARKER = "gt_only.marker"


def _sample_is_complete(sample_outdir: str, gt_only: bool = False) -> bool:
    if not os.path.exists(os.path.join(sample_outdir, "stats.json")):
        return False
    return gt_only or not os.path.exists(os.path.join(sample_outdir, GT_ONLY_MARKER))


def _refresh_cached_stats_ground_truth(
    pair_dir: str,
    stats: Dict[str, Any],
    gt: Dict[str, Any],
    target_name: str,
    target_oid: Optional[str] = None,
) -> Dict[str, Any]:
    gt_norm = get_ground_truth_for_target(
        gt,
        target_name,
        pair_dir=pair_dir,
        target_oid=target_oid or stats.get("target"),
    )
    if not gt_norm:
        return stats

    per_function_path = os.path.join(pair_dir, "per_function_results.json")
    if not os.path.exists(per_function_path):
        logger.warning("Cannot refresh ground truth for %s: missing per_function_results.json", pair_dir)
        return stats

    per_function_results = _read_json(per_function_path)
    if not isinstance(per_function_results, list):
        logger.warning("Cannot refresh ground truth for %s: per_function_results.json is not a list", pair_dir)
        return stats

    gt_target_count = len(gt_norm.get("targets", []) or [])
    gt_retained = 0
    counts = {"hit": 0, "dismissed": 0, "failed": 0}
    bounded_counts = {"hit": 0, "dismissed": 0, "failed": 0}

    def _outcome(label: Any, flagged: Any) -> str:
        if flagged:
            return "hit"
        return "failed" if label in {"failed", "skipped"} else "dismissed"

    for row in per_function_results:
        if not isinstance(row, dict):
            continue
        if not gt_row_matches_any(row, gt_norm):
            continue
        gt_retained += 1
        # Rows written before unbounded existed carry no pipeline label; fall back to
        # the bounded label so a refreshed older run stays internally consistent.
        counts[
            _outcome(
                row.get("pipeline_label") or row.get("bounded_label"),
                row.get("pipeline_flagged", row.get("bounded_flagged")),
            )
        ] += 1
        bounded_counts[_outcome(row.get("bounded_label"), row.get("bounded_flagged"))] += 1

    refreshed = dict(stats)
    refreshed.update(
        {
            "gt_sample_key": gt_norm.get("sample_key"),
            "gt_target_count": gt_target_count,
            "gt_retained": gt_retained,
            **counts,
        }
    )
    _write_json(os.path.join(pair_dir, "stats.json"), refreshed)

    stage_path = os.path.join(pair_dir, "stage_metrics.json")
    if os.path.exists(stage_path):
        stage_metrics = _read_json(stage_path)
        if isinstance(stage_metrics, dict) and isinstance(stage_metrics.get("bounded"), dict):
            stage_metrics["bounded"].update(bounded_counts)
            _write_json(stage_path, stage_metrics)
    return refreshed


def _process_pair(
    idx: int,
    total: int,
    target: str,
    baseline: str,
    category_outdir: str,
    run_opts: Dict[str, Any],
    gt: Optional[Dict[str, Any]],
) -> Dict[str, Any]:
    try:
        target_name = oxide.api.get_colname_from_oid(target)
    except Exception:
        target_name = str(target)
    if isinstance(target_name, set):
        target_name = next(iter(sorted(str(x) for x in target_name)), str(target))
    if not target_name:
        target_name = str(target)
    try:
        baseline_name = oxide.api.get_colname_from_oid(baseline)
    except Exception:
        baseline_name = str(baseline)
    if isinstance(baseline_name, set):
        baseline_name = next(iter(sorted(str(x) for x in baseline_name)), str(baseline))
    if not baseline_name:
        baseline_name = str(baseline)

    pair_dir = os.path.join(category_outdir, _comparison_dir(target_name, baseline_name))
    if _sample_is_complete(pair_dir, bool(run_opts.get("gt_only"))):
        logger.info("[%d/%d] %s -> %s (cached)", idx, total, target_name, baseline_name)
        stats = _read_json(os.path.join(pair_dir, "stats.json"))
        if gt:
            stats = _refresh_cached_stats_ground_truth(pair_dir, stats, gt, target_name, target)
        stage_metrics = _read_json(os.path.join(pair_dir, "stage_metrics.json"))
    else:
        logger.info("[%d/%d] START %s -> %s", idx, total, target_name, baseline_name)
        pair_t0 = time.perf_counter()
        result = _run_one_comparison(target, baseline, pair_dir, run_opts)
        marker = os.path.join(pair_dir, GT_ONLY_MARKER)
        if run_opts.get("gt_only"):
            os.makedirs(pair_dir, exist_ok=True)
            open(marker, "w").close()
        elif os.path.exists(marker):
            os.remove(marker)
        stats = result.get("stats")
        stage_metrics = result.get("stage_metrics")
        # Without a finish line an interleaved run shows only starts, so there is no way
        # to tell which samples are still in flight or how long any of them took.
        summary = stats if isinstance(stats, dict) else {}
        logger.info(
            "[%d/%d] DONE %s in %.1fm (%d filtered, %d investigated, %d flagged, %d failed)",
            idx, total, target_name, (time.perf_counter() - pair_t0) / 60.0,
            int(summary.get("filtered_functions") or 0),
            int(summary.get("investigated_functions") or 0),
            int(summary.get("flagged_functions") or 0),
            int(summary.get("failed_functions") or 0),
        )

    row = dict(stats) if isinstance(stats, dict) else {}
    # Carried in memory only, for the per-stage columns of the summary. stats.json on disk
    # stays a clean tool-wide record with no stage fields in it.
    if isinstance(stage_metrics, dict):
        row["_stage_metrics"] = stage_metrics
    index = _candidate_index(_pair_candidates(pair_dir), os.path.basename(pair_dir))
    row["_index"] = index
    row["_candidates"] = _candidate_metrics(index)
    row["_trace"] = _pair_trace_metrics(pair_dir)
    return row


DEFAULT_OLLAMA_URL = "http://127.0.0.1:11434"
# qwen3.6:35b-a3b's native context. Pinned so every worker is sized alike; see launch().
DEFAULT_CONTEXT_LENGTH = 262144
DEFAULT_OLLAMA_BASE_PORT = 11435


def _explicit_endpoints(opts: Dict[str, Any]) -> List[str]:
    """Ollama base URLs given by the caller, if any."""
    raw = opts.get("endpoints") or opts.get("ollama_base_urls") or os.getenv("DELT_ENDPOINTS")
    if isinstance(raw, (list, tuple)):
        return [str(u).strip() for u in raw if str(u).strip()]
    return [u.strip() for u in str(raw or "").split(",") if u.strip()]


def _endpoint_serves_model(base_url: str, model: str, timeout: float = 5.0) -> Optional[str]:
    """None if base_url is serving `model`, else a one-line reason why not."""
    url = base_url.rstrip("/") + "/api/tags"
    try:
        with urllib.request.urlopen(url, timeout=timeout) as resp:
            payload = json.loads(resp.read().decode("utf-8", errors="replace"))
    except Exception as exc:  # noqa: BLE001 — any failure here is a config error to report
        return f"unreachable ({exc!r})"
    names = {str(entry.get("name") or "") for entry in (payload.get("models") or [])}
    if model not in names:
        listed = ", ".join(sorted(names)[:4]) or "none"
        return f"reachable but does not serve {model!r} (has: {listed})"
    return None


def _preflight_endpoints(endpoints: List[str], model: str) -> None:
    """Fail before any comparison runs if an endpoint cannot serve the model.

    Without this a dead or misconfigured endpoint just makes every model call raise
    ConnectError, and the run still writes a full set of stats.json files reporting zero
    detections -- an infrastructure failure that reads exactly like a model result.
    """
    problems = [(url, why) for url in endpoints if (why := _endpoint_serves_model(url, model))]
    if not problems:
        logger.info("endpoint preflight ok: %d endpoint(s) serving %s", len(endpoints), model)
        return
    detail = "\n".join(f"  {url}: {why}" for url, why in problems)
    raise RuntimeError(
        f"{len(problems)} of {len(endpoints)} Ollama endpoint(s) cannot serve {model!r}:\n{detail}\n"
        "Fix the endpoints (or drop --endpoints to let the run launch its own) and retry."
    )


def _free_port_block(base_port: int, count: int, limit: int = 200) -> int:
    """First port p >= base_port where p .. p+count-1 are all unused.

    Ports near the Ollama default are often already taken -- 11435 in particular may
    belong to another user's server -- so scan rather than fail on the first collision.
    """
    for start in range(base_port, base_port + limit):
        if all(_port_is_free(start + offset) for offset in range(count)):
            return start
    raise RuntimeError(
        f"No block of {count} free ports found at or above {base_port}."
    )


def _port_is_free(port: int) -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.settimeout(0.3)
        return sock.connect_ex(("127.0.0.1", port)) != 0


def _get_gpu_uuids() -> List[str]:
    """Return GPU UUIDs from nvidia-smi, or [] if unavailable."""
    try:
        out = subprocess.check_output(["nvidia-smi", "-L"], text=True, stderr=subprocess.DEVNULL)
        return [
            line.split("UUID: ")[1].rstrip(")")
            for line in out.strip().splitlines()
            if "UUID:" in line
        ]
    except Exception:
        return []


@dataclass
class _ManagedOllama:
    proc: "subprocess.Popen[bytes]"
    base_url: str


class OllamaManager:
    """Launch and manage Ollama subprocess instances for multi-GPU parallel runs."""

    def __init__(self) -> None:
        self._instances: List[_ManagedOllama] = []

    @staticmethod
    def _candidate_model_dirs() -> List[str]:
        candidates: List[str] = []
        for raw in (
            os.environ.get("OLLAMA_MODELS"),
            os.path.expanduser("~/.ollama/models"),
            "/usr/share/ollama/.ollama/models",
        ):
            path = str(raw or "").strip()
            if not path or path in candidates:
                continue
            candidates.append(path)
        return candidates

    @classmethod
    def _manifest_path(cls, root: str, model: str) -> str:
        name, tag = model.split(":", 1) if ":" in model else (model, "latest")
        return os.path.join(root, "manifests", "registry.ollama.ai", "library", name, tag)

    @classmethod
    def _select_model_dir(cls, model: str) -> str:
        for path in cls._candidate_model_dirs():
            if os.path.isfile(cls._manifest_path(path, model)):
                return path
        for path in cls._candidate_model_dirs():
            if os.path.isdir(os.path.join(path, "manifests")) and os.path.isdir(
                os.path.join(path, "blobs")
            ):
                return path
        return str(os.environ.get("OLLAMA_MODELS") or os.path.expanduser("~/.ollama/models"))

    def launch(
        self,
        n: int,
        model: str,
        base_port: int = DEFAULT_OLLAMA_BASE_PORT,
        context_length: int = DEFAULT_CONTEXT_LENGTH,
    ) -> List[str]:
        gpu_uuids = _get_gpu_uuids()
        models_dir = self._select_model_dir(model)
        logger.info("OllamaManager: using OLLAMA_MODELS=%s", models_dir)
        urls: List[str] = []
        for i in range(n):
            port = base_port + i
            base_url = f"http://127.0.0.1:{port}"
            self._ensure_port_available(port)
            env = dict(os.environ)
            env["OLLAMA_HOST"] = f"127.0.0.1:{port}"
            env["OLLAMA_MAX_LOADED_MODELS"] = "1"
            env["OLLAMA_NUM_PARALLEL"] = "1"
            env["OLLAMA_KEEP_ALIVE"] = "-1"
            # Ollama otherwise sizes the context from whatever VRAM is free when each
            # server loads, so identical cards can end up on different tiers and the run is
            # no longer reproducible. Pinned to the model's native length, which was
            # measured resident at 29GB of 48GB fully on GPU. This is server capacity, not
            # a model option: nothing is added to the request.
            env["OLLAMA_CONTEXT_LENGTH"] = str(context_length)
            env["OLLAMA_MODELS"] = models_dir
            if gpu_uuids and i < len(gpu_uuids):
                env["CUDA_VISIBLE_DEVICES"] = str(i)
                logger.info("OllamaManager: worker %d -> GPU %d port %d", i, i, port)
            else:
                env.pop("CUDA_VISIBLE_DEVICES", None)
                logger.info("OllamaManager: worker %d -> CPU/shared port %d", i, port)
            proc = subprocess.Popen(
                ["ollama", "serve"], env=env,
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            )
            self._instances.append(_ManagedOllama(proc=proc, base_url=base_url))
            urls.append(base_url)
        for inst in self._instances:
            self._wait_ready(inst.base_url)
            self._warmup(inst.base_url, model)
        return urls

    @staticmethod
    def _ensure_port_available(port: int) -> None:
        if not _port_is_free(port):
            raise RuntimeError(
                f"Ollama worker port {port} is already in use. "
                "Choose a different --ollama_base_port or stop the existing server."
            )

    def _wait_ready(self, base_url: str, timeout: float = 120.0) -> None:
        deadline = time.perf_counter() + timeout
        while time.perf_counter() < deadline:
            try:
                with urllib.request.urlopen(base_url + "/", timeout=2) as resp:
                    if "Ollama is running" in resp.read().decode("utf-8", errors="replace"):
                        return
            except Exception:
                pass
            time.sleep(0.5)
        raise RuntimeError(f"Ollama at {base_url} did not become ready within {timeout:.0f}s")

    def _warmup(self, base_url: str, model: str) -> None:
        show_req = urllib.request.Request(
            base_url + "/api/show",
            data=json.dumps({"model": model}).encode(),
            headers={"Content-Type": "application/json"},
        )
        gen_req = urllib.request.Request(
            base_url + "/api/generate",
            data=json.dumps({"model": model, "prompt": "", "keep_alive": -1}).encode(),
            headers={"Content-Type": "application/json"},
        )
        try:
            with urllib.request.urlopen(show_req, timeout=30) as resp:
                resp.read()
            with urllib.request.urlopen(gen_req, timeout=120) as resp:
                resp.read()
        except urllib.error.HTTPError as exc:
            try:
                body = exc.read().decode("utf-8", errors="replace").strip()
            except Exception:
                body = ""
            if body:
                logger.warning(
                    "OllamaManager: warmup failed at %s: HTTP %s %s | %s",
                    base_url, exc.code, exc.reason, body[:400],
                )
            else:
                logger.warning("OllamaManager: warmup failed at %s: %r", base_url, exc)
        except Exception as exc:
            logger.warning("OllamaManager: warmup failed at %s: %r", base_url, exc)

    def shutdown(self) -> None:
        for inst in self._instances:
            try:
                inst.proc.terminate()
                inst.proc.wait(timeout=5)
            except Exception:
                try:
                    inst.proc.kill()
                except Exception:
                    pass
        self._instances.clear()


def _provision_sample_endpoints(
    opts: Dict[str, Any], sample_workers: int
) -> Tuple[List[str], Any]:
    """Return (endpoints, manager) ready for use, or raise explaining what is wrong.

    Explicit endpoints (the `endpoints` opt or DELT_ENDPOINTS) are used as given. Otherwise
    one Ollama server per GPU is launched for the run and shut down afterwards. Either way
    every endpoint is verified to serve the model before any comparison starts; `manager`
    is None when nothing was launched and must otherwise be shut down by the caller.
    """
    model = str(opts.get("model") or "")
    explicit = _explicit_endpoints(opts)
    if explicit:
        logger.info("using %d caller-supplied endpoint(s)", len(explicit))
        _preflight_endpoints(explicit, model)
        return explicit, None

    if sample_workers <= 1:
        _preflight_endpoints([DEFAULT_OLLAMA_URL], model)
        return [], None

    base_port = _free_port_block(
        int(opts.get("ollama_base_port") or DEFAULT_OLLAMA_BASE_PORT), sample_workers
    )
    logger.info(
        "launching %d Ollama server(s) for this run on ports %d-%d (one per GPU)",
        sample_workers, base_port, base_port + sample_workers - 1,
    )
    manager = OllamaManager()
    endpoints = manager.launch(
        sample_workers, model, base_port=base_port,
        context_length=int(opts.get("context_length") or DEFAULT_CONTEXT_LENGTH),
    )
    try:
        # OllamaManager only logs a warning when warmup fails, so a server can come up
        # pointed at the wrong model store and 404 every call. Verify before running.
        _preflight_endpoints(endpoints, model)
        _verify_residency(endpoints, model)
    except Exception:
        manager.shutdown()
        raise
    return endpoints, manager


def _resident_model(base_url: str, model: str, timeout: float = 10.0) -> Dict[str, Any]:
    """What the endpoint currently holds for `model`, from /api/ps."""
    try:
        with urllib.request.urlopen(base_url.rstrip("/") + "/api/ps", timeout=timeout) as resp:
            loaded = json.loads(resp.read().decode("utf-8", errors="replace")).get("models") or []
    except Exception as exc:  # noqa: BLE001
        return {"error": repr(exc)}
    for entry in loaded:
        if entry.get("name") == model or entry.get("model") == model:
            return entry
    return {}


def _verify_residency(endpoints: List[str], model: str) -> None:
    """Fail the run if the workers are not all holding the model the same way.

    Ollama sizes the context and the GPU/CPU split from whatever VRAM is free when each
    server loads, so identical cards can end up with different contexts and with layers on
    the CPU. A partly-offloaded 30B model cannot answer inside the per-call timeout, and the
    run then spends hours turning that into thousands of indistinguishable timeouts. Cheaper
    to refuse here.
    """
    problems: List[str] = []
    contexts = set()
    for url in endpoints or [DEFAULT_OLLAMA_URL]:
        resident = _resident_model(url, model)
        if resident.get("error"):
            problems.append(f"  {url}: unreachable ({resident['error']})")
            continue
        if not resident:
            problems.append(f"  {url}: warmed up but not holding {model!r}")
            continue
        size, in_vram = int(resident.get("size") or 0), int(resident.get("size_vram") or 0)
        context = resident.get("context_length")
        contexts.add(context)
        on_gpu = (in_vram / size) if size else 0.0
        logger.info(
            "%s: %s resident, context %s, %.0f%% on GPU", url, model, context, 100 * on_gpu
        )
        if size and on_gpu < 0.99:
            problems.append(
                f"  {url}: only {100 * on_gpu:.0f}% of the model is on the GPU "
                f"(context {context}); it will not answer inside the call timeout"
            )
    if len(contexts) > 1:
        problems.append(
            f"  workers disagree on context length: {sorted(str(c) for c in contexts)}; "
            "set OLLAMA_CONTEXT_LENGTH so every worker is sized the same"
        )
    if problems:
        raise RuntimeError(
            "Ollama workers are not in a usable state:\n" + "\n".join(problems) + "\n"
            "Free the GPUs (check for other ollama servers holding VRAM) and retry."
        )
    logger.info("residency check ok: %d worker(s) fully on GPU at one context", len(endpoints or [1]))


def _run_category(
    pairs: List[Tuple[str, str]],
    category_outdir: str,
    run_opts: Dict[str, Any],
    *,
    gt: Optional[Dict[str, Any]] = None,
    sample_workers: int = 1,
    endpoints: Optional[List[str]] = None,
) -> List[Dict[str, Any]]:
    """Run every comparison in a category, returning rows in the input pair order.

    Parallelism is at the sample level: each worker runs whole comparisons end to end, so
    bounded, binary context, and unbounded all run concurrently across workers. Workers
    pull from a shared queue, which self-balances the very uneven per-sample function
    counts without needing to know them up front.
    """
    os.makedirs(category_outdir, exist_ok=True)
    total = len(pairs)
    endpoints = list(endpoints or [])

    if sample_workers <= 1 or total <= 1:
        return [
            _process_pair(idx, total, target, baseline, category_outdir, run_opts, gt)
            for idx, (target, baseline) in enumerate(pairs, 1)
        ]

    n_workers = min(sample_workers, total)
    work: "queue.Queue[Tuple[int, str, str]]" = queue.Queue()
    for idx, (target, baseline) in enumerate(pairs, 1):
        work.put((idx, target, baseline))
    results: Dict[int, Dict[str, Any]] = {}
    results_lock = threading.Lock()

    def _worker(worker_idx: int) -> None:
        # One endpoint per worker, so each worker's runtime gets its own model client.
        worker_opts = dict(run_opts)
        if endpoints:
            worker_opts["ollama_base_url"] = endpoints[worker_idx % len(endpoints)]
        while True:
            try:
                idx, target, baseline = work.get_nowait()
            except queue.Empty:
                return
            try:
                row = _process_pair(idx, total, target, baseline, category_outdir, worker_opts, gt)
            except Exception as exc:  # noqa: BLE001 — one bad comparison must not kill the worker
                logger.exception(
                    "[%d/%d] FAILED %s -> %s on %s", idx, total, target, baseline,
                    worker_opts.get("ollama_base_url") or "default endpoint",
                )
                row = {"error": repr(exc)}
            with results_lock:
                results[idx] = row
                completed = len(results)
            logger.info("progress: %d/%d comparisons complete, %d in flight",
                        completed, total, min(n_workers, total - completed))
            work.task_done()

    logger.info(
        "sample-level parallelism: %d workers over %d comparisons, %s",
        n_workers, total,
        f"{len(endpoints)} endpoint(s)" if endpoints else "shared endpoint",
    )
    threads = [threading.Thread(target=_worker, args=(w,), daemon=True) for w in range(n_workers)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    return [results[i] for i in sorted(results)]


_TOOL_ARGS_RE = re.compile(r"\[agent\] tool args: (\w+)\((\{.*\})\)$", re.MULTILINE)

# Tools whose arguments name a specific part of the binary, so that two calls can be
# compared for having asked the same question. The rest take no such argument.
LOOKUP_TOOLS = frozenset(
    {
        "decompile_function", "disassemble", "decomp_diff", "get_matched_function",
        "get_control_flow_graph", "get_call_graph", "list_xrefs", "read_bytes",
        "search_symbols_by_name", "search_strings", "search_functions",
    }
)

STAGES = ("bounded", "unbounded")


def _lookup_key(tool: str, raw_args: str) -> Optional[str]:
    """Canonical identity of one lookup, or None if the arguments cannot be read.

    Argument order varies between calls and offsets appear in both hex and decimal, so the
    same request reaches the log in several forms and has to be normalized before two of
    them can be compared.
    """
    try:
        args = ast.literal_eval(raw_args)
    except (ValueError, SyntaxError):
        return None
    if not isinstance(args, dict):
        return None
    parts = []
    for key, value in sorted(args.items()):
        text = str(value)
        try:
            text = str(int(text, 0))
        except (TypeError, ValueError):
            pass
        parts.append(f"{key}={text}")
    return f"{tool}(" + ",".join(parts) + ")"


def _parse_trace(path: str) -> Tuple[Counter, List[str]]:
    """(tool calls by name, canonical lookup keys) from one investigation's agent trace.

    Read from the `tool args` lines, which carry the tool name and its complete arguments
    on one line and appear exactly once per call.
    """
    counts: Counter = Counter()
    lookups: List[str] = []
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as handle:
            text = handle.read()
    except OSError:
        logger.warning("unreadable agent trace %s", path)
        return counts, lookups
    for match in _TOOL_ARGS_RE.finditer(text):
        tool, raw_args = match.group(1), match.group(2)
        counts[tool] += 1
        if tool in LOOKUP_TOOLS:
            key = _lookup_key(tool, raw_args)
            if key is not None:
                lookups.append(key)
    return counts, lookups


def _pair_trace_metrics(pair_dir: str) -> Dict[str, Any]:
    """Tool use and cross-investigation overlap for one comparison.

    The analyzer records tool calls only as text in each investigation's agent trace, so
    they have to be read back out of the logs. The result is cached in the pair directory
    because re-summarizing a finished run would otherwise re-read every trace.
    """
    cache = os.path.join(pair_dir, "tool_metrics.json")
    if os.path.exists(cache):
        return _read_json(cache)

    by_stage = {stage: Counter() for stage in STAGES}
    per_investigation: List[List[str]] = []
    row_fields = {"bounded": "tool_calls", "unbounded": "unbounded_tool_calls"}
    counted = {stage: set() for stage in STAGES}
    rows_path = os.path.join(pair_dir, "per_function_results.json")
    rows = _read_json(rows_path) if os.path.exists(rows_path) else []
    for row in rows if isinstance(rows, list) else []:
        func_dir = os.path.join(
            pair_dir, f"filepair_{int(row.get('filepair_index') or 0):02d}", "modified_functions",
            f"b{row.get('baseline_addr')}__t{row.get('target_addr')}",
        )
        for stage, field in row_fields.items():
            if isinstance(row.get(field), dict) and row[field]:
                by_stage[stage] += Counter(row[field].get("by_tool", row[field]))
                counted[stage].add(os.path.normpath(func_dir))
    for stage in STAGES:
        pattern = os.path.join(
            pair_dir, "filepair_*", "modified_functions", "*", stage, "agent_trace.log"
        )
        for trace in glob.glob(pattern):
            counts, lookups = _parse_trace(trace)
            func_dir = os.path.normpath(os.path.dirname(os.path.dirname(trace)))
            if func_dir not in counted[stage]:
                by_stage[stage] += counts
            if stage == "unbounded" and lookups:
                per_investigation.append(lookups)

    # Counted per investigation, not per call: a lookup is shared only when separate
    # investigations of this binary both asked for it. An agent repeating its own lookup is
    # a different thing and must not inflate the overlap.
    investigations_per_lookup: Counter = Counter()
    for lookups in per_investigation:
        investigations_per_lookup.update(set(lookups))
    requested = sum(len(lookups) for lookups in per_investigation)

    metrics = {
        "tool_calls": {
            stage: {"total": sum(counts.values()), "by_tool": dict(sorted(counts.items()))}
            for stage, counts in by_stage.items()
        },
        "overlap": {
            "investigations_with_lookups": len(per_investigation),
            "lookups_requested": requested,
            "distinct_lookups": len(investigations_per_lookup),
            "lookups_shared_across_investigations": sum(
                1 for n in investigations_per_lookup.values() if n > 1
            ),
            "redundant_lookups": sum(
                n - 1 for n in investigations_per_lookup.values() if n > 1
            ),
        },
    }
    _write_json(cache, metrics)
    return metrics


def _disposition(label: Any, flagged: Any = None) -> str:
    """One investigation's outcome as flagged / cleared / failed.

    Failure is taken from the label rather than inferred from the absence of a flag, so that
    an investigation that never returned a verdict is not counted as a clearance. Bounded
    rows carry a separate flag field; unbounded rows have only the label.
    """
    if label in {"failed", "skipped", "", None}:
        return "failed"
    if flagged is None:
        return "flagged" if label == "not_safe" else "cleared"
    return "flagged" if flagged else "cleared"


def _pair_candidates(pair_dir: str) -> List[Dict[str, Any]]:
    path = os.path.join(pair_dir, "per_function_results.json")
    if not os.path.exists(path):
        return []
    rows = _read_json(path)
    return [row for row in rows if isinstance(row, dict)] if isinstance(rows, list) else []


def _candidate_index(rows: Iterable[Dict[str, Any]], pair: str) -> List[Dict[str, Any]]:
    """One record per investigation, keyed so the same candidate matches across arms.

    Every arm applies the same structural filter to the same pairs, so a candidate is
    identified by its binary pair and its two function addresses. Keeping that key stable is
    what lets a consumer join arms and compare a candidate against itself.
    """
    index: List[Dict[str, Any]] = []
    for row in rows:
        unbounded_ran = bool(row.get("unbounded_ran"))
        index.append(
            {
                "pair": pair,
                "key": ":".join(
                    str(row.get(k) or "")
                    for k in ("baseline_oid", "baseline_addr", "target_addr")
                ),
                "gt": bool(row.get("gt_match")),
                "bounded": _disposition(row.get("bounded_label"), row.get("bounded_flagged"))
                if row.get("bounded_ran")
                else None,
                "unbounded": _disposition(row.get("unbounded_label"))
                if unbounded_ran
                else None,
                "final": _disposition(row.get("pipeline_label"), row.get("pipeline_flagged")),
                "bounded_tokens": int(row.get("llm_total_tokens") or 0),
                "unbounded_tokens": int(row.get("unbounded_llm_total_tokens") or 0),
                "bounded_s": float(row.get("llm_elapsed_s") or 0.0),
                "unbounded_s": float(row.get("unbounded_llm_elapsed_s") or 0.0),
                "failure": row.get("failure_reason") or row.get("unbounded_failure_reason"),
            }
        )
    return index


def _candidate_metrics(index: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Investigation-level judgments, wall clock and failure reasons for one comparison."""
    judgments = {stage: Counter() for stage in STAGES}
    failures: Counter = Counter()
    elapsed = {"bounded": 0.0, "unbounded": 0.0}
    for record in index:
        for stage, field in (("bounded", "bounded"), ("unbounded", "unbounded")):
            outcome = record[field]
            if outcome is None:
                continue
            judgments[stage][outcome] += 1
            elapsed[stage] += record[f"{stage}_s"]
        if record["failure"]:
            failures[str(record["failure"])] += 1
    return {
        "judgments": {stage: dict(counts) for stage, counts in judgments.items()},
        "elapsed_s": elapsed,
        "failure_reasons": dict(failures),
    }


def _stage(row: Dict[str, Any], stage: str) -> Dict[str, Any]:
    """Per-stage metrics attached to a result row by _process_pair, or {} if absent."""
    metrics = row.get("_stage_metrics")
    if not isinstance(metrics, dict):
        return {}
    stage_metrics = metrics.get(stage)
    return stage_metrics if isinstance(stage_metrics, dict) else {}


def _fp_bin_counts(results: List[Dict[str, Any]], stage: Optional[str] = None) -> Dict[str, int]:
    counts = {label: 0 for label, _, _ in FP_BINS}
    for row in results:
        source = _stage(row, stage) if stage else row
        # Fail-closed: a review that never returned a verdict stays in the not_safe
        # queue rather than counting as cleared.
        flagged = int(source.get("flagged_functions") or 0) + int(source.get("failed_functions") or 0)
        for label, lower, upper in FP_BINS:
            if flagged < lower:
                continue
            if upper is not None and flagged > upper:
                continue
            counts[label] += 1
            break
    return counts


def _summarize_category(results: List[Dict[str, Any]], category: str) -> Dict[str, Any]:
    total_pairs = len(results)
    charged_input_tokens = sum(int(row.get("input_tokens") or 0) for row in results)
    charged_output_tokens = sum(int(row.get("output_tokens") or 0) for row in results)
    total_filtered = sum(int(row.get("filtered_functions") or 0) for row in results)
    total_flagged = sum(int(row.get("flagged_functions") or 0) for row in results)
    total_failed = sum(int(row.get("failed_functions") or 0) for row in results)
    investigated = sum(int(row.get("investigated_functions") or 0) for row in results)

    def _stage_sum(stage: str, key: str) -> int:
        return sum(int(_stage(row, stage).get(key) or 0) for row in results)

    def _accumulate(totals: Dict[str, Any], node: Dict[str, Any]) -> None:
        for key, value in node.items():
            if isinstance(value, dict):
                _accumulate(totals.setdefault(key, {}), value)
            else:
                totals[key] = totals.get(key, 0) + value

    def _merge(path: Tuple[str, ...]) -> Dict[str, Any]:
        """Sum the leaf numbers of one nested block across every comparison."""
        totals: Dict[str, Any] = {}
        for row in results:
            node: Any = row
            for key in path:
                node = node.get(key) if isinstance(node, dict) else None
            if isinstance(node, dict):
                _accumulate(totals, node)
        return totals

    def _judgments(stage: str) -> Dict[str, Any]:
        counts = _merge(("_candidates", "judgments", stage))
        reviewed = sum(counts.values())
        counts["reviewed"] = reviewed
        counts["clear_rate"] = (counts.get("cleared", 0) / reviewed) if reviewed else 0.0
        return counts

    bounded_tokens = _stage_sum("bounded", "total_tokens")
    unbounded_tokens = _stage_sum("unbounded", "total_tokens")
    tool_calls = _merge(("_trace", "tool_calls"))
    elapsed = _merge(("_candidates", "elapsed_s"))

    total_input_tokens = charged_input_tokens
    total_output_tokens = charged_output_tokens
    total_tokens = total_input_tokens + total_output_tokens

    summary: Dict[str, Any] = {
        "total_pairs": total_pairs,
        "input_tokens": total_input_tokens,
        "output_tokens": total_output_tokens,
        "total_tokens": total_tokens,
        "filtered_functions": total_filtered,
        "investigated_functions": investigated,
        "flagged_functions": total_flagged,
        "failed_functions": total_failed,
        "avg_input_tokens_per_invocation": (total_input_tokens / float(total_filtered)) if total_filtered else 0.0,
        "avg_output_tokens_per_invocation": (total_output_tokens / float(total_filtered)) if total_filtered else 0.0,
        "avg_total_tokens_per_invocation": (total_tokens / float(total_filtered)) if total_filtered else 0.0,
        # Failure reasons across both stages, so a change in the failure rate can be told
        # apart from a change in judgment.
        "failure_reasons": _merge(("_candidates", "failure_reasons")),
        "overlap": _merge(("_trace", "overlap")),
        # Per-stage breakdown. Bounded runs on every filtered candidate, unbounded only on
        # the escalated ones, so each average carries its own denominator.
        "stages": {
            "bounded": {
                "flagged_functions": _stage_sum("bounded", "flagged_functions"),
                "dismissed_functions": _stage_sum("bounded", "dismissed_functions"),
                "failed_functions": _stage_sum("bounded", "failed_functions"),
                "total_tokens": bounded_tokens,
                "avg_tokens_per_function": (bounded_tokens / float(total_filtered)) if total_filtered else 0.0,
                "judgments": _judgments("bounded"),
                "elapsed_s": elapsed.get("bounded", 0.0),
                "tool_calls": tool_calls.get("bounded", {}),
            },
            "unbounded": {
                "investigations": _stage_sum("unbounded", "investigations"),
                "with_report": _stage_sum("unbounded", "with_report"),
                "without_report": _stage_sum("unbounded", "without_report"),
                "flagged_functions": _stage_sum("unbounded", "flagged_functions"),
                "cleared_functions": _stage_sum("unbounded", "cleared_functions"),
                "failed_functions": _stage_sum("unbounded", "failed_functions"),
                "total_tokens": unbounded_tokens,
                "avg_tokens_per_investigation": (unbounded_tokens / float(investigated)) if investigated else 0.0,
                # Escalation from bounded, measured against investigating every filtered
                # candidate.
                "forwarded_functions": investigated,
                "forward_rate": (investigated / float(total_filtered)) if total_filtered else 0.0,
                "investigations_avoided": max(0, total_filtered - investigated),
                "judgments": _judgments("unbounded"),
                "elapsed_s": elapsed.get("unbounded", 0.0),
                "tool_calls": tool_calls.get("unbounded", {}),
            },
        },
    }

    if category == "backdoored":
        def _recall(rows: List[Dict[str, Any]], src: Optional[str]) -> Dict[str, Any]:
            def _get(row: Dict[str, Any], key: str) -> int:
                return int((_stage(row, src) if src else row).get(key) or 0)

            hits = sum(1 for row in rows if _get(row, "hit") > 0)
            dismissed = sum(1 for row in rows if _get(row, "hit") <= 0 and _get(row, "dismissed") > 0)
            failed = sum(1 for row in rows if _get(row, "hit") <= 0 and _get(row, "failed") > 0)
            not_safe_pairs = hits + failed
            safe_pairs = total_pairs - not_safe_pairs
            return {
                "not_safe_pairs": not_safe_pairs,
                "safe_pairs": safe_pairs,
                "not_safe_pairs_hit": hits,
                "not_safe_pairs_failed": failed,
                "safe_pairs_dismissed": dismissed,
            }

        summary.update(_recall(results, None))
        # Bounded's recall on its own, for the single-stage comparison.
        summary["stages"]["bounded"].update(_recall(results, "bounded"))
    else:
        not_safe_pairs = sum(
            1
            for row in results
            if (int(row.get("flagged_functions") or 0) + int(row.get("failed_functions") or 0)) > 0
        )
        summary["not_safe_pairs"] = not_safe_pairs
        summary["safe_pairs"] = total_pairs - not_safe_pairs
        summary["fp_bins"] = _fp_bin_counts(results)
        summary["stages"]["bounded"]["fp_bins"] = _fp_bin_counts(results, "bounded")

    return summary


def _prepare_run_opts(opts: Dict[str, Any], *, diff_mode: str, filter_key: Optional[str], gt_path: Optional[str], overrides: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    run_opts = dict(opts)
    run_opts["diff_mode"] = diff_mode
    run_opts["filter"] = filter_key
    run_opts["ground_truth"] = gt_path
    if overrides:
        run_opts.update(overrides)
    return run_opts


def _sha256_file(path: str) -> Optional[str]:
    try:
        with open(path, "rb") as handle:
            return hashlib.sha256(handle.read()).hexdigest()
    except OSError:
        return None


def _model_provenance(base_url: str, model: str) -> Dict[str, Any]:
    """Digest, quantization and baked-in parameters of the model actually being served."""
    try:
        request = urllib.request.Request(
            base_url.rstrip("/") + "/api/show",
            data=json.dumps({"model": model}).encode(),
            headers={"Content-Type": "application/json"},
        )
        with urllib.request.urlopen(request, timeout=30) as response:
            shown = json.loads(response.read().decode("utf-8", errors="replace"))
        with urllib.request.urlopen(base_url.rstrip("/") + "/api/version", timeout=10) as response:
            version = json.loads(response.read().decode("utf-8", errors="replace")).get("version")
    except Exception as exc:  # noqa: BLE001 -- provenance must not abort a run
        logger.warning("could not read model provenance from %s: %r", base_url, exc)
        return {"error": repr(exc)}

    digest = ""
    try:
        with urllib.request.urlopen(base_url.rstrip("/") + "/api/tags", timeout=10) as response:
            for entry in json.loads(response.read().decode("utf-8", errors="replace")).get("models") or []:
                if entry.get("name") == model:
                    digest = str(entry.get("digest") or "")
                    break
    except Exception:  # noqa: BLE001
        pass

    info = shown.get("model_info") or {}
    return {
        "tag": model,
        "digest": digest,
        "ollama_version": version,
        "details": shown.get("details") or {},
        "context_length": next(
            (v for k, v in info.items() if k.endswith(".context_length")), None
        ),
        # The model's own Modelfile parameters. Anything the client does not override is
        # what actually applies, so this has to be recorded next to what we set.
        "modelfile_parameters": shown.get("parameters") or "",
        "chat_template_sha256": hashlib.sha256(
            (shown.get("template") or "").encode("utf-8")
        ).hexdigest(),
    }


def _loaded_models(base_url: str) -> Any:
    """What Ollama currently has resident, including the context size it chose."""
    try:
        with urllib.request.urlopen(base_url.rstrip("/") + "/api/ps", timeout=10) as response:
            return json.loads(response.read().decode("utf-8", errors="replace")).get("models") or []
    except Exception as exc:  # noqa: BLE001 -- provenance must not abort a run
        return {"error": repr(exc)}


def _environment_provenance() -> Dict[str, Any]:
    versions: Dict[str, Any] = {"python": platform.python_version()}
    for package in (
        "ollama", "langchain", "langchain-core", "langchain-ollama", "langgraph",
        "langgraph-checkpoint", "deepagents", "langchain-mcp-adapters", "mcp", "pyyaml",
    ):
        try:
            versions[package] = importlib.metadata.version(package)
        except Exception:  # noqa: BLE001
            versions[package] = None

    ghidra: Dict[str, Any] = {}
    ghidra_path = ""
    try:
        from oxide.core import config as oxide_config

        ghidra_path = str(getattr(getattr(oxide_config, "dir", None), "ghidra_path", "") or "")
    except Exception:  # noqa: BLE001
        pass
    if not ghidra_path:
        # The plugin may be summarizing outside a configured framework, so fall back to the
        # config file the framework itself reads.
        parser = configparser.ConfigParser()
        try:
            parser.read(os.path.expanduser("~/.config/oxide/.config.txt"))
            ghidra_path = parser.get("dir", "ghidra_path", fallback="").strip()
        except Exception:  # noqa: BLE001
            pass
    if ghidra_path:
        ghidra["path"] = ghidra_path
        properties = os.path.join(ghidra_path, "Ghidra", "application.properties")
        try:
            with open(properties, "r", encoding="utf-8") as handle:
                for line in handle:
                    key, _, value = line.partition("=")
                    if key.strip() in {"application.version", "application.build.date"}:
                        ghidra[key.strip().split(".", 1)[1]] = value.strip()
        except OSError:
            pass

    commit = dirty = None
    try:
        root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(__file__))))
        commit = subprocess.check_output(
            ["git", "-C", root, "rev-parse", "HEAD"], text=True, stderr=subprocess.DEVNULL
        ).strip()
        dirty = bool(
            subprocess.check_output(
                ["git", "-C", root, "status", "--porcelain"], text=True, stderr=subprocess.DEVNULL
            ).strip()
        )
    except Exception:  # noqa: BLE001
        pass

    return {"versions": versions, "ghidra": ghidra, "oxide_commit": commit, "oxide_dirty": dirty}


def _prompt_provenance() -> Dict[str, Optional[str]]:
    """sha256 of every prompt template, so a reworded prompt is visible in the record."""
    prompt_dir = os.path.join(
        os.path.dirname(os.path.dirname(__file__)),
        "modules", "analyzers", "delt_verification", "pipeline", "prompts",
    )
    return {
        os.path.basename(path): _sha256_file(path)
        for path in sorted(glob.glob(os.path.join(prompt_dir, "*.yaml")))
    }


def _resolved_analyzer_opts(base_opts: Dict[str, Any]) -> Dict[str, Any]:
    """The opts the analyzer will actually run with.

    Oxide fills opts_doc defaults for mangled opts at the module boundary, and the runtime
    then applies its negative-means-unsent convention to the sampling options. Reading
    base_opts instead reports the plugin's own fallbacks for anything the caller left
    unset, which is how a run came to record a bounded budget it never used and an empty
    overridden_options while every sampling option was in fact pinned.
    """
    from oxide.modules.analyzers.delt_verification import module_interface as delt_module
    from oxide.modules.analyzers.delt_verification.pipeline.agents.runtime import (
        _resolve_runtime_opts,
    )

    merged = dict(base_opts)
    for key, spec in delt_module.opts_doc.items():
        if spec.get("mangle") and key not in merged and "default" in spec:
            merged[key] = spec["default"]
    if not str(merged.get("model") or "").strip():
        merged["model"] = "unset"
    return _resolve_runtime_opts(merged)


def _run_manifest(base_opts: Dict[str, Any], endpoints: List[str]) -> Dict[str, Any]:
    """Everything needed to say what produced a set of results.

    Written once per model per run. Decoding settings are recorded next to the model's own
    baked-in parameters, because anything the client does not override still applies.
    """
    model = str(base_opts.get("model") or "")
    base_url = (endpoints or [DEFAULT_OLLAMA_URL])[0]
    from oxide.modules.analyzers.delt_verification.pipeline.agents.runtime import SAMPLING_OPTS

    resolved = _resolved_analyzer_opts(base_opts)
    settings = {
        key: resolved[key]
        for key in (
            "bounded_request_s", "bounded_model_call_s",
            "unbounded_request_s", "unbounded_model_call_s",
        )
    }
    overridden = []
    for key in SAMPLING_OPTS:
        if resolved.get(key) is None:
            continue
        settings[key] = resolved[key]
        overridden.append(key)
    from oxide.modules.analyzers.delt_verification.pipeline.tools import binary_pair

    return {
        "recorded_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "model": _model_provenance(base_url, model),
        "overridden_options": overridden,
        "settings": settings,
        # Ollama sizes the context from free VRAM unless told otherwise, so it is a property
        # of the machine and of what else was resident. Left at the default deliberately,
        # and therefore recorded from the loaded model rather than assumed.
        "loaded": _loaded_models(base_url),
        "endpoints": list(endpoints),
        "context_length": int(base_opts.get("context_length") or DEFAULT_CONTEXT_LENGTH),
        "configs": [
            {"arm": name, "diff_mode": diff, "filter": filt, "opts": overrides}
            for name, diff, filt, overrides in EXPERIMENT_CONFIGS
        ],
        "prompts": _prompt_provenance(),
        "tools": {"unbounded": list(binary_pair.PAIR_TOOLS)},
        "environment": _environment_provenance(),
    }


def _run_experiment_configs(
    base_opts: Dict[str, Any],
    *,
    config_root: str,
    backdoored_pairs: List[Tuple[str, str]],
    safe_pairs: List[Tuple[str, str]],
    gt: Dict[str, Any],
    gt_path: Optional[str],
    dry_run: bool = False,
) -> Dict[str, Any]:
    """Run the LLM experiment configs for a single model into config_root. In dry_run mode
    only the `bounded` config runs, with bounded disabled, so each modified
    function gets its unified diff and agent inputs on disk but the agent never runs."""
    from oxide.modules.analyzers.delt_verification.pipeline.agents.runtime import SAMPLING_OPTS

    SAMPLING_OPT_NAMES = set(SAMPLING_OPTS)
    resolved_opts = _resolved_analyzer_opts(base_opts)
    configs = EXPERIMENT_CONFIGS
    if dry_run:
        configs = tuple(cfg for cfg in EXPERIMENT_CONFIGS if cfg[0] == "bounded")
    config_summaries: Dict[str, Any] = {}
    for config_name, diff_mode, filter_key, overrides in configs:
        config_dir = os.path.join(config_root, config_name)
        os.makedirs(config_dir, exist_ok=True)
        include_added_callees = bool(
            overrides.get("include_added_callees", base_opts.get("include_added_callees", True))
        )
        config_summary: Dict[str, Any] = {
            "model": base_opts.get("model"),
            "sample_workers": int(base_opts.get("sample_workers") or 1),
            "diff_mode": diff_mode,
            "filter_mode": "NONE" if not filter_key else filter_key,
            "include_added_callees": include_added_callees,
            "skip_bounded": bool(overrides.get("skip_bounded")),
            "skip_unbounded": bool(overrides.get("skip_unbounded")),
            "no_bounded_report": bool(overrides.get("no_bounded_report")),
            "unbounded_request_s": resolved_opts["unbounded_request_s"],
            "bounded_request_s": resolved_opts["bounded_request_s"],
            "bounded_model_call_s": resolved_opts["bounded_model_call_s"],
            "sampling": {
                key: value
                for key, value in resolved_opts.items()
                if key in SAMPLING_OPT_NAMES and value is not None
            },
        }

        # gt_only is a backdoor-recall shortcut: only the ground-truth function is boundedd.
        # It applies to the backdoored set alone. The safe category has no ground truth, so
        # it always runs in full, with gt_only forced off for it below.
        gt_only = bool(base_opts.get("gt_only"))
        categories: List[Tuple[str, List[Tuple[str, str]], Optional[str], Dict[str, Any]]] = []
        if backdoored_pairs:
            categories.append(("backdoored", backdoored_pairs, gt_path, gt))
        if safe_pairs:
            categories.append(("safe", safe_pairs, None, {}))

        for category, pairs, category_gt_path, category_gt in categories:
            category_dir = os.path.join(config_dir, category)
            run_opts = _prepare_run_opts(
                base_opts,
                diff_mode=diff_mode,
                filter_key=filter_key,
                gt_path=category_gt_path,
                overrides=overrides,
            )
            # gt_only restricts bounded to the ground-truth function, which only exists for
            # the backdoored set. Force it off for safe so it boundeds every filtered
            # function and its false-positive counts stay complete.
            run_opts["gt_only"] = gt_only and category == "backdoored"
            results = _run_category(
                pairs, category_dir, run_opts, gt=category_gt,
                sample_workers=int(base_opts.get("sample_workers") or 1),
                endpoints=list(base_opts.get("_endpoints") or []),
            )
            summary = _summarize_category(results, category)
            config_summary[category] = summary

            comparison_rows = [
                {
                    "index": index + 1,
                    **{k: v for k, v in row.items() if not k.startswith("_")},
                }
                for index, row in enumerate(results)
            ]
            _write_json(
                os.path.join(category_dir, "comparisons_summary.json"),
                {
                    "config": config_name,
                    "category": category,
                    "comparisons": comparison_rows,
                },
            )
            _write_json(os.path.join(category_dir, "series_metrics.json"), summary)
            # Flattened across pairs so one arm's investigations can be joined against
            # another's on the candidate key.
            _write_json(
                os.path.join(category_dir, "candidates.json"),
                [record for row in results for record in row.get("_index") or []],
            )

        _write_json(os.path.join(config_dir, "config_summary.json"), config_summary)
        config_summaries[config_name] = config_summary
    return config_summaries


def run_experiments(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Run the experiment matrix using the `delt_verification` analyzer.

    One arm per entry in EXPERIMENT_CONFIGS, each run over the backdoored and safe pair
    sets, into outdir/<arm>/<category>/. Each category directory receives:

      series_metrics.json      pair recall, tokens, alert bins, investigation-level
                               judgments and clear rates, per-stage tool calls and wall
                               clock, escalation counts, survey cost separated from
                               investigation cost, failure reasons, and lookup overlap
      candidates.json          one record per investigation, keyed by pair and function
                               addresses so a candidate can be matched across arms
      comparisons_summary.json per-pair stats in input order

    Tool use and lookup overlap are parsed back out of each investigation's agent trace,
    the only place the analyzer records them, and cached per pair in tool_metrics.json.
    Completed pairs are read from cache, so re-running over an existing outdir
    re-summarizes it without calling a model.

    Required/expected opts:
      backdoored   -- entries file of backdoored target,baseline pairs
      ground_truth -- ground-truth JSON for the backdoored pairs

    Model selection:
      model        -- a single model tag passed through to the delt_verification analyzer
      models       -- a models file (like models.txt); each line is
                      `model_tag [sample_workers]` (sample_workers defaults to 1).
                      Results for each model land under outdir/<model_slug>/.
      (neither)    -- dry run: only the `bounded` config runs, with bounded
                      disabled, so each modified function gets its unified diff and the
                      agent's input files (outdir/bounded/<category>/<pair>/
                      filepair_NN/modified_functions/<b..t..>/{diff.txt,agent_inputs/})
                      written to disk without invoking the agent. Use this to author
                      ground truth.

    Parallelization is owned by this plugin, not the analyzer: the analyzer runs one
    comparison sequentially, and this plugin runs several comparisons at once, one per
    Ollama endpoint. That parallelizes all three stages -- bounded, binary context, and
    unbounded -- where per-function fan-out inside the analyzer would only have
    parallelized bounded, the smallest share of the work. Workers pull from a shared queue,
    which self-balances the very uneven per-sample function counts.

    Endpoints are handled for you: with sample_workers > 1 and no explicit endpoints, one
    Ollama server per GPU is launched for the run and shut down when it finishes. Every
    endpoint is verified to serve the model before any comparison starts, so a dead server
    or a wrong model store fails immediately instead of producing a full set of zero-
    detection results that look like a model outcome.
      sample_workers -- how many comparisons run concurrently for the single --model form
                      (default 1). In the models file it is the per-model second column.
                      Set it to the number of GPUs you want to use.
      endpoints    -- optional comma-separated Ollama base URLs (or DELT_ENDPOINTS) to use
                      servers you started yourself, e.g.
                      http://127.0.0.1:11436,http://127.0.0.1:11437. Each worker is pinned
                      to one, and nothing is launched or shut down.
      ollama_base_port -- first port to try when launching (default 11435). Ports in use
                      are skipped, so a neighbouring server is never hijacked.
      context_length -- OLLAMA_CONTEXT_LENGTH for every launched worker (default 262144).
                      Pinned rather than left to Ollama, which sizes it from free VRAM and
                      so gives identical cards different contexts. Only applies to servers
                      this run launches; with explicit endpoints, set it there.

    Optional opts:
      safe         -- entries file of safe target,baseline pairs
      outdir       -- root output directory (default: out/delt_verification_experiments)
      gt_only      -- backdoor-recall shortcut: bounded only the ground-truth
                      insertion function(s) of each backdoored pair instead of every
                      filtered candidate. Filter counts are still reported; only the
                      boundedd subset shrinks, so it runs much faster when you only need
                      to check whether the backdoor is detected. Forced off for the safe
                      pairs, which have no ground truth.
    """
    backdoored_path: Optional[str] = opts.get("backdoored")
    safe_path: Optional[str] = opts.get("safe")
    gt_path: Optional[str] = opts.get("ground_truth")
    outdir = str(opts.get("outdir") or "out/delt_verification_experiments")

    if not backdoored_path and not safe_path:
        raise ValueError("At least one of --backdoored or --safe must be provided.")

    model_specs, nested, dry_run = _resolve_model_specs(opts)

    backdoored_pairs = _read_series_file(backdoored_path) if backdoored_path else []
    safe_pairs = _read_series_file(safe_path) if safe_path else []
    gt = load_ground_truth_file(gt_path) if gt_path else {}

    os.makedirs(outdir, exist_ok=True)
    experiment_summary: Dict[str, Any] = {}

    model_summaries: Dict[str, Any] = {}
    for model, sample_workers in model_specs:
        base_opts = dict(opts)
        base_opts["model"] = model
        # Whole comparisons run concurrently here, one per endpoint; the analyzer itself is
        # sequential. See _run_category.
        base_opts["sample_workers"] = sample_workers
        # Dry run: disable bounded so the analyzer only produces per-function diffs and
        # agent inputs. No model client is built.
        base_opts["no_bounded"] = dry_run
        config_root = os.path.join(outdir, _model_slug(model)) if nested else outdir
        os.makedirs(config_root, exist_ok=True)

        # Provision and verify endpoints once per model, before any comparison runs, and
        # tear down anything this run launched. A dry run never calls a model.
        manager = None
        if dry_run:
            logger.info("running dry-run (no bounded) to produce bounded inputs")
        else:
            endpoints, manager = _provision_sample_endpoints(base_opts, sample_workers)
            base_opts["_endpoints"] = endpoints
            logger.info(
                "running experiment configs for model %s (sample_workers %d, %s)",
                model, sample_workers,
                f"{len(endpoints)} endpoint(s)" if endpoints else "default endpoint",
            )

        _write_json(
            os.path.join(config_root, "run_manifest.json"),
            _run_manifest(base_opts, list(base_opts.get("_endpoints") or [])),
        )

        try:
            config_summaries = _run_experiment_configs(
                base_opts,
                config_root=config_root,
                backdoored_pairs=backdoored_pairs,
                safe_pairs=safe_pairs,
                gt=gt,
                gt_path=gt_path,
                dry_run=dry_run,
            )
        finally:
            if manager is not None:
                logger.info("shutting down Ollama server(s) launched for this run")
                manager.shutdown()

        if nested:
            model_summaries[model] = config_summaries
            _write_json(os.path.join(config_root, "experiment_summary.json"), config_summaries)
        else:
            experiment_summary.update(config_summaries)

    if nested:
        experiment_summary["models"] = model_summaries

    _write_json(os.path.join(outdir, "experiment_summary.json"), experiment_summary)
    logger.info("Experiment summary written to %s", os.path.join(outdir, "experiment_summary.json"))
    return experiment_summary


exports = [run_experiments]
