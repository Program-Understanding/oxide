""" agentic_re — native agentic reverse-engineering for Oxide (Oxide-shell adapter).

This plugin is a THIN adapter: it parses opts, resolves oids, handles the per-(oid, question)
answer cache, and delegates to the orchestration loop in
`oxide.core.libraries.agentic.pipeline.run()` — which is the heart of the feature:

  plan (LLM, FULL ordered task list) -> for each task top-to-bottom:
      specialist agent(s) -> verify findings -> planner ASSESS (mark done / unsolvable)
      -> REPLAN the task (bounded retries) -> REVISE the plan (add tasks for new leads)
  -> deterministic call/value recall -> tiered synthesis

The whole feature lives in `core/libraries/agentic/` (see its README); this file is just the
shell entry point.

Shell usage:
  oxide> import /path/to/binary | agentic_re --question="What does this binary do?"
  oxide> agentic_re %<oid> --question="..." [--max-subtasks=8 --max-iter=8 --endpoint=http://host:8000/v1]

Returns (and prints) the tiered answer; caches per (oid, question) in the plugin local store.
"""
from __future__ import annotations

import hashlib
from typing import Any, Dict, List

from oxide.core.oxide import api

from oxide.core.libraries.agentic import llm as L
from oxide.core.libraries.agentic import trace as TR
from oxide.core.libraries.agentic import pipeline

NAME = "agentic_re"


def agentic_re(args: List[str], opts: Dict[str, Any]):
    """Run the agentic RE pipeline on the given binary oid(s).

    args : oids / collection names (or none, if piped). Use a path via --import=<path>.
    opts : question (required), max_rounds, max_subtasks, max_iter,
           planner_model, worker_model, verifier_model, endpoint, no_cache, phoenix.
    """
    question = opts.get("question") or opts.get("q")
    if not question:
        raise ShellSyntaxError("agentic_re needs --question=\"...\"")

    oids: List[str] = []
    imp = opts.get("import")
    if imp:
        oid, _new = api.import_file(imp)
        if oid:
            oids.append(oid)
    valid, _invalid = api.valid_oids(args)
    oids.extend(api.expand_oids(valid))
    oids = list(dict.fromkeys(oids))
    if not oids:
        raise ShellSyntaxError("no valid oids — pass %<oid>, a collection, or --import=<path>")

    # Phoenix tracing: enable via the bare `--phoenix` flag, OR AGENTIC_PHOENIX=1 / `[agentic]`
    # config `phoenix = 1`. Endpoint via --phoenix_endpoint / AGENTIC_PHOENIX_ENDPOINT / config.
    if ("phoenix" in opts) or bool(L._opt(opts, "phoenix")):
        ep = L._opt(opts, "phoenix_endpoint") or "http://localhost:6006/v1/traces"
        TR.setup_phoenix(ep)

    cfg = L.resolve_config(opts)
    max_rounds = int(opts.get("max_rounds", 3))
    max_subtasks = int(opts.get("max_subtasks", 12))
    max_iter = int(opts.get("max_iter", 12))
    use_cache = not bool(opts.get("no_cache", False))

    out: Dict[str, str] = {}
    for oid in oids:
        key = hashlib.sha1((oid + "::" + question + "::" + cfg["worker_model"]).encode()).hexdigest()
        if use_cache and api.local_exists(NAME, key):
            answer = api.local_retrieve(NAME, key)
            print(f"[agentic_re] cached answer for {oid[:12]}")
        else:
            print(f"[agentic_re] oid={oid[:12]}  endpoint={cfg['endpoint']}  "
                  f"worker={cfg['worker_model']}  verifier={cfg['verifier_model']}")
            print(f"question={question}\n" + "=" * 60)
            answer = pipeline.run(oid, question, cfg, max_rounds, max_subtasks, max_iter)
            api.local_store(NAME, key, answer)
        print("\n" + "=" * 60 + "\nFINAL ANSWER\n" + "=" * 60 + "\n" + str(answer) + "\n")
        out[oid] = answer
    return out


# ShellSyntaxError is injected into plugin namespace by the loader; fall back for direct import
try:
    from oxide.core.oshell import ShellSyntaxError  # type: ignore
except Exception:  # noqa: BLE001
    class ShellSyntaxError(Exception):
        pass


exports = [agentic_re]
