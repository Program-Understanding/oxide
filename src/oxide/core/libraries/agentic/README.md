# Running the agentic RE feature

A multi-agent reverse-engineering pipeline exposed as the Oxide `agentic_re` plugin: it plans tasks,
runs specialist agents with tools, verifies findings, and synthesizes a tiered answer about a binary.

## Configure the LLM (required)

All settings come from the `[agentic]` section of `~/.config/oxide/.config.txt` — there are **no
built-in defaults** (a missing key raises a clear error). Use any OpenAI-compatible server:

```ini
[agentic]
endpoint    = http://localhost:8000/v1
model       = Qwen/Qwen3.6-35B-A3B   ; sets planner + worker + verifier at once
nothink     = 1                      ; optional: disable chain-of-thought (faster on local models)
ctx_chars   = 320000                 ; input-context budget (chars)
max_tokens  = 16384                  ; max output tokens per call
out_cap     = 40000                  ; per-tool-output char cap (0 = unlimited)
req_timeout = 400                    ; per-request timeout (seconds)
```

Per-setting override order: opts → env `AGENTIC_<KEY>` → `[agentic]` config.

## Oxide shell

```
oxide> import /path/to/binary | agentic_re --question="What does this binary do?"
oxide> agentic_re %<oid> --question="Recover the C type of each variable in main"
```

## Programmatically

```python
from oxide.core.oxide import api
from oxide.plugins import agentic_re

oid, _ = api.import_file("/path/to/binary")
result = agentic_re.agentic_re([oid], {"question": "What does this binary do?"})
print(result[oid])          # the tiered answer
```

`agentic_re(oids, opts)` returns `{oid: answer}`. Useful `opts`: `question` (required),
`max_subtasks`, `max_iter`, `max_rounds`, `no_cache`, and per-run LLM overrides (`endpoint`,
`model`, …). Requires `oxide/src` on `PYTHONPATH`, and `JAVA_HOME` set (Ghidra's headless subprocess).
