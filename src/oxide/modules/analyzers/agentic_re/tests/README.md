# agentic_re offline test suite

Fully offline: **no LLM server, no Ghidra, no Oxide datastore, no network.** The real module code
runs against a fake Oxide api (`conftest.FakeApi`), a small synthetic x86-64 function set, and
synthetic decompilation strings.

## Running

```bash
cd oxide/src/oxide/modules/analyzers/agentic_re
python3 -m pytest tests -q          # ~2 s
python3 -m pytest tests -q -x       # stop at first failure
python3 -m pytest tests/test_regressions.py -v
```

Only `pytest` and `langchain-core` are needed (the latter is already a runtime dependency; only
`test_deepagent_helpers` touches it).

## Layout

| File | Covers |
|---|---|
| `conftest.py` | `FakeApi`, the synthetic binary, shared fixtures (`ctx`, `call_tool`, `oxide_stub`, `empty_libc`, `msg`) |
| `test_common.py` | question parsers (`_vid_sizes`, `_vid_to_arg`, …), `_split_args`, `_arg_is_value`, pointer predicates, libc lookup |
| `test_oracles_libc_spilled.py` | `callee_signature`, `spilled_param` |
| `test_interproc.py` | forwarding walk, deref/scalar evidence, definition-line guard, size guard |
| `test_signedness.py` | disasm parsing, def-use walk, sign vetoes |
| `test_struct_shape.py` | shape rendering, slot aliasing |
| `test_certify.py` | size coercion, undefined-rescue, all five claim modes, end-to-end `_collect_oracle_facts` |
| `test_claims.py` | per-stage claim capture and attribution |
| `test_deepagent_helpers.py` | salvage, channel strip, prose-tool-call repair, roster filter, loop cap, scaling rules |
| `test_tools_registry.py` | registry schemas, name-mangling tolerance, memoization, out-cap, oracle registration uniformity |
| `test_tool_backends.py` | real `ghidra.py`/`elf.py`/`context.py` against the synthetic binary |
| `test_mcp_server.py` | address/offset normalization, memo + tool log, import masking, published-tool/roster agreement |
| `test_regressions.py` | **named guards for bugs that actually shipped** — read this first |

## Conventions

* **`test_regressions.py` is the important file.** Every test there pins a bug with a measured cost
  recorded in its docstring. Add one whenever you fix something that changed a score.
* Tests set env with `monkeypatch.setenv`, never `os.environ` directly, so flags cannot leak.
* `conftest` sets `AGENTIC_LIBC=1` so libc-dependent paths are testable; the production default
  (off) is asserted by `test_libc_table_is_off_by_default`.
* One test is an intentional `xfail`: `test_sign_idiom_not_counted_as_unsigned` documents the
  signedness false positive found in the 2026-08-04 A/B (`shr reg,31` sign-bit extraction and
  `movzx`-after-`setcc` are emitted for *signed* ints). It flips to pass when the vetoes land —
  `strict=False`, so an early fix does not fail the suite.

## What is NOT covered

The graph itself (`create_deep_agent`, the coordinator→worker→verifier run) needs a model server, so
it is out of scope here; `run_trex_one.py` remains the end-to-end check. Also uncovered: `extras/`
(flow recorder, angr runtime probe, demos) and Phoenix tracing.
