"""Native agentic reverse-engineering for Oxide.

This package brings the multi-agent RE pipeline (planner -> parallel workers ->
adversarial verifier -> coverage gates -> deterministic grounding/recall -> tiered
synthesis) into Oxide as first-class, in-tree code. Oxide's own analysis modules
(ghidra_disasm, control_flow_graph, call_graph, ghidra_decmap, elf, strings) are the
tools; the LLM backend is configurable (Together.ai now, local ollama later).

Modules:
  prompts    — agent system prompts + deterministic catalogs (single source of truth)
  llm        — configurable LLM layer (make_llm / complete / run_react)
  tools      — Oxide-backed tool layer (build_tools / call_tool), mirrors the radare2
               tool contract so the grounding parsers are reused unchanged
  grounding  — deterministic grounding (V1-V4) + value/call recall (R1-R3) + tiered answer
"""
