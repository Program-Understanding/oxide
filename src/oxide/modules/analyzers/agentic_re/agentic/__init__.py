"""Native agentic reverse-engineering for Oxide.

Shared infrastructure for the deepagents multi-agent RE pipeline. The pipeline driver itself
(`deepagent` + `flow_recorder`) runs over the Oxide MCP server (`oxide/mcp_server.py`); this package
holds the pieces that server and the agents both depend on.

Modules:
  config     — settings resolution (env / [agentic] config / opts) + the USAGE counter
  tools      — Oxide-backed tool layer (build_tools / call_tool over ghidra/elf backends)
  grounding  — deterministic grounding + the domain-oracle registry (register_domain_oracle)
  tasks      — the type-recovery + runtime-probe oracles that register with grounding
  trace      — optional Phoenix / OpenTelemetry tracing sink
  deepagent  — the coordinator/worker/verifier driver + oracle-certified trailer
  flow_recorder — optional per-run flow diagrams (Mermaid + markdown)
"""
