"""Optional extras for the agentic RE package — NOT part of the minimal pipeline.

These modules load lazily and only when their feature flag is set, so the core (deepagent +
static oracles + tool backends) never depends on them:
  * trace          — Phoenix / OpenTelemetry run tracing (AGENTIC_PHOENIX*)
  * flow_recorder  — Mermaid run-flow diagrams (AGENTIC_FLOW_DIAGRAM=1)
  * runtime_probe  — opt-in dynamic angr type oracle (domain_oracles includes runtime_type_probe)
"""
