"""Task modules — the DOMAIN layer of the agentic RE framework.

Each module here instantiates one reverse-engineering task's Ω (its task-specific deterministic
oracles) and registers them with the core via `grounding.register_domain_oracle`. The CORE library
(pipeline / grounding / prompts) contains NO task knowledge; importing a task module is what makes its
certifiers available. A harness imports the task module(s) it needs before running the pipeline.
"""
