"""Type-recovery task package: the deterministic oracles, split one per module.

Was a single 1207-line module until 2026-07-30. `agentic.tasks.type_recovery` remains the import
path and the public surface -- every name other code used is re-exported below, so callers
(`mcp_agentic`, `deepagent`, `extras.runtime_probe`, `characterize.py`) are unaffected.

Importing this package REGISTERS the oracles and publishes the tool wrappers; that is a side effect
other modules rely on, so the submodule imports below are load-bearing, not conveniences.
"""
from agentic.grounding import register_domain_oracle

from .common import *          # noqa: F401,F403  shared tables, parsers, pointer predicates
from .common import (DEFAULT_ORACLES, is_shapeless_pointer, _is_vague_pointer,  # noqa: F401
                     _vid_to_arg, _vid_stack_offsets, _vid_sizes, _decl_pointer_map,
                     _libc_type_of_param, _arg_is_value)
from .libc_abi import callee_type_recall_facts, _oracle_callee_signature          # noqa: F401
from .decompiler import decompiler_pointer_facts, _oracle_decompiler_pointer      # noqa: F401
from .spilled import spilled_param_facts, _oracle_spilled_param                   # noqa: F401
from .interproc import (interprocedural_param_usage_facts,                        # noqa: F401
                        _oracle_interprocedural_param_usage)
from .signedness import signedness_facts, _oracle_signedness                      # noqa: F401
from .struct_shape import struct_shape_facts, _oracle_struct_shape                # noqa: F401
from . import tools as _tools                                                     # noqa: F401

register_domain_oracle("callee_signature", _oracle_callee_signature)
register_domain_oracle("decompiler_pointer", _oracle_decompiler_pointer)
register_domain_oracle("interprocedural_param_usage", _oracle_interprocedural_param_usage)
register_domain_oracle("spilled_param", _oracle_spilled_param)
register_domain_oracle("signedness", _oracle_signedness)
register_domain_oracle("struct_shape", _oracle_struct_shape)
