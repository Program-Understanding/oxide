"""callee-signature oracle: a parameter's type from the fixed ABI of a C-library function it is
passed to. The strongest evidence in the set -- an external contract, not an inference."""
from __future__ import annotations

import json
import re
from .common import _LIBC_CALL, _LIBC_SIG, _arg_is_value, _is_vague_pointer, _split_args, _vid_to_arg


def callee_type_recall_facts(call_tool, question) -> list:
    """For each register-passed PARAMETER named in the question, if the decompilation passes it
    (directly, or through a one-level local alias) to a known library function at a position whose ABI
    type is fixed, emit that type. Returns a list of (vid, ctype, callee, argpos) tuples."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    addr = m.group(1)
    vid_param = _vid_to_arg(question)
    if not vid_param:
        return []
    try:
        dec = call_tool("decompile", {"addr": addr})
    except Exception:  # noqa: BLE001
        return []
    if not isinstance(dec, str) or dec.startswith("(no"):
        return []
    # The shared `_LIBC_CALL` (one level of nested parens), NOT a flat `[^()]*` matcher: Ghidra's
    # dominant call idiom is `strcmp((char *)param_1, param_2)`, and a flat matcher fails on the
    # cast's parens -- silently missing the call `_arg_is_value`'s cast-stripping exists to handle.
    facts, taken = [], set()
    for vid, k in vid_param.items():
        if vid in taken:
            continue
        pname = f"param_{k}"
        aliases = {pname}
        for am in re.finditer(rf"\b([A-Za-z_]\w*)\s*=\s*{pname}\b(?![\w.\[])", dec):
            aliases.add(am.group(1))
        alt = "|".join(re.escape(a) for a in aliases)
        for line in dec.splitlines():
            for cm in _LIBC_CALL.finditer(line):
                sig = _LIBC_SIG.get(cm.group(1))
                if not sig:
                    continue
                args = _split_args(cm.group(2))
                for j, a in enumerate(args):
                    if j < len(sig) and sig[j] and _arg_is_value(a, aliases):
                        facts.append((vid, sig[j], cm.group(1), j + 1))
                        taken.add(vid)
                        break
                if vid in taken:
                    break
            if vid in taken:
                break
    return facts


def _oracle_callee_signature(call_tool, question) -> list:
    out = []
    for vid, ctype, callee, argpos in callee_type_recall_facts(call_tool, question):
        out.append({
            "vid": vid, "ctype": ctype, "source": "deterministic_callee_signature",
            "floor": _is_vague_pointer(ctype),
            "claim": (f"{vid} has C type `{ctype}` — it is passed as argument {argpos} to "
                      f"`{callee}`, whose library ABI signature fixes that parameter's type. "
                      f"Treat as established; this overrides any weaker guess for {vid}."),
            "reason": f"ABI signature of {callee} fixes argument {argpos}"})
    return out
