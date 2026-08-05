"""Tool backends (tools/ghidra.py, tools/elf.py, tools/context.py) against the synthetic binary.

These exercise the REAL analysis code -- frame-delta arithmetic, the CFG may-analysis in
register_usage/struct_shape, the disassembly window, coordinate conversion -- with canned Oxide
retrievals, so no Ghidra process is needed.
"""
import pytest

from agentic.tools import ghidra as GH
from agentic.tools import elf as ELF


# ---- coordinate conversion (context.py) ----
def test_off_to_vaddr_roundtrip(ctx):
    assert ctx.off_to_vaddr(0x1000) == 0x101000
    assert ctx.vaddr_to_off(0x101000) == 0x1000


def test_off_to_vaddr_outside_sections(ctx):
    assert ctx.off_to_vaddr(0x999999) is None


def test_fmt_detects_elf(ctx):
    assert ctx.fmt() == "elf"


def test_resolve_func_by_name_and_addr(ctx):
    assert ctx.resolve_func("funcA") == "funcA"
    assert ctx.resolve_func("0x101000") == "funcA"
    assert ctx.resolve_func("sym.funcA") == "funcA"


def test_clean_name():
    assert GH.__dict__ and ELF.__dict__                      # modules imported
    from agentic.tools.context import OxideContext
    assert OxideContext.clean_name("<EXTERNAL>::__printf_chk") == "__printf_chk"


def test_is_import(ctx):
    assert ctx.is_import("strlen") is True
    assert ctx.is_import("funcA") is False


# ---- disassemble ----
def test_disassemble_lists_instructions(ctx):
    out = GH.disassemble(ctx, "0x101000")
    assert "0x101000" in out and "push rbp" in out


def test_disassemble_unknown_addr(ctx):
    assert "no function at" in GH.disassemble(ctx, "0xdeadbeef")


def test_disassemble_window_is_full_width(ctx):
    # the window must be n instructions even when centred on the entry (the slide-back fix)
    out = GH.disassemble(ctx, "0x101000", n_instructions=8)
    body = [l for l in out.splitlines() if l.startswith("0x")]
    assert len(body) == 8
    assert "window: instructions" in out


def test_disassemble_marks_requested_address(ctx):
    out = GH.disassemble(ctx, "0x101008", n_instructions=8)
    assert "<=== requested address" in out


# ---- stack_var ----
def test_stack_var_lists_all_slots(ctx):
    out = GH.stack_var(ctx, "0x101000")
    offsets = {s["offset"] for s in out["slots"]}
    assert out["frame_delta"] == 8                            # one `push rbp` before mov rbp,rsp
    assert "-0x20" in offsets                                 # rbp -0x18 in question coordinates


def test_stack_var_single_slot_found(ctx):
    out = GH.stack_var(ctx, "0x101000", offset="-0x20")
    assert out["found"] is True
    assert out["rbp_offset"] == "-0x18"
    assert any("rdi" in a for a in out["accesses"])


def test_stack_var_missing_slot(ctx):
    out = GH.stack_var(ctx, "0x101000", offset="-0x99")
    assert out["found"] is False and out["accesses"] == []


def test_stack_var_bad_offset(ctx):
    assert "error" in GH.stack_var(ctx, "0x101000", offset="not-hex")


# ---- register_usage ----
def test_register_usage_by_offset_and_name(ctx):
    a = GH.register_usage(ctx, "0x101000", "0x38")
    b = GH.register_usage(ctx, "0x101000", "rdi")
    assert a["register"] == b["register"] == "rdi"
    assert a["arg_position"] == 1


def test_register_usage_detects_deref_and_stride(ctx):
    out = GH.register_usage(ctx, "0x101000", "0x38")
    assert out["dereferenced"] is True
    assert out["stride_arith"] is True and "+0x5" in out["strides"]
    assert "ADDRESS" in out["summary"]


def test_register_usage_reports_callee(ctx):
    out = GH.register_usage(ctx, "0x101000", "0x38")
    assert any(p["arg_position"] == 1 for p in out["passed_to"])


def test_register_usage_rejects_non_argument_register(ctx):
    assert "error" in GH.register_usage(ctx, "0x101000", "rax")
    assert "error" in GH.register_usage(ctx, "0x101000", "0x99")


def test_register_usage_unspilled_register(ctx):
    out = GH.register_usage(ctx, "0x101000", "rcx")
    assert out["home_slot"] is None and "never spilled" in out["summary"]


def test_register_usage_cfg_join_idiom(ctx):
    # funcC: `if (p == NULL) p = &default;` -- the deref after the join must still be seen
    out = GH.register_usage(ctx, "0x102000", "0x38")
    assert out["analysis"] == "cfg-dataflow"
    assert out["dereferenced"] is True


# ---- value_usage (decompilation lens) ----
def test_value_usage_reports_deref_and_call(ctx):
    out = GH.value_usage(ctx, "0x101000", "param_1")
    assert out["dereferenced"] is True
    assert any(p["callee"] == "funcB" for p in out["passed_to"])


def test_value_usage_unknown_variable_hints(ctx):
    out = GH.value_usage(ctx, "0x101000", "nosuchvar")
    assert "error" in out and "available_vars" in out


def test_value_usage_register_name_maps_to_param(ctx):
    out = GH.value_usage(ctx, "0x101000", "rdi")
    assert "param_1" in out["hint"]


# ---- decompile ----
def test_decompile_returns_source(ctx):
    out = GH.decompile(ctx, "0x101000")
    assert "funcA" in out and "param_1" in out


def test_decompile_missing(ctx):
    assert GH.decompile(ctx, "0x101100").startswith("(no decompilation")


# ---- struct_shape ----
def test_struct_shape_single_field_not_aggregate(ctx):
    out = GH.struct_shape(ctx, "0x101000", "param_1")
    assert out["is_aggregate"] is False                       # one field at 0x0 is just T *


def test_struct_shape_rejects_bad_register(ctx):
    assert "error" in GH.struct_shape(ctx, "0x101000", "rax")


# ---- elf tools ----
def test_info_reports_elf(ctx):
    out = ELF.info(ctx)
    assert out["format"] == "elf" and out["pie"] is True


def test_imports_lists_undefined_symbols(ctx):
    out = ELF.imports(ctx)
    assert "strlen" in out["imports"] and out["count"] >= 1


def test_read_values_typed_array(ctx):
    out = ELF.read_values(ctx, "0x101000", type="int8", count=4, signed=False)
    assert out["count"] == 4 and len(out["values"]) == 4


def test_read_values_bad_type(ctx):
    assert "error" in ELF.read_values(ctx, "0x101000", type="float128")


def test_frame_delta_helper():
    insns = {"0": "push rbp", "1": "push rbx", "2": "mov rbp,rsp"}
    delta, has_rbp = GH._frame_delta(insns, ["0", "1", "2"])
    assert (delta, has_rbp) == (16, True)


def test_parse_stack_off():
    assert GH._parse_stack_off("-0x40") == -64
    assert GH._parse_stack_off("0xfffffffffffffff0") == -16
    assert GH._parse_stack_off("garbage") is None
