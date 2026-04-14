# dwarf5 — DWARF4/5 Extractor Module

Oxide extractor module that parses DWARF debug information from ELF binaries.
Primary target is **DWARF5** (§ references are to the DWARF5 standard); DWARF4
and earlier are supported where the format is compatible.

---

## File Overview

```
dwarf5/
├── module_interface.py   Oxide entry point
├── extract.py            Top-level orchestration
├── info.py               .debug_info  (CU headers + DIE tree)
├── abbrev.py             .debug_abbrev (abbreviation tables)
├── forms.py              DW_FORM_* attribute value decoder
├── constants.py          DWARF enums and name maps
├── models.py             Shared dataclasses (UnitHeader)
├── stream.py             BinaryReader helper
├── leb128.py             ULEB128 / SLEB128 decoding
├── line.py               .debug_line  (line-number program header)
├── aranges.py            .debug_aranges (address→CU lookup)
├── addr.py               .debug_addr  (DWARF5 address table)
├── str_offsets.py        .debug_str_offsets (DWARF5 string-offset table)
├── loclists.py           .debug_loclists (DWARF5 — scaffold)
└── rnglists.py           .debug_rnglists (DWARF5 — scaffold)
```

---

## Per-File Details

### `module_interface.py`
**Oxide glue layer.** Implements the standard `documentation()` / `process()` interface.

- Adds the module directory to `sys.path` (via `__init__.py`) so submodules can
  use bare `import` names.
- At import time does `import extract`; all other submodules are transitively
  pulled in then.
- Calls `extract.parse_dwarf(oid, data, header)` inside `process()` and stores
  the result with `api.store()`.
- Supports a **`--reload` opt** that calls `importlib.reload()` on all 14
  submodules in dependency order, allowing source edits to take effect inside a
  running oxide shell without restarting:

  ```
  run dwarf5 ^mybinary --reload --reprocess | show
  ```

**opts_doc:**
| opt | type | default | effect |
|-----|------|---------|--------|
| `reload` | bool | False | hot-reload all submodules before parsing |

---

### `extract.py`
**Top-level orchestration.** Called by `module_interface.py`.

1. Receives `(oid, raw_bytes, header)` where `header.section_info` is a dict of
   `section_name → {section_offset, section_len, …}` from oxide's
   `object_header` module.
2. Calls `_initialize_sections()` to slice each `.debug_*` section out of the
   raw binary bytes into a shared `debug_sections` dict:
   ```python
   debug_sections[".debug_info"]["data"]  # raw bytes for that section
   ```
3. Dispatches each present section to its parser and collects results into the
   output dict.
4. Calls `_normalize_info()` to convert the raw DIE list into the shape
   `high_dwarf` (and other consumers) expect:
   ```
   { cu_offset: { die_offset: { "Tag": "DW_TAG_xxx", "Attributes": [(name, val), …] } } }
   ```
5. Resolves `DW_AT_language` integer → human name (e.g. `29` → `"C11"`) using
   `LANGUAGE_NAME` from `constants.py`.

**Sections parsed (when present):**
| key | parser |
|-----|--------|
| `.debug_info` | `info.parse_debug_info` |
| `.debug_addr` | `addr.parse_debug_addr` |
| `.debug_str_offsets` | `str_offsets.parse_str_offsets` |
| `.debug_rnglists` | `rnglists.parse_rnglists` |
| `.debug_loclists` | `loclists.parse_loclists` |
| `.debug_aranges` | `aranges.parse_aranges` |
| `.debug_line` | `line.parse_line` |

---

### `info.py`
**Parses `.debug_info`** — the core DWARF section containing all type and
variable information, organised as a tree of Debugging Information Entries
(DIEs).

**What it does:**
1. `_parse_unit_header()` reads each Compilation Unit (CU) header.
   - DWARF4: `unit_length | version | abbrev_offset | address_size`
   - DWARF5: `unit_length | version | unit_type | address_size | abbrev_offset`
     (field order changed in DWARF5 §7.5.1.1)
2. Looks up the abbrev table for this CU via `abbrev.parse_abbrev_table()`.
3. Iterates DIEs, calling `forms.decode_form()` for each attribute.
4. Tracks **unit-scoped base attributes** (`DW_AT_str_offsets_base`,
   `DW_AT_addr_base`, etc.) in a `unit_bases` dict so DWARF5 indirect forms
   (STRX, ADDRX) resolve correctly within the same CU.

**Returns:** `{"compile_units": [{"header": UnitHeader, "dies": [...]}]}`

---

### `abbrev.py`
**Parses `.debug_abbrev`** — the abbreviation table that describes DIE
structure.

Each entry maps an `abbrev_code` → `(tag, has_children, [(attr_name, form, implicit_const), …])`.
Multiple CUs can share an abbrev table or have their own (determined by
`abbrev_offset` in the CU header).

`parse_abbrev_table(data, offset)` starts reading at `offset` and returns a
`dict[int, AbbrevEntry]` for that table. A code of 0 terminates the table.

---

### `forms.py`
**Decodes DW_FORM_* attribute values** (DWARF5 §7.5.4).

`decode_form(form, reader, dwarf64, address_size, debug_sections, unit_bases,
implicit_const)` dispatches on `form` and returns a Python value:

| Form family | Return type | Source |
|---|---|---|
| `ADDR` | `int` | raw address |
| `DATA1..DATA8`, `UDATA`, `SDATA` | `int` | integer constant |
| `FLAG`, `FLAG_PRESENT` | `bool` | boolean |
| `STRP` | `str` | `.debug_str[offset]` |
| `LINE_STRP` | `str` | `.debug_line_str[offset]` |
| `STRX*` | `str` | `.debug_str_offsets[base+idx]` → `.debug_str` |
| `ADDRX*` | `int` | `.debug_addr[base+idx]` |
| `REF*` | `int` | DIE offset |
| `BLOCK*`, `EXPRLOC` | `bytes` | raw expression bytes |
| `SEC_OFFSET` | `int` | section offset (4 or 8 bytes) |
| `IMPLICIT_CONST` | `int` | value stored in abbrev table |
| `INDIRECT` | recursive | reads form code first |

String resolution for STRX uses `str_offsets.lookup_str_offset()` then looks
up in `.debug_str`. This requires `DW_AT_str_offsets_base` to already be
populated in `unit_bases` (handled by `info.py`'s attribute loop).

---

### `constants.py`
**All DWARF enumerations and name-lookup tables.**

Key classes (all `IntEnum`):
- `DwarfTag` — `DW_TAG_*` codes (§7.5.4)
- `DwarfAttribute` — `DW_AT_*` codes (§7.5.4)
- `DwarfForm` — `DW_FORM_*` codes (§7.5.4)
- `DwarfLanguage` — `DW_LANG_*` codes including all DWARF5 additions (C11,
  Swift, Kotlin, C17, Rust, Ruby, etc.) (§7.12)
- `DwarfEncoding` — `DW_ATE_*` base type encodings
- `DwarfOp` — `DW_OP_*` expression opcodes (§7.7)
- `DwarfUnitType` — `DW_UT_*` (DWARF5 §7.5.1)

Convenience dicts:
- `LANGUAGE_NAME` — `{int → "C11", "Rust", …}` used by `extract.py` to
  humanise `DW_AT_language`.

---

### `models.py`
**Shared dataclasses.**

`UnitHeader` — holds all fields parsed from a CU header:
```python
@dataclass
class UnitHeader:
    unit_offset: int
    is_64bit: bool
    unit_length: int
    version: int
    unit_type: int | None   # DWARF5 only
    address_size: int
    abbrev_offset: int
    unit_end: int
    extras: dict            # type_signature, dwo_id, etc.
```

---

### `stream.py`
**`BinaryReader` — low-level binary reading helper.**

Wraps a `bytes` buffer with a position cursor. All parsers create one of these
from their section's `data` bytes.

Methods: `read_u8/u16/u32/u64`, `read_bytes(n)`, `read_cstring()`,
`read_uleb128()`, `read_sleb128()`, `tell()`, `seek(offset)`.

Default endianness is little-endian (all current DWARF targets).

---

### `leb128.py`
**LEB128 integer decoding** (DWARF §7.6).

- `decode_uleb128(data, offset)` → `(value, new_offset)` — unsigned
- `decode_sleb128(data, offset)` → `(value, new_offset)` — signed

Used by `stream.BinaryReader.read_uleb128/sleb128()`. Abbrev codes,
`DW_FORM_UDATA/SDATA`, and many other DWARF fields use LEB128 encoding.

---

### `line.py`
**Parses `.debug_line`** — the line-number program (§6.2).

Currently parses the **header only** (does not execute the line-number program
state machine or produce a full address→line mapping).

Header field differences between versions:
- **DWARF4**: `unit_length | version | header_length | min_instr_len | default_is_stmt | …`
- **DWARF5**: `unit_length | version | address_size | segment_selector_size | header_length | …`
  (§6.2.4 — `address_size` and `segment_selector_size` precede `header_length`)

Returns per unit:
```python
{
  "version": 5, "address_size": 8, "segment_selector_size": 0,
  "header_length": 51, "min_instruction_length": 1,
  "max_ops_per_instruction": 1, "default_is_stmt": True,
  "line_base": -5, "line_range": 14, "opcode_base": 13,
  "standard_opcode_lengths": [0,1,1,1,1,0,0,0,1,0,0,1]
}
```

---

### `aranges.py`
**Parses `.debug_aranges`** — the address-range-to-CU lookup table (§6.1.2).

Simple fixed-width entries: `(segment, address, length)` triples terminated by
a `(0, 0)` pair. Used to quickly find which CU covers a given address.

Returns:
```python
{"units": [{"offset": 0, "version": 2, "debug_info_offset": 0,
            "address_size": 8, "segment_size": 0, "is_64bit": False,
            "entries": [{"segment": None, "address": 4457, "length": 225}]}]}
```

---

### `addr.py`
**Parses `.debug_addr`** — DWARF5 address table (§7.27).

Stores relocated addresses indexed by `DW_FORM_addrx*` forms. Returns a flat
`list[int]` of all addresses in the section (after any unit header).

Used by `forms.py` when decoding `DW_FORM_addrx` / `DW_FORM_addrx1..4`.
The base index for a given CU comes from `DW_AT_addr_base` (tracked in
`unit_bases` by `info.py`).

---

### `str_offsets.py`
**Parses `.debug_str_offsets`** — DWARF5 string offset table (§7.26).

DWARF5 introduces `DW_FORM_strx*` forms where a DIE stores a small integer
index rather than a full 4-byte string offset. This section maps
`(base + index × 4)` → offset into `.debug_str`.

- `parse_str_offsets(data, dwarf64)` — returns `list[int]` of all offsets,
  skipping the optional DWARF5 section header (8 bytes for 32-bit DWARF).
- `lookup_str_offset(data, base, index, dwarf64)` — used by `forms.py` to
  perform a single indexed lookup without parsing the whole section.

The `base` comes from `DW_AT_str_offsets_base` in the CU DIE.

---

### `loclists.py` *(scaffold)*
**Parses `.debug_loclists`** — DWARF5 location lists (§7.29).

Currently returns `{"raw_size": N, "status": "scaffold"}`. Full parsing will
decode `DW_LLE_*` opcodes and produce `(start_addr, end_addr, expr_bytes)` per
entry. These are referenced by `DW_AT_location` with `DW_FORM_loclistx` or
`DW_FORM_sec_offset`.

---

### `rnglists.py` *(scaffold)*
**Parses `.debug_rnglists`** — DWARF5 range lists (§7.28).

Currently returns `{"raw_size": N, "status": "scaffold"}`. Full parsing will
decode `DW_RLE_*` opcodes and produce `(start_addr, end_addr)` pairs. These are
referenced by `DW_AT_ranges` with `DW_FORM_rnglistx` or `DW_FORM_sec_offset`
in functions with non-contiguous address ranges.

---

## Data Flow

```
ELF binary (raw bytes)
        │
        ▼
module_interface.process()
  │  gets: data (raw bytes), header.section_info (offsets/sizes from object_header)
  │
  ▼
extract._initialize_sections()
  │  produces: debug_sections = { ".debug_info": {"data": bytes, ...}, ... }
  │
  ├──► info.parse_debug_info(debug_sections)
  │         │
  │         ├── abbrev.parse_abbrev_table()   reads .debug_abbrev
  │         └── forms.decode_form()           for each attribute
  │                   │
  │                   ├── str_offsets.lookup_str_offset()  for STRX forms
  │                   └── reads .debug_str / .debug_line_str / .debug_addr
  │
  ├──► line.parse_line()            reads .debug_line
  ├──► aranges.parse_aranges()      reads .debug_aranges
  ├──► addr.parse_debug_addr()      reads .debug_addr (if present)
  ├──► str_offsets.parse_str_offsets()  reads .debug_str_offsets (if present)
  ├──► rnglists.parse_rnglists()    reads .debug_rnglists (if present)
  └──► loclists.parse_loclists()    reads .debug_loclists (if present)
        │
        ▼
extract._normalize_info()
  │  converts raw DIE list → { cu_offset: { die_offset: {Tag, Attributes} } }
  │  resolves DW_AT_language int → name string
        │
        ▼
api.store("dwarf5", oid, result)   stored in oxide datastore
```

---

## The `debug_sections` Contract

Every section-level parser receives `debug_sections` as a dict:

```python
debug_sections = {
    ".debug_info":        {"data": bytes, "section_offset": int, "section_len": int},
    ".debug_abbrev":      {"data": bytes, ...},
    ".debug_str":         {"data": bytes, ...},
    ".debug_line_str":    {"data": bytes, ...},
    ".debug_str_offsets": {"data": bytes, ...},
    ".debug_addr":        {"data": bytes, ...},
    # ... only sections present in the binary
}
```

`forms.py` uses this dict to resolve string/address cross-references between
sections at attribute-decode time.

---

## Output Shape

The result stored by `api.store()`:

```python
{
    "sections": [".debug_abbrev", ".debug_aranges", ...],   # sorted list

    ".debug_info": {
        0: {                                    # CU offset
            12: {                               # DIE offset
                "Tag": "DW_TAG_compile_unit",
                "Attributes": [
                    ("DW_AT_name",     "hello.c"),
                    ("DW_AT_language", "C11"),
                    ("DW_AT_low_pc",   4457),
                    ...
                ]
            },
            ...
        }
    },

    ".debug_line": {
        "units": [{"version": 5, "address_size": 8, "header_length": 51, ...}]
    },

    ".debug_aranges": {
        "units": [{"offset": 0, "version": 2, "entries": [...], ...}]
    },

    # present only when section exists in binary:
    ".debug_addr":        [int, ...],
    ".debug_str_offsets": [int, ...],
    ".debug_rnglists":    {"raw_size": N, "status": "scaffold"},
    ".debug_loclists":    {"raw_size": N, "status": "scaffold"},
}
```

---

## Development Workflow

### Apply code edits without restarting the shell
```
run dwarf5 ^mybinary --reload --reprocess | show
```
`--reload` calls `importlib.reload()` on all submodules in dependency order.
`--reprocess` forces oxide to re-run `process()` instead of serving the cached result.

### Full restart (always works)
```
exit          # in oxide shell
./oxide.sh    # relaunch
run dwarf5 ^mybinary --reprocess | show
```

### Running against both DWARF4 and DWARF5 binaries
```
run dwarf5 ^hello_4 --reprocess | show
run dwarf5 ^hello_5 --reprocess | show
```

---

## Sections Not Yet Implemented

| Section | DWARF | Notes |
|---------|-------|-------|
| `.debug_ranges` | DWARF4 | Range lists for non-contiguous functions |
| `.debug_loc` | DWARF4 | Location lists for variables |
| `.debug_pubnames` / `.debug_pubtypes` | DWARF4 | Accelerated name lookup |
| `.debug_names` | DWARF5 | Accelerated name/type lookup (§6.1.1) |
| `.debug_frame` / `.eh_frame` | DWARF4/5 | Call Frame Information |
| `.debug_macro` / `.debug_macinfo` | DWARF4/5 | Macro expansion data |
| `.debug_types` | DWARF4 | Type units |
