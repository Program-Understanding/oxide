# Oxide-Formula — FastAPI REST Backend

`Oxide-Formula` is the REST adapter that bridges the Oxide Python runtime (`src/oxide`) and the Next.js frontend (`oxide-app`). It translates HTTP requests into calls to the Oxide core API and normalizes Python data structures (sets, tuples, NetworkX graphs) into JSON-serializable formats.

---

## Architecture overview

```
Browser (Next.js)
└── HTTP → FastAPI (localhost:8000)
    └── Oxide Python runtime (src/oxide/core/oxide.py)
        ├── Datastore (filesystem or SQLite)
        └── Modules (extractors, analyzers, map_reducers)
```

**Key design principle:** The adapter is a thin shim. It does not implement analysis logic — it exposes the Oxide Python API over HTTP and handles serialization.

---

## Project structure

```
Oxide-Formula/
├── main.py               # FastAPI app, CORS config, route wiring, Oxide path resolution
├── config.ini            # Runtime config (host, port, Oxide src path)
├── requirements.txt      # Python dependencies
├── api_server.sh        # Dev launcher
└── routes/
    ├── __init__.py       # Exports all routers
    ├── collections.py    # Collection CRUD (list, files, create, delete)
    ├── modules.py        # Module introspection (list, chart capabilities, documentation)
    ├── retrieve.py        # Module execution (oid, oids, or collection targeting)
    ├── imports.py        # File import, OID deletion, collection modification
    └── oxide.py          # Generic wrappers (retrieve_all, get_field)
```

---

## Route summary

All routes are mounted under `/api`.

| Route | Method | Purpose |
|-------|--------|---------|
| `/modules/` | GET | List all loaded Oxide modules |
| `/modules/chart-capabilities` | GET | Check which chart modules are available |
| `/modules/{name}/documentation` | GET | Get opts_doc and description for a module |
| `/collections/` | GET | List all collections |
| `/collections/{name}/files` | GET | Get OIDs and filenames in a collection |
| `/analysis/retrieve` | POST | Run a module (single OID, OID list, or collection) |
| `/oxide/methods` | GET | List generic wrapper method signatures |
| `/oxide/retrieve-all/{module}` | GET | Get all cached records for a module |
| `/oxide/get-field` | POST | Extract a single field from module results |
| `/import/upload` | POST | Import files into Oxide |
| `/import/collection` | POST | Create a named collection |
| `/import/collection/{name}` | DELETE | Delete a collection |
| `/import/collection/{name}/oids` | POST | Add OIDs to a collection |
| `/import/collection/{name}/oids/delete` | POST | Remove OIDs from a collection |
| `/import/oid/{oid}` | DELETE | Flush all data for an OID |

---

## `/analysis/retrieve` — Module execution

This is the primary endpoint for running analysis.

**Request:** exactly one of `oid`, `oids`, or `collection` must be provided.

```json
// Single file
{ "module": "entropy_graph", "oid": "abc123...", "opts": {} }

// Multiple files
{ "module": "entropy_graph", "oids": ["abc...", "def..."], "opts": {} }

// Entire collection
{ "module": "triage", "collection": "malware_set", "opts": {} }
```

**Response:**

```json
{
  "module": "entropy_graph",
  "target": { "type": "oid", "oid": "abc123..." },
  "results": { ... }
}
```

For a collection run, `target` includes the full CID and OID list:

```json
{
  "module": "triage",
  "target": {
    "type": "collection",
    "collection": "malware_set",
    "cid": "...",
    "oids": ["abc...", "def..."]
  },
  "results": { ... }
}
```

**Error codes:**
- `404` — OID, collection, or module not found
- `422` — Zero or multiple targeting fields provided
- `500` — Unexpected Python exception (traceback in detail)

---

## Result normalization (`_normalize_result`)

The Python runtime produces types that are not JSON-serializable. The adapter normalizes them before returning:

| Python type | Normalized to |
|------------|--------------|
| `set` | `list` (recursive) |
| `tuple` | `list` (recursive) |
| `dict` | plain `dict` with string keys |
| `nx.Graph` | [node-link data](https://networkx.org/documentation/stable/reference/readwrite/generated/networkx.readwrite.json_graph.node_link_data.html) |
| `None`, `str`, `int`, `float`, `bool` | passed through |
| anything else | `str()` |

---

## Module documentation model

Each module exposes `documentation()` returning:

```python
{
    "description": "...",
    "opts_doc": {
        "arch": {
            "type": str,      # Python type class
            "mangle": True,  # Affects cache key?
            "default": "x86"  # Default value (None if unset)
        }
    },
    "private": False,
    "set": True,     # Accepts collection/OID list inputs?
    "atomic": False  # Single-file processing?
}
```

The adapter translates Python types to `"str"`, `"int"`, or `"bool"` strings in the HTTP response. Unknown types default to `"str"`.

---

## Adding a new chart module

To make a module appear in the charts page dropdown:

1. Edit `routes/modules.py` → `REQUIRED_CHART_MODULES`:

```python
REQUIRED_CHART_MODULES = [
    ...
    "my_new_chart_module",
]
```

2. Create a renderer in the frontend. See `oxide-app/README.md` → "Adding a new chart renderer".

---

## Configuring the Oxide source path

The adapter needs to find `src/oxide/core/oxide.py`. Resolution order:

1. `OXIDE_SRC_PATH` environment variable
2. `[Oxide] path` in `config.ini`
3. Auto: `{repo}/src` (relative to `web_interface/Oxide-Formula/`)

The resolved path is written back to `config.ini` on startup.

---

## Configuration (`config.ini`)

```ini
[General]
host = localhost
hostport = 8000
clientip = localhost
clientport = 3000

[Oxide]
path = /path/to/oxide/src
```

CORS is auto-configured for `localhost:3000` and `127.0.0.1:3000`. Port is configurable via `clientport`.

---

## Running locally

```bash
cd web_interface/Oxide-Formula
pip install -r requirements.txt
./api_server.sh
```

This runs `uvicorn main:app` on `localhost:8000`. The startup script also validates the Oxide source path and writes it to `config.ini`.

---

## Dependencies

| Package | Purpose |
|--------|---------|
| `fastapi` | Web framework |
| `uvicorn` | ASGI server |
| `pydantic` | Request/response validation |
| `networkx` | Graph normalization (optional — silently skipped if unavailable) |

Python 3.9+ required.
