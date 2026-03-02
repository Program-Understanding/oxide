# Oxide-Formula (FastAPI Adapter)

`Oxide-Formula` is the REST backend that bridges the Oxide Python runtime (`src/oxide`) and the new Next/React frontend (`web_interface/oxide-app`).

## Running locally

### Requirements

- Python 3.9+
- `fastapi`, `uvicorn` (from `requirements.txt`)
- Accessible Oxide source directory (`.../src`)

### Start

```bash
cd web_interface/Oxide-Formula
pip install -r requirements.txt
./api_server.sh
```
can run api_server.sh in oxide dir or Oxide-Formula dir

By default, the API runs on `http://localhost:8000`.



## Endpoint Info

### `GET /api/modules/`

Returns loaded module names.

Response:

```json
{
	"modules": ["file_meta", "entropy_graph", "call_graph"]
}
```

### `GET /api/modules/chart-capabilities`

Response:

```json
{
	"required_chart_modules": [
		{ "module": "entropy_graph", "available": true },
		{ "module": "call_graph", "available": false }
	]
}
```

### `GET /api/collections/`

Response:

```json
{
	"collections": ["default", "sample_binaries"]
}
```

### `GET /api/collections/{collection_name}/files`

Response:

```json
{
	"collection": "default",
	"cid": "...",
	"files": [
		{ "oid": "...", "names": ["binary.exe"] }
	]
}
```

Errors:

- `404` if collection name does not resolve to `cid`
- `500` for unexpected runtime failures

### `POST /api/analysis/retrieve`

Request model:

```json
{
	"module": "entropy_graph",
	"oid": "...",
	"opts": {}
}
```

Targeting rules:

- exactly **one** of `oid`, `oids`, or `collection` must be provided
- otherwise returns `422`

Collection form example:

```json
{
	"module": "entropy_graph",
	"collection": "default",
	"opts": {}
}
```

Response envelope:

```json
{
	"module": "entropy_graph",
	"target": { "type": "oid", "oid": "..." },
	"results": { }
}
```

### `GET /api/oxide/methods`

Returns supported generic wrapper signatures:

```json
{
	"methods": {
		"retrieve_all": ["module"],
		"get_field": ["module", "oid", "field", "opts"]
	}
}
```

### `GET /api/oxide/retrieve-all/{module_name}`

Returns all records for a module via `oxide.retrieve_all(module_name)` in normalized form.

### `POST /api/oxide/get-field`

Request:

```json
{
	"module": "file_meta",
	"oid": "...",
	"field": "size",
	"opts": {}
}
```

Response:

```json
{
	"module": "file_meta",
	"oid": "...",
	"field": "size",
	"value": 12345
}
```

## Configuration

`config.ini`:

- `[General] host` / `hostport`: FastAPI bind host/port
- `[General] clientip` / `clientport`: preferred frontend origin
- `[Oxide] path`: optional explicit Oxide src path

`main.py` writes back resolved path to config once validated.


