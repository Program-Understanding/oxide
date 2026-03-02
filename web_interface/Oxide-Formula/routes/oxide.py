from fastapi import APIRouter, HTTPException
from pydantic import BaseModel, Field
from oxide.core import oxide as oxide
from typing import Any

try:
    import networkx as nx
except ImportError:
    nx = None

oxide_router = APIRouter(prefix="/oxide")


class MethodsResponse(BaseModel):
    methods: dict[str, list[str]]


class RetrieveAllResponse(BaseModel):
    module: str
    results: dict


class GetFieldRequest(BaseModel):
    module: str
    oid: str
    field: str
    opts: dict = Field(default_factory=dict)


class GetFieldResponse(BaseModel):
    module: str
    oid: str
    field: str
    value: Any = None


def _normalize_result(value):
    if value is None or isinstance(value, (str, int, float, bool)):
        return value

    if isinstance(value, set):
        return [_normalize_result(item) for item in value]

    if isinstance(value, tuple):
        return [_normalize_result(item) for item in value]

    if isinstance(value, list):
        return [_normalize_result(item) for item in value]

    if isinstance(value, dict):
        return {str(key): _normalize_result(item) for key, item in value.items()}

    if nx is not None and isinstance(value, nx.Graph):
        return nx.node_link_data(value)

    return str(value)


supported_api_funs = {
    "retrieve_all": ["module"],
    "get_field": ["module", "oid", "field", "opts"],
}

@oxide_router.get("/methods")
async def api_get_funs() -> MethodsResponse:
    return MethodsResponse(methods=supported_api_funs)


@oxide_router.get("/retrieve-all/{module_name}")
async def retrieve_all_module(module_name: str) -> RetrieveAllResponse:
    try:
        results = _normalize_result(oxide.retrieve_all(module_name))
        return RetrieveAllResponse(module=module_name, results=results)
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@oxide_router.post("/get-field")
async def get_field_module(payload: GetFieldRequest) -> GetFieldResponse:
    try:
        value = _normalize_result(
            oxide.get_field(payload.module, payload.oid, payload.field, payload.opts)
        )
        return GetFieldResponse(
            module=payload.module,
            oid=payload.oid,
            field=payload.field,
            value=value,
        )
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
