from fastapi import APIRouter, HTTPException
from pydantic import BaseModel, Field
from oxide.core import oxide as oxide

try:
    import networkx as nx
except ImportError:
    nx = None

retrieve_router = APIRouter(prefix="/analysis")


class RetrieveRequest(BaseModel):
    module: str
    oid: str | None = None
    oids: list[str] | None = None
    collection: str | None = None
    opts: dict = Field(default_factory=dict)


class RetrieveResponse(BaseModel):
    module: str
    target: dict
    results: dict | list | str | int | float | bool | None


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


@retrieve_router.post("/retrieve")
async def retrieve_module(payload: RetrieveRequest) -> RetrieveResponse:
    try:
        provided_targets = sum(
            [
                payload.oid is not None,
                payload.oids is not None,
                payload.collection is not None,
            ]
        )
        if provided_targets != 1:
            raise HTTPException(
                status_code=422,
                detail="Exactly one of oid, oids, or collection must be provided",
            )

        if payload.collection is not None:
            cid = oxide.get_cid_from_name(payload.collection)
            if not cid:
                raise HTTPException(status_code=404, detail=f"Collection not found: {payload.collection}")
            oid_list = oxide.expand_oids(cid)
            target = {"type": "collection", "collection": payload.collection, "cid": cid, "oids": oid_list}
            results = _normalize_result(oxide.retrieve(payload.module, oid_list, payload.opts))
            return RetrieveResponse(module=payload.module, target=target, results=results)

        if payload.oids is not None:
            target = {"type": "oids", "oids": payload.oids}
            results = _normalize_result(oxide.retrieve(payload.module, payload.oids, payload.opts))
            return RetrieveResponse(module=payload.module, target=target, results=results)

        target = {"type": "oid", "oid": payload.oid}
        results = _normalize_result(oxide.retrieve(payload.module, payload.oid, payload.opts))
        return RetrieveResponse(module=payload.module, target=target, results=results)
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
