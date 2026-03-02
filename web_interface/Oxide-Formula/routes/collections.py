from fastapi import APIRouter, HTTPException
from pydantic import BaseModel
from oxide.core import oxide as oxide

collections_router = APIRouter(prefix="/collections")


class CollectionFile(BaseModel):
    oid: str
    names: list[str]


class CollectionsResponse(BaseModel):
    collections: list[str]


class CollectionFilesResponse(BaseModel):
    collection: str
    cid: str
    files: list[CollectionFile]


@collections_router.get("/")
async def get_collections() -> CollectionsResponse:
    collection_names = oxide.collection_names()
    return CollectionsResponse(collections=collection_names)


@collections_router.get("/{collection_name}/files")
async def get_collection_files(collection_name: str) -> CollectionFilesResponse:
    try:
        cid = oxide.get_cid_from_name(collection_name)
        if not cid:
            raise HTTPException(status_code=404, detail=f"Collection not found: {collection_name}")

        file_oids = oxide.expand_oids(cid)
        files: list[CollectionFile] = []
        for oid in file_oids:
            names = oxide.get_names_from_oid(oid)
            files.append(CollectionFile(oid=oid, names=sorted(list(names))))

        return CollectionFilesResponse(collection=collection_name, cid=cid, files=files)
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
      