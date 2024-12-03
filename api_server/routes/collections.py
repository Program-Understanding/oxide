from fastapi import APIRouter, HTTPException
from oxide.core import oxide as oxide
from fastapi import HTTPException
collections_router = APIRouter(prefix="/collections")

@collections_router.get("/")
async def get_collections():
   collection_names = oxide.collection_names()
   return collection_names


@collections_router.get("/files")
async def get_collection_files(selected_collection: str):
    names = {}
    try:
        cid = oxide.get_cid_from_name(selected_collection)
        file_oids = oxide.expand_oids(cid)
        for oid in file_oids:
            names.update({f'{oxide.get_names_from_oid(oid)}' : f'${oid}'})
        return names
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
      