from fastapi import APIRouter
from oxide.core import oxide as oxide
 
     
retrieve_router = APIRouter()

@retrieve_router.get("/retrieve")
async def retrieve_module(selected_module: str, selected_collection: str = None, selected_oid: str = None):
    try:
        if selected_oid:
            oid_list = []
            oid_list.append(selected_oid)
            
            results = oxide.retrieve(selected_module, oid_list)
            return results
        
        if selected_collection:
            cid = oxide.get_cid_from_name(selected_collection)
            files = oxide.expand_oids(cid)
            results = oxide.retrieve(selected_module, files)
            return results
        
    except Exception as e:
        return {"error": str(e)}
