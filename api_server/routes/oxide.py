from fastapi import APIRouter, HTTPException
from oxide.core import oxide as oxide
from fastapi import HTTPException
import json
import traceback

oxide_router = APIRouter(prefix="/oxide")

supported_api_funs = {
    #fun name : [args]
    "retrieve_all": ["module"],
    "retrieve": ["module","oid or oids_list","opts"],
    "get_field": ["module","oid or oids_list","field","opts"]
}

@oxide_router.get("/methods")
async def api_get_funs():
    return supported_api_funs

@oxide_router.get("/retrieve/")
async def retrieve_module(mod,oid,opts="{}",oids_list=None):
    opts = json.loads(opts)
    try:
        if oids_list is not None:
            results=oxide.retrieve(mod,oids_list,opts)
        else:
            results = oxide.retrieve(mod,oid,opts)
        print(results)
        return results
    except Exception as e:
        print(traceback.format_exc())
        return {"Internal error": str(e)}

@oxide_router.get("/retrieve_all/")
async def retrieve_all_module(mod):
    try:
        results = oxide.retrieve_all(mod)
        return results
    except Exception as e:
        return {"Internal error": str(e)}

@oxide_router.get("/get_field/")
async def get_field_module(mod,oid,field,opts="{}",oids_list=None):
    opts = json.loads(opts)
    try:
        if oids_list is not None:
            results = oxide.get_field(mod,oid,field,opts,oids_list)
        else:
            results = oxide.get_field(mod,oid,field,opts)
        if not results: #don't know a better way to handle ghidra disasm failing
            return {"error": -1}
        return results
    except Exception as e:
        return {"Internal error": str(e)}
