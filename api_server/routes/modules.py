from fastapi import APIRouter
from oxide.core import oxide as oxide

modules_router = APIRouter(prefix="/modules")

@modules_router.get("/")
async def get_modules():
   modules_names = oxide.modules_list()
   return modules_names
