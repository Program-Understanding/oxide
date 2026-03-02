from fastapi import APIRouter
from pydantic import BaseModel
from oxide.core import oxide as oxide

modules_router = APIRouter(prefix="/modules")


class ModulesResponse(BaseModel):
   modules: list[str]


class ModuleCapability(BaseModel):
   module: str
   available: bool


class ChartCapabilitiesResponse(BaseModel):
   required_chart_modules: list[ModuleCapability]


REQUIRED_CHART_MODULES = [
   "entropy_graph",
   "byte_histogram",
   "byte_ngrams",
   "opcode_histogram",
   "opcode_ngrams",
   "call_graph",
   "control_flow_graph",
   "binary_visualizer",
]

@modules_router.get("/")
async def get_modules() -> ModulesResponse:
   modules_names = oxide.modules_list()
   return ModulesResponse(modules=modules_names)


@modules_router.get("/chart-capabilities")
async def get_chart_capabilities() -> ChartCapabilitiesResponse:
   modules_names = set(oxide.modules_list())
   capabilities = [
      ModuleCapability(module=module_name, available=(module_name in modules_names))
      for module_name in REQUIRED_CHART_MODULES
   ]
   return ChartCapabilitiesResponse(required_chart_modules=capabilities)
