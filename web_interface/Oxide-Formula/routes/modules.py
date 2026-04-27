from fastapi import APIRouter, HTTPException
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


class OptEntry(BaseModel):
   type: str
   mangle: bool
   default: str | int | bool | None


class ModuleDocumentationResponse(BaseModel):
   description: str
   opts_doc: dict[str, OptEntry]


REQUIRED_CHART_MODULES = [
    "entropy_graph",
    "byte_histogram",
    "byte_ngrams",
    "opcode_histogram",
    "opcode_ngrams",
    "call_graph",
    "control_flow_graph",
    "binary_visualizer",
    "triage",
    "cyclo_complexity",
]

_TYPE_MAP = {
   str: "str",
   int: "int",
   bool: "bool",
}


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


@modules_router.get("/{module_name}/documentation")
async def get_module_documentation(module_name: str) -> ModuleDocumentationResponse:
   doc = None
   try:
      doc = oxide.documentation(module_name)
   except Exception:
      pass

   if doc is None:
      raise HTTPException(status_code=404, detail=f"Module not found: {module_name}")

   opts_doc = {}
   raw_opts = doc.get("opts_doc")
   if raw_opts:
      for opt_name, opt_info in raw_opts.items():
         py_type = opt_info.get("type") if isinstance(opt_info, dict) else None
         opts_doc[opt_name] = OptEntry(
            type=_TYPE_MAP.get(py_type, "str"),
            mangle=opt_info.get("mangle", False) if isinstance(opt_info, dict) else False,
            default=opt_info.get("default") if isinstance(opt_info, dict) else None,
         )

   return ModuleDocumentationResponse(
      description=doc.get("description", ""),
      opts_doc=opts_doc,
   )
