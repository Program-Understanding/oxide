import tempfile
import os
from fastapi import APIRouter, HTTPException, UploadFile
from pydantic import BaseModel
from typing import Optional
from oxide.core import oxide as oxide

imports_router = APIRouter(prefix="/import")


class ImportedFile(BaseModel):
    name: str
    oid: str
    success: bool
    error: Optional[str] = None


class UploadResponse(BaseModel):
    uploaded: list[ImportedFile]
    failed: list[ImportedFile]
    total: int


MAX_FILES = 20


@imports_router.post("/upload")
async def upload_files(files: list[UploadFile]) -> UploadResponse:
    # Debug: check if modules are loaded
    import logging
    debug_logger = logging.getLogger("oxide.debug")
    debug_logger.debug("Source modules available: %s", oxide.modules_available.get("source", []))
    debug_logger.debug("All modules_available: %s", dict(oxide.modules_available))

    if not files:
        raise HTTPException(status_code=400, detail="No files provided")

    if len(files) > MAX_FILES:
        raise HTTPException(
            status_code=400,
            detail=f"Too many files. Maximum is {MAX_FILES} per request.",
        )

    uploaded: list[ImportedFile] = []
    failed: list[ImportedFile] = []

    for file in files:
        if not file.filename:
            failed.append(ImportedFile(name="<unknown>", oid="", success=False, error="No filename"))
            continue

        contents = await file.read()
        if not contents:
            failed.append(ImportedFile(name=file.filename, oid="", success=False, error="Empty file"))
            continue

        # Use the original filename in the temp path so file_meta shows it correctly
        safe_name = "".join(c for c in file.filename if c.isalnum() or c in "._-") or "upload"
        with tempfile.NamedTemporaryFile(delete=False, dir="/tmp", prefix=f"{safe_name}_") as tmp:
            tmp.write(contents)
            tmp_path = tmp.name

        try:
            oid_from_data = oxide.get_oid_from_data(contents)
            process_files_ok = None
            process_meta_ok = None

            mod_type = oxide.get_mod_type("files")
            init_modules = list(oxide.initialized_modules.keys())

            opts_file = {"file_contents": contents}
            opts_meta = {"file_location": tmp_path, "stat": {"size": len(contents)}}

            if not oxide.exists("files", oid_from_data, opts_file):
                process_files_ok = oxide.process("files", [oid_from_data], opts_file)
            else:
                process_files_ok = True  # already exists

            process_meta_ok = oxide.process("file_meta", [oid_from_data], opts_meta, force=True)

            if process_files_ok and process_meta_ok:
                uploaded.append(ImportedFile(name=file.filename, oid=oid_from_data, success=True))
            else:
                failed.append(ImportedFile(
                    name=file.filename,
                    oid=oid_from_data,
                    success=False,
                    error=(
                        f"files module={process_files_ok}, file_meta module={process_meta_ok}, "
                        f"'files' mod_type={mod_type}, init_modules={init_modules[:5]}"
                    )
                ))
        except Exception as e:
            failed.append(ImportedFile(name=file.filename, oid="", success=False, error=str(e)))
        finally:
            try:
                os.unlink(tmp_path)
            except OSError:
                pass

    return UploadResponse(
        uploaded=uploaded,
        failed=failed,
        total=len(files),
    )


class CreateCollectionRequest(BaseModel):
    name: str
    oid_list: list[str]
    notes: str = ""


class CreateCollectionResponse(BaseModel):
    name: str
    cid: str
    oid_count: int


@imports_router.post("/collection")
async def create_collection(payload: CreateCollectionRequest) -> CreateCollectionResponse:
    if not payload.name:
        raise HTTPException(status_code=400, detail="Collection name is required")
    if not payload.oid_list:
        raise HTTPException(status_code=400, detail="oid_list cannot be empty")

    try:
        ok = oxide.create_collection(payload.name, payload.oid_list, payload.notes)
        if not ok:
            raise HTTPException(status_code=500, detail="Failed to create collection")
        cid = oxide.get_cid_from_name(payload.name)
        return CreateCollectionResponse(
            name=payload.name,
            cid=cid or "",
            oid_count=len(payload.oid_list),
        )
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
