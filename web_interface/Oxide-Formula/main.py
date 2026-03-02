import uvicorn
import configparser
from pathlib import Path
from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
import os
import sys


BASE_DIR = Path(__file__).resolve().parent
CONFIG_PATH = BASE_DIR / "config.ini"
ENV_OXIDE_SRC = "OXIDE_SRC_PATH"


def create_default_config(config: configparser.ConfigParser) -> None:
    config["General"] = {
        "host": "localhost",
        "hostport": "8000",
        "clientport": "3000",
        "clientip": "localhost",
    }
    config["Oxide"] = {"path": ""}


def is_valid_oxide_src(path_str: str) -> bool:
    if not path_str:
        return False
    path = Path(path_str).expanduser().resolve()
    return path.is_dir() and (path / "oxide" / "core" / "oxide.py").is_file()


def resolve_oxide_src(config: configparser.ConfigParser) -> str:
    env_path = os.getenv(ENV_OXIDE_SRC, "").strip()
    config_path = config.get("Oxide", "path", fallback="").strip()
    auto_path = str((BASE_DIR.parent.parent / "src").resolve())

    for candidate in (env_path, config_path, auto_path):
        if is_valid_oxide_src(candidate):
            return str(Path(candidate).expanduser().resolve())

    raise RuntimeError(
        "Unable to resolve Oxide src path. Set OXIDE_SRC_PATH or update [Oxide] path in "
        f"{CONFIG_PATH}. Tried: env='{env_path}', config='{config_path}', auto='{auto_path}'."
    )


config = configparser.ConfigParser()
if CONFIG_PATH.is_file():
    config.read(CONFIG_PATH)
else:
    create_default_config(config)
    with open(CONFIG_PATH, "w") as configfile:
        config.write(configfile)

host = config.get("General", "host", fallback="localhost")
clientport = config.getint("General", "clientport", fallback=3000)
hostport = config.getint("General", "hostport", fallback=8000)
clientip = config.get("General", "clientip", fallback="localhost")

oxide_path = resolve_oxide_src(config)
config.set("Oxide", "path", oxide_path)
with open(CONFIG_PATH, "w") as configfile:
    config.write(configfile)

if oxide_path not in sys.path:
    sys.path.append(oxide_path)

from routes import collections_router, modules_router, retrieve_router, oxide_router
app = FastAPI()

allowed_origins = {
    f"http://{host}:{clientport}",
    f"http://{clientip}:{clientport}",
    f"http://localhost:{clientport}",
    f"http://127.0.0.1:{clientport}",
}

app.add_middleware(
    CORSMiddleware,
    allow_origins=sorted(allowed_origins),
    allow_origin_regex=r"^https?://(localhost|127\.0\.0\.1)(:\d+)?$",
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)
app.include_router(collections_router, prefix="/api")
app.include_router(modules_router, prefix="/api")
app.include_router(retrieve_router, prefix="/api")
app.include_router(oxide_router, prefix="/api")

if __name__ == "__main__":
    uvicorn.run(app, port=hostport, host=host)
    
