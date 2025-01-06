import uvicorn 
import configparser
from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
import os
import sys

config = configparser.ConfigParser()
#check if the config file exists, else create it
if os.path.isfile("config.ini"):
    config.read("config.ini")
else:
    config['General'] = {"host": "localhost",
                         "hostport" : '8000',
                         "clientport" : '3000',
                         "clientip": "localhost"}
    config["Oxide"] = {"path": ""}
    with open("config.ini", 'w') as configfile:
        config.write(configfile)

host = config.get("General", "host")
clientport = config.getint("General", "clientport")
hostport = config.getint("General", "hostport")
oxide_path = config.get("Oxide", "path")
clientip = config.get("General", "clientip")

# Check if oxide_path is a valid path
while not os.path.exists(oxide_path) or not os.path.isdir(oxide_path):
    print(f"The path {oxide_path} is invalid.")
    oxide_path = input("Please enter the path to oxide/src: ")

# Update the config.ini file with the new path
config.set("Oxide", "path", oxide_path)
with open("config.ini", "w") as configfile:
    config.write(configfile)

sys.path.append(oxide_path)

from routes import collections_router, modules_router, retrieve_router, oxide_router
app = FastAPI()
app.add_middleware(
    CORSMiddleware,
    allow_origins=[f"http://{host}:{clientport}", f"http://{clientip}:{clientport}"],  # Adjust to your SvelteKit dev server URL
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
    
