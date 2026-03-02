#!/bin/bash

# Set the current directory as the working directory
# Ensures this works regardless of where script is executed from
cd "$(dirname "$0")"

# Launch frontend
cd web_interface/oxide-app/
./web_app.sh