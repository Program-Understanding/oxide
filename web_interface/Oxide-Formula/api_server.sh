#!/bin/bash

# Set the current directory as the working directory
# Ensures this works regardless of where script is executed from
cd "$(dirname "$0")/api_server"

# Add the src directory to PYTHONPATH
echo $pwd
export PYTHONPATH=$PYTHONPATH:$(pwd)/src
echo $PYTHONPATH

python3 main.py
