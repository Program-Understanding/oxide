#!/bin/bash

# Set the current directory as the working directory
# Ensures this works regardless of where script is executed from
cd "$(dirname "$0")"

# Add the src directory to PYTHONPATH
echo $pwd
export PYTHONPATH=$PYTHONPATH:$(pwd)/src
echo $PYTHONPATH

# Execute your Python script
python3 api_server/main.py
