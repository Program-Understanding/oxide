#!/bin/bash

# Set the current directory as the working directory
# Ensures this works regardless of where script is executed from
cd "$(dirname "$0")"

# Add the src directory to PYTHONPATH
export PYTHONPATH=$PYTHONPATH:$(pwd)/src

# Execute your Python script
python3 src/oxide/shell.py
