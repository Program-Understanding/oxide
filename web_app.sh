#!/bin/bash

# Set the current directory as the working directory
# Ensures this works regardless of where script is executed from
cd "$(dirname "$0")"

# Execute your Python script
cd web_app/client/
npm run dev