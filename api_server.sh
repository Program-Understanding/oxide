#!/bin/bash

set -euo pipefail

# Run from this directory
cd "$(dirname "$0")"

PY_BIN="${PYTHON_BIN:-python3}"

echo "Starting Oxide-Formula backend with ${PY_BIN}"
cd web_interface/Oxide-Formula/
"${PY_BIN}" main.py
