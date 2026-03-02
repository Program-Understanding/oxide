#!/bin/bash

set -euo pipefail

# Set the current directory as the working directory
cd "$(dirname "$0")"

node_major="$(node -p "process.versions.node.split('.')[0]")"

if [ "$node_major" -lt 20 ]; then
	echo "Detected Node $(node -v). Using Node 20 wrapper for Next 16 compatibility..."
	npm run dev:node20
else
	npm run dev
fi