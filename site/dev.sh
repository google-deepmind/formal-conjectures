#!/usr/bin/env bash
# dev.sh — Quick local website development.
#
# Downloads the conjectures data from the live production site and builds the
# website locally, without needing to compile any Lean code.
#
# Requirements: Python 3, Node.js (or install via: conda install -c conda-forge nodejs)
#
# Usage:
#   ./dev.sh              # build and serve on port 8080
#   ./dev.sh --build-only # build without serving
#   ./dev.sh --port 3000  # serve on a custom port

set -euo pipefail
cd "$(dirname "$0")"

LIVE_URL="https://google-deepmind.github.io/formal-conjectures"
PORT=8080
SERVE=true

# Parse arguments
while [[ $# -gt 0 ]]; do
  case "$1" in
    --build-only) SERVE=false; shift ;;
    --port) PORT="$2"; shift 2 ;;
    *) echo "Unknown option: $1"; echo "Usage: $0 [--build-only] [--port PORT]"; exit 1 ;;
  esac
done

# Check for Node.js
if ! command -v node &>/dev/null; then
  echo "Error: Node.js not found."
  echo "Install it via one of:"
  echo "  conda install -c conda-forge nodejs"
  echo "  sudo apt install nodejs"
  echo "  https://nodejs.org/"
  exit 1
fi

echo "==> Downloading data from live site ($LIVE_URL) ..."
mkdir -p data

python3 ../scripts/download_catalog.py --out data

echo "==> Building website ..."
FC_RENDER_BASE="$LIVE_URL" node build.js

echo "==> Done. Output in site/"

if [[ "$SERVE" == "true" ]]; then
  echo "==> Serving at http://localhost:${PORT} (Ctrl+C to stop)"
  python3 -m http.server "$PORT" --directory site
fi
