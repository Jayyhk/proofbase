#!/bin/bash
set -uo pipefail # no -e here, a missing postgres container shouldn't kill the script
cd "$(dirname "$0")/.." # run from repo root

echo "==> postgres"
docker start proofbase-db >/dev/null 2>&1 || echo "  (proofbase-db not found or already up)"

echo "==> flask API on :5000"
.venv/bin/python -m flask --app api.app run --port 5000 --debug & # & backgrounds it so vite can run too
FLASK_PID=$!
# ctrl+c stops vite, not flask, so kill flask when this script exits
trap "echo; echo '==> stopping'; kill $FLASK_PID 2>/dev/null" EXIT

echo "==> vite on :5173  (Ctrl+C to stop)"
cd web && npm run dev # vite proxies /proofs, /compile, etc to :5000. see vite.config.ts
