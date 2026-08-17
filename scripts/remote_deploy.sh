#!/bin/bash
set -euo pipefail # stop on any error, unset var, or failed pipe stage

command -v psql >/dev/null || sudo dnf install -y postgresql15 # install psql

echo "--> schema"
psql "$PSQL_URL" -f db/schema.sql # drop and recreate every table

echo "--> build"
sudo docker build -t proofbase . # builds the react bundle, python deps, and lean toolchains (cached after the first build)

echo "--> ingest"
# load the seed proofs. --rm deletes the container after this job finishes
sudo docker run --rm -e DATABASE_URL="$DATABASE_URL" proofbase python -m scripts.seed data/json/*.json

echo "--> run"
sudo docker rm -f proofbase 2>/dev/null || true # remove previous container.
# -d backgrounds the container. always restart it if it stops. -p maps the ec2's port 80 to gunicorn's 8000
sudo docker run -d --restart always -p 80:8000 -e DATABASE_URL="$DATABASE_URL" --name proofbase proofbase

echo "--> prune dangling images"
sudo docker image prune -f # delete the old untagged image (the build cache is kept)

echo "--> up"
