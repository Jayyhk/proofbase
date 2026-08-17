#!/bin/bash
set -euo pipefail # exit on error, on unset vars, and on any failed pipe stage
cd "$(dirname "$0")/.." # run from repo root

KEY=~/.ssh/id_ed25519_proofbase # private key for the ec2

APP_IP=$(terraform -chdir=terraform output -raw app_ip) # ec2 IP
DB_HOST=$(terraform -chdir=terraform output -raw db_endpoint | cut -d: -f1) # db endpoint is host:port, get the host
DB_PASS=$(sed -n 's/^db_password *= *"\(.*\)"/\1/p' terraform/terraform.tfvars) # get the password from tfvars

DATABASE_URL="postgresql+psycopg://proofbase:${DB_PASS}@${DB_HOST}:5432/proofbase" # +psycopg for SQLalchemy
PSQL_URL="postgresql://proofbase:${DB_PASS}@${DB_HOST}:5432/proofbase" # plain url for psql cli

echo "==> rsync code -> $APP_IP"
# mirror the repo on the ec2. --delete removes files on the destination that are not on the source.
# StrictHostKeyChecking=no skips the unknown host prompt so the script isn't interactive
rsync -az --delete -e "ssh -i $KEY -o StrictHostKeyChecking=no" \
  --exclude=.venv --exclude=.git --exclude=terraform --exclude=__pycache__ --exclude=node_modules \
  --exclude=.lake --exclude=Upload.lean --exclude=.upload.json \
  ./ ec2-user@"$APP_IP":proofbase/

echo "==> deploy on box"
# ssh in and run the remote deploy script there, passing in both connection strings
ssh -i "$KEY" -o StrictHostKeyChecking=no ec2-user@"$APP_IP" "cd ~/proofbase && DATABASE_URL='$DATABASE_URL' PSQL_URL='$PSQL_URL' bash scripts/remote_deploy.sh"

echo "==> live at http://$APP_IP/proofs"
curl -s "http://$APP_IP/health" && echo # should print {"ok":true}
