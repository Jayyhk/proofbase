## Local

```
python -m venv .venv && .venv/bin/pip install -r requirements.txt
cd web && npm install && cd ..

docker run -d --name proofbase-db -p 5432:5432 \
  -e POSTGRES_USER=proofbase -e POSTGRES_PASSWORD=proofbase -e POSTGRES_DB=proofbase postgres

psql postgresql://proofbase:proofbase@localhost:5432/proofbase -f db/schema.sql
.venv/bin/python -m scripts.seed data/json/*.json
scripts/dev.sh
```

API on :5000, frontend on :5173.

Sample proofs are in `data/lean`, their extracted graphs in `data/json`. To compile new proofs, install Lean:

```
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
for v in compile-env/*/; do (cd "$v" && lake update && lake exe cache get); done
```

## Deploy

Put a `db_password` in `terraform/terraform.tfvars`, then:

```
cd terraform && terraform apply
scripts/deploy.sh
```
