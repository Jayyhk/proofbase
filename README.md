## Local

Needs a `.venv` with `requirements.txt` and `npm install` in `web/`.

```
# postgres, once. dev.sh starts this container on later runs
docker run -d --name proofbase-db -p 5432:5432 \
  -e POSTGRES_USER=proofbase -e POSTGRES_PASSWORD=proofbase -e POSTGRES_DB=proofbase postgres

psql postgresql://proofbase:proofbase@localhost:5432/proofbase -f db/schema.sql  # create the tables
.venv/bin/python -m scripts.seed data/json/*.json                                # load the example proofs
scripts/dev.sh                                                                   # flask on :5000, vite on :5173
```

## Deploy

```
cd terraform && terraform apply    # ec2 + rds, needs db_password in terraform.tfvars
scripts/deploy.sh                  # rsync, build, seed, run
```

## Proofs

Sample proofs are given in `/data` and are seeded into the table by `scripts/seed.py`.
The `.lean` sources live in `data/lean`, their extracted graphs in `data/json`.
