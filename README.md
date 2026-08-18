## Local

You need a `.venv` with `requirements.txt` installed, and `npm install` in `web/`.

Start Postgres. You only have to do this once, `dev.sh` starts the container after that:

```
docker run -d --name proofbase-db -p 5432:5432 \
  -e POSTGRES_USER=proofbase -e POSTGRES_PASSWORD=proofbase -e POSTGRES_DB=proofbase postgres
```

Then create the tables, load the proofs, and run it:

```
psql postgresql://proofbase:proofbase@localhost:5432/proofbase -f db/schema.sql
.venv/bin/python -m scripts.seed data/json/*.json
scripts/dev.sh
```

The API runs on port 5000 and the frontend on port 5173.

## Deploy

Terraform provisions the EC2 instance and an RDS Postgres. Put a `db_password` in
`terraform/terraform.tfvars` first, since the variable has no default.

```
cd terraform && terraform apply
scripts/deploy.sh
```

`deploy.sh` copies the repo to the instance, then creates the tables, builds the image,
loads the proofs, and runs the container on port 80.

## Proofs

There are some sample proofs in `data/lean`, with their extracted graphs in `data/json`.
`seed.py` reads the graphs and loads them into the table.
