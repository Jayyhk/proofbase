import datetime
import hashlib
import json
import sys
from pathlib import Path

from sqlalchemy import text

from api.db import engine
from api.ingest import ingest_proof

# load the pre-extracted proofs into an empty db. run as: python -m scripts.seed data/json/*.json
paths = [Path(arg) for arg in sys.argv[1:]]

# hash the name for a fixed but arbitrary order, so the dates below aren't alphabetical
order = sorted(paths, key=lambda p: hashlib.md5(p.stem.encode()).hexdigest())
latest = datetime.date.today()
# space the proofs 15 days apart, with the last one landing on today
date_of = {
    p.stem: (latest - datetime.timedelta(days=15 * (len(order) - 1 - i))).isoformat()
    for i, p in enumerate(order)
}

for path in paths:
    data = json.loads(path.read_text())
    lean = path.parents[1] / "lean" / (path.stem + ".lean")  # data/json/x.json -> data/lean/x.lean
    file = lean.read_text()
    with engine.begin() as conn:
        # the row has to exist first so ingest_proof has an id to hang declarations off
        proof_id = conn.execute(
            text("""
                INSERT INTO proof (name, file, created_at)
                VALUES (:name, :file, CAST(:d AS timestamptz))
                RETURNING id
            """),
            {"name": path.stem, "file": file, "d": date_of[path.stem]}
        ).scalar()
        ingest_proof(conn, proof_id, data)  # declarations, edges, axioms, then stats and the svg
    print(f"{path.stem}: proof {proof_id} ({date_of[path.stem]}), "
          f"{len(data['nodes'])} declarations, {len(data['edges'])} edges")
