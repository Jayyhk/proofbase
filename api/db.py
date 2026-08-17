import os

from sqlalchemy import create_engine

# database location is DATABASE_URL env var in prod, local dev default
# postgresql via the psycopg driver, username:password and database name are all "proofbase"
DATABASE_URL = os.environ.get(
    "DATABASE_URL", "postgresql+psycopg://proofbase:proofbase@localhost:5432/proofbase"
)

# one shared connection pool for the whole app
engine = create_engine(DATABASE_URL)
