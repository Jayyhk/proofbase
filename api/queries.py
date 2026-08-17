from sqlalchemy import text


# compute stats for one proof in the table row
def store_proof_stats(conn, proof_id):
    conn.execute(
        text("""
            UPDATE proof SET
                -- count of this proof's real declarations
                declarations = (
                    SELECT count(*) FROM graph_declaration d
                    WHERE d.proof_id = :id
                ),
                -- roots = declarations where nothing points at them (exclude axioms)
                roots = (
                    SELECT count(*) FROM graph_declaration d
                    WHERE d.proof_id = :id
                    AND NOT EXISTS (
                        SELECT 1 FROM edge e
                        JOIN graph_declaration f ON f.id = e.from_id
                        WHERE e.to_id = d.id AND f.kind <> 'axiom'
                    )
                ),
                -- edges between 2 real declarations (exclude axioms)
                edges = (
                    SELECT count(*) FROM edge e
                    JOIN graph_declaration f ON f.id = e.from_id
                    JOIN graph_declaration t ON t.id = e.to_id
                    WHERE e.proof_id = :id AND f.kind <> 'axiom'
                ),
                -- count axiom uses by risk kind
                flagged = (SELECT count(*) FROM axiom_use WHERE proof_id = :id AND kind <> 'standard'),
                sorry = (SELECT count(*) FROM axiom_use WHERE proof_id = :id AND kind = 'sorry'),
                trust = (SELECT count(*) FROM axiom_use WHERE proof_id = :id AND kind = 'trust'),
                unsafe = (SELECT count(*) FROM axiom_use WHERE proof_id = :id AND kind = 'unsafe'),
                custom = (SELECT count(*) FROM axiom_use WHERE proof_id = :id AND kind = 'custom')
            WHERE id = :id
        """),
        {"id": proof_id}
    )


# get pre-rendered graph svg
def get_proof_svg(conn, proof_id):
    return conn.execute(
        text("SELECT graph_svg FROM proof WHERE id = :id"), {"id": proof_id}
    ).scalar()


# get all proofs for the table view
def get_proofs(conn):
    rows = (
        conn.execute(
            text("""
            SELECT
                id, name, lean_version,
                to_char(created_at, 'YYYY-MM-DD') AS added,
                to_char(created_at, 'YYYY-MM-DD HH24:MI:SS.US') AS created_at,
                declarations, roots, edges, flagged, sorry, trust, unsafe, custom, status, error
            FROM proof
            ORDER BY created_at DESC
        """)
        )
        .mappings()
        .all()
    )
    return [dict(r) for r in rows]


# create initial proof row with status="queued" and return its id
def create_queued_proof(conn, name, lean_version, file):
    return conn.execute(
        text("""
            INSERT INTO proof (name, status, lean_version, file)
            VALUES (:name, 'queued', :lean_version, :file)
            RETURNING id
        """),
        {"name": name, "lean_version": lean_version, "file": file}
    ).scalar()


# get a proof's .lean source
def get_proof_file(conn, proof_id):
    return conn.execute(
        text("SELECT file FROM proof WHERE id = :id"), {"id": proof_id}
    ).scalar()


# set proof status to "compiling"
def mark_proof_compiling(conn, proof_id):
    conn.execute(
        text("UPDATE proof SET status = 'compiling' WHERE id = :id"), {"id": proof_id}
    )


# set proof status to "failed" and record the error
def mark_proof_failed(conn, proof_id, error):
    conn.execute(
        text("UPDATE proof SET status = 'failed', error = :error WHERE id = :id"),
        {"id": proof_id, "error": error}
    )


# delete a proof (and cascade)
def delete_proof(conn, proof_id):
    conn.execute(text("DELETE FROM proof WHERE id = :id"), {"id": proof_id})


# rename a proof
def rename_proof(conn, proof_id, name):
    conn.execute(
        text("UPDATE proof SET name = :name WHERE id = :id"),
        {"id": proof_id, "name": name}
    )


# get one declaration with its proof name and lean version
def get_declaration(conn, declaration_id):
    row = (
        conn.execute(
            text("""
            SELECT d.*, p.name AS proof, p.lean_version
            FROM declaration d
            JOIN proof p ON p.id = d.proof_id
            WHERE d.id = :declaration_id
        """),
            {"declaration_id": declaration_id}
        )
        .mappings()
        .first()
    )
    if row is None:
        return None
    result = dict(row)
    result.pop("proof_id", None)
    return result


# axiom risk rankings
def kind_severity_sql(kind_expr):
    return f"""CASE {kind_expr}
        WHEN 'trust' THEN 1
        WHEN 'custom' THEN 2
        WHEN 'sorry' THEN 3
        WHEN 'unsafe' THEN 4
        ELSE 0 END"""


# get the axioms a single declaration uses, with their risk kind and severity number
def get_declaration_axioms(conn, declaration_id):
    rows = (
        conn.execute(
            text(f"""
            SELECT axiom AS name, kind, {kind_severity_sql("kind")} AS severity
            FROM axiom_use
            WHERE declaration_id = :declaration_id
            ORDER BY axiom
        """),
            {"declaration_id": declaration_id}
        )
        .mappings()
        .all()
    )
    return [dict(r) for r in rows]


# helper sql query to get the severity number of a declaration. take the max of
# 1) if the declaration is an axiom (severity 2)
# 2) the worst axiom it uses
def severity_sql(alias):
    return f"""
        GREATEST(
            CASE WHEN {alias}.kind = 'axiom' THEN 2 ELSE 0 END,
            COALESCE((
                SELECT max({kind_severity_sql("au.kind")})
                FROM axiom_use au
                WHERE au.declaration_id = {alias}.id
            ), 0) -- coalesce: no axioms means max is NULL, so default to 0
        ) AS severity
    """


# get a declaration's dependencies and dependents
def get_declaration_neighbors(conn, declaration_id):
    dependencies = (
        conn.execute(
            text(f"""
            SELECT t.id, t.name, {severity_sql("t")}
            FROM edge e
            JOIN declaration f ON f.id = e.from_id
            JOIN graph_declaration t ON t.id = e.to_id
            WHERE e.from_id = :id AND f.kind <> 'axiom'
            ORDER BY severity DESC, t.name
        """),
            {"id": declaration_id}
        )
        .mappings()
        .all()
    )
    dependents = (
        conn.execute(
            text(f"""
            SELECT f.id, f.name, {severity_sql("f")}
            FROM edge e
            JOIN graph_declaration f ON f.id = e.from_id
            JOIN declaration t ON t.id = e.to_id
            WHERE e.to_id = :id AND f.kind <> 'axiom'
            ORDER BY severity DESC, f.name
        """),
            {"id": declaration_id}
        )
        .mappings()
        .all()
    )
    return {
        "dependencies": [dict(r) for r in dependencies],
        "dependents": [dict(r) for r in dependents],
    }


# get a proof's drawable nodes and edges. the ids let the frontend map a clicked node/edge back to a declaration
def get_proof_graph(conn, proof_id):
    nodes = (
        conn.execute(
            text(f"""
            SELECT d.id, d.name, d.kind, {severity_sql("d")}
            FROM graph_declaration d
            WHERE d.proof_id = :proof_id
            ORDER BY d.id
        """),
            {"proof_id": proof_id}
        )
        .mappings()
        .all()
    )
    edges = (
        conn.execute(
            text("""
            SELECT e.from_id, e.to_id
            FROM edge e
            JOIN graph_declaration f ON f.id = e.from_id
            JOIN graph_declaration t ON t.id = e.to_id
            WHERE e.proof_id = :proof_id AND f.kind <> 'axiom'
        """),
            {"proof_id": proof_id}
        )
        .mappings()
        .all()
    )
    return {"nodes": [dict(n) for n in nodes], "edges": [dict(e) for e in edges]}
