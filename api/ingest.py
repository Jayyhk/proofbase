from collections import Counter

from sqlalchemy import text

from api.queries import get_proof_graph, store_proof_stats
from api.render import render_svg


def ingest_proof(conn, proof_id, data):
    # the graph has to be self-consistent before any of it is written: a duplicate name would
    # trip the unique index and a dangling edge would raise KeyError below, both a long way
    # from the cause
    counts = Counter(n["name"] for n in data["nodes"])
    duplicate = next((n for n, c in counts.items() if c > 1), None)
    if duplicate:
        raise ValueError(f"extractor reported {duplicate} twice")
    known = set(counts)
    for e in data["edges"]:
        if e["from"] not in known or e["to"] not in known:
            missing = e["from"] if e["from"] not in known else e["to"]
            raise ValueError(f"edge {e['from']} -> {e['to']} names {missing}, which is not a declaration")

    # insert all declarations (nodes) in the db
    declarations = [
        {
            "proof_id": proof_id,
            "name": n["name"],
            "kind": n["kind"],
            "is_generated": n["generated"],
            "is_instance": n.get("instance", False),
            "is_simp": n.get("simp", False),
            "line_start": n["lineStart"],
            "line_end": n["lineEnd"],
        }
        for n in data["nodes"]
    ]
    conn.execute(
        text("""
            INSERT INTO declaration
                (proof_id, name, kind, is_generated, is_instance, is_simp, line_start, line_end)
            VALUES
                (:proof_id, :name, :kind, :is_generated, :is_instance, :is_simp, :line_start, :line_end)
        """),
        declarations
    )

    # read ids back so we can map declaration names to ids
    rows = conn.execute(
        text("SELECT id, name FROM declaration WHERE proof_id = :proof_id"),
        {"proof_id": proof_id}
    ).fetchall()
    id_by_name = {name: decl_id for decl_id, name in rows}

    # for the edges, the json references declarations by name. convert them to ids
    edges = [
        {"proof_id": proof_id, "from_id": id_by_name[e["from"]], "to_id": id_by_name[e["to"]]}
        for e in data["edges"]
    ]
    if edges:
        conn.execute(
            text("INSERT INTO edge (proof_id, from_id, to_id) VALUES (:proof_id, :from_id, :to_id)"),
            edges
        )

    # insert (declaration, axiom) pairs into axiom_dependency
    axiom_deps = [
        {"declaration_id": id_by_name[n["name"]], "axiom_id": id_by_name[a]}
        for n in data["nodes"]
        for a in n["axioms"]
    ]
    if axiom_deps:
        conn.execute(
            text("INSERT INTO axiom_dependency (declaration_id, axiom_id) VALUES (:declaration_id, :axiom_id)"),
            axiom_deps
        )

    # the drawn graph hides generated declarations, definitions and standard axioms, so a
    # dependency that passes through one is stepped over to the next declaration that shows.
    # doing it here walks each declaration once, where sql has to re-cross the hidden region
    # for every source it carries through the recursion
    policy = {r[0] for r in conn.execute(text("SELECT name FROM axiom_policy"))}
    kind_of = {n["name"]: n["kind"] for n in data["nodes"]}
    shown = {n["name"] for n in data["nodes"]
             if not n["generated"] and n["kind"] in ("theorem", "axiom") and n["name"] not in policy}
    after = {}
    for e in data["edges"]:
        after.setdefault(e["from"], []).append(e["to"])
    stepped = []
    for source in shown:
        if kind_of[source] == "axiom": # axioms depend on nothing
            continue
        seen, stack = set(), list(after.get(source, ()))
        while stack:
            name = stack.pop()
            if name in seen:
                continue
            seen.add(name)
            if name not in shown:
                stack.extend(after.get(name, ()))
            elif name != source: # stepping over can lead back to the source
                stepped.append({"proof_id": proof_id,
                                "from_id": id_by_name[source], "to_id": id_by_name[name]})
    if stepped:
        conn.execute(
            text("INSERT INTO visible_edge (proof_id, from_id, to_id) VALUES (:proof_id, :from_id, :to_id)"),
            stepped
        )

    # rows exist now. compute stats, render the svg, mark status as ready
    store_proof_stats(conn, proof_id)
    graph = get_proof_graph(conn, proof_id)
    conn.execute(
        text("UPDATE proof SET lean_version = :lean_version, graph_svg = :svg, status = 'ready' WHERE id = :id"),
        {
            "lean_version": data["proof"]["leanVersion"],
            "svg": render_svg(graph["nodes"], graph["edges"]),
            "id": proof_id,
        }
    )
