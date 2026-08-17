import os
import threading

from flask import Flask, request, send_from_directory

from api import queries
from api.compiler import CompileError, compile_and_extract, supported_versions
from api.db import engine
from api.ingest import ingest_proof

compile_lock = threading.Lock()

# React dist frontend path
DIST = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "web", "dist")

# Flask application object
# any request under /assets/... is served from web/dist/assets/...
app = Flask(__name__, static_folder=os.path.join(DIST, "assets"), static_url_path="/assets")


################### API routes


# check if server is up
@app.get("/health")
def health():
    return {"ok": True}


# list the Lean versions available for upload (newest first)
@app.get("/versions")
def versions():
    return {"versions": supported_versions()}


# list all proofs for the main table
@app.get("/proofs")
def proofs():
    with engine.connect() as conn:
        return {"proofs": queries.get_proofs(conn)}


# function run in a background thread that does the compilation
def run_compile(proof_id, file, version):
    with compile_lock: # sequential
        with engine.begin() as conn:
            queries.mark_proof_compiling(conn, proof_id) # status: queued->compiling
        try:
            graph = compile_and_extract(file, version) # compile the Lean, run extractor to get proof json
            with engine.begin() as conn:
                ingest_proof(conn, proof_id, graph) # load the proof, stats, svg, into the db. status: compiling->ready
        except CompileError as e:
            with engine.begin() as conn:
                queries.mark_proof_failed(conn, proof_id, str(e)) # Lean build error/timeout
        except Exception as e:
            with engine.begin() as conn:
                queries.mark_proof_failed(conn, proof_id, f"internal error: {e}") # any other failures


# validate an uploaded proof, queue it, and start compiling in the bg 
@app.post("/compile")
def compile_proof():
    body = request.get_json(silent=True)
    if not isinstance(body, dict):
        return {"error": "expected a JSON object"}, 400
    name = body.get("name")
    file = body.get("file")
    version = body.get("version")
    if not isinstance(name, str) or not name:
        return {"error": "missing 'name'"}, 400
    if not isinstance(file, str) or not file:
        return {"error": "missing 'file'"}, 400
    if version not in supported_versions():
        return {"error": f"unsupported Lean version: {version}"}, 400
    with engine.begin() as conn:
        proof_id = queries.create_queued_proof(conn, name, f"leanprover/lean4:v{version}", file) # insert the queued proof, get its id
    threading.Thread(target=run_compile, args=(proof_id, file, version), daemon=True).start() # spawn a thread running run_compile
    return {"name": name, "proof_id": proof_id, "status": "queued"}, 201 # return name and proof_id and use 201 Created


# serve a proof's stored graph svg as an image
@app.get("/proofs/<int:proof_id>/graph")
def graph(proof_id):
    with engine.connect() as conn:
        svg = queries.get_proof_svg(conn, proof_id) # get pre-rendered svg string
    if svg is None:
        return {"error": f"no graph for proof {proof_id}"}, 404
    return app.response_class(svg, mimetype="image/svg+xml") # send svg with correct image content-type


# serve a proof's raw .lean source as plain text
@app.get("/proofs/<int:proof_id>/file")
def proof_file(proof_id):
    with engine.connect() as conn:
        contents = queries.get_proof_file(conn, proof_id) # get source text for the proof
    if contents is None:
        return {"error": f"no file for proof {proof_id}"}, 404
    return app.response_class(contents, mimetype="text/plain") # return source as plain text


# delete a proof
@app.delete("/proofs/<int:proof_id>")
def delete_proof(proof_id):
    with engine.begin() as conn:
        queries.delete_proof(conn, proof_id) # delete a proof and cascade
    return {"deleted": proof_id}


# rename a proof using the new name from the request body
@app.patch("/proofs/<int:proof_id>")
def rename_proof(proof_id):
    body = request.get_json(silent=True)
    name = body.get("name") if isinstance(body, dict) else None
    if not isinstance(name, str) or not name.strip():
        return {"error": "missing 'name'"}, 400
    with engine.begin() as conn:
        queries.rename_proof(conn, proof_id, name.strip()) # update the row's name to the trimmed value
    return {"id": proof_id, "name": name.strip()}


# get one declaration's fields, axioms, and neighbors in one response
@app.get("/declarations/<int:declaration_id>")
def declaration(declaration_id):
    with engine.connect() as conn:
        row = queries.get_declaration(conn, declaration_id) # the declaration itself
        if row is None:
            return {"error": f"no declaration {declaration_id}"}, 404
        axioms = queries.get_declaration_axioms(conn, declaration_id) # its axioms, each with a risk kind
        neighbors = queries.get_declaration_neighbors(conn, declaration_id) # its dependencies and dependents
    return {**row, "axioms": axioms, **neighbors} # flatten into one dict object


################### page routes


# serve the app at the root url
@app.get("/")
def index():
    return send_from_directory(DIST, "index.html")


# <path:path> matches any url
# serve a real file if it exists, else index.html
@app.get("/<path:path>")
def spa(path):
    if os.path.isfile(os.path.join(DIST, path)):
        return send_from_directory(DIST, path) # a real file in dist
    return send_from_directory(DIST, "index.html") # unknown path
