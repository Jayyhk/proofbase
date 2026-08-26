import json
import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent # repo root
COMPILE_ENV = ROOT / "compile-env"
EXTRACTOR = COMPILE_ENV / "extract.lean"
ELAN_BIN = str(Path.home() / ".elan" / "bin")


# no extra behavior except subclassing Exception so we can raise CompileError
class CompileError(Exception):
    pass


# get supported lean versions by the directory version names that exist
def supported_versions():
    dirs = (p.name for p in COMPILE_ENV.iterdir() if (p / "lean-toolchain").exists())
    return sorted(dirs, key=lambda v: [int(x) for x in v.split(".")], reverse=True)


# run a command with lean toolchain on PATH and returns its result
def run(args, cwd):
    # copy env vars and put elan's bin dir on PATH so lake/lean are found
    env = {**os.environ, "PATH": ELAN_BIN + os.pathsep + os.environ.get("PATH", "")}

    return subprocess.run( # run to completion, however long it takes
        args, cwd=cwd, env=env, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )


# drop lake's "trace:" lines
def clean_output(result):
    lines = [l for l in (result.stdout + result.stderr).splitlines() if not l.startswith("trace:")]
    return "\n".join(lines).strip()


# lean --json prints one message per line
def parse_messages(result):
    messages = []
    for line in result.stdout.splitlines():
        try:
            messages.append(json.loads(line))
        except json.JSONDecodeError:
            pass # lake prints plain lines too
    return messages


# just the errors, in the "file:line:col: message" form the failure log shows
def error_text(messages):
    return "\n".join(
        f"Upload.lean:{m['pos']['line']}:{m['pos']['column']}: {m['data']}"
        for m in messages if m.get("severity") == "error"
    ).strip()


# a simp lemma proved by rfl leaves no trace in the proof term, so the extractor misses it
# simp reports a lemma by name, and a definition it unfolded as "unfold <name>"
SIMP_TRACE = re.compile(r"\[Meta\.Tactic\.simp\.rewrite\]\s+(?:unfold\s+)?([A-Za-z_][\w.'\u2019]*)")


# the lemmas simp used, paired with the declaration that used them
# the trace names the lemma, the position says who used it
def simp_edges(messages, nodes):
    owned = {n["name"] for n in nodes}
    by_suffix = {}
    for name in owned:
        parts = name.split(".")
        for i in range(len(parts)):
            by_suffix.setdefault(".".join(parts[i:]), []).append(name)
    # smallest range first, so the innermost declaration wins
    ranges = sorted(
        ((n["lineStart"], n["lineEnd"] or n["lineStart"], n["name"]) for n in nodes if n["lineStart"]),
        key=lambda r: r[1] - r[0]
    )

    edges = set()
    for message in messages:
        at = message.get("pos", {}).get("line")
        user = next((name for lo, hi, name in ranges if lo <= at <= hi), None)
        if user is None:
            continue
        for lemma in SIMP_TRACE.findall(message.get("data", "")): # one message can hold several
            candidates = by_suffix.get(lemma, [])
            if len(candidates) > 1 and user: # ambiguous suffix: the nearest namespace wins
                candidates = sorted(candidates, key=lambda c: -shared_prefix(c, user))
            full = candidates[0] if candidates else None
            if full and full != user: # only the proof's own, and no self loops
                edges.add((user, full))
    return edges


# how many leading dotted components two names share, for picking between same-suffix candidates
def shared_prefix(a, b):
    a, b = a.split("."), b.split(".")
    n = 0
    while n < min(len(a), len(b)) and a[n] == b[n]:
        n += 1
    return n


# write the proof, compile it, run the extractor, return graph json
def compile_and_extract(file, version, simp_trace=False):
    env_dir = COMPILE_ENV / version # lean version dir
    upload = env_dir / "Upload.lean"
    out = env_dir / ".upload.json"
    olean = env_dir / ".lake" / "build" / "lib" / "lean" / "Upload.olean"
    upload.write_text(file) # write the uploaded proof into Upload.lean
    olean.parent.mkdir(parents=True, exist_ok=True) # lake makes this, but not on a fresh box

    flags = ["-D", "maxHeartbeats=0"]
    if simp_trace:
        flags += ["-D", "trace.Meta.Tactic.simp.rewrite=true"]
    build = run(["lake", "env", "lean", "--json", *flags, "-o", str(olean), "Upload.lean"], env_dir) # compile the proof
    messages = parse_messages(build)
    if build.returncode != 0:
        raise CompileError(error_text(messages) or clean_output(build))

    extract = run(["lake", "env", "lean", "--run", str(EXTRACTOR), "-o", str(out), "Upload"], env_dir) # extract info from .olean files
    if extract.returncode != 0:
        raise CompileError(clean_output(extract))

    graph = json.loads(out.read_text()) # parse json the extractor wrote

    known = {(e["from"], e["to"]) for e in graph["edges"]}
    for user, lemma in sorted(simp_edges(messages, graph["nodes"]) - known): # edges the term missed
        graph["edges"].append({"from": user, "to": lemma})
    return graph
