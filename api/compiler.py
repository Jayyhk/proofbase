import json
import os
import re
import signal
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent # repo root
COMPILE_ENV = ROOT / "compile-env"
EXTRACTOR = COMPILE_ENV / "extract.lean"
ELAN_BIN = str(Path.home() / ".elan" / "bin")
TIMEOUT = 300 # compile timeout, seconds


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

    proc = subprocess.Popen( # start command
        args, cwd=cwd, env=env, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True
    )
    try:
        out, err = proc.communicate(timeout=TIMEOUT) # finish and collect output, give up after TIMEOUT seconds
    except subprocess.TimeoutExpired: # ran too long, try to kill it
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL) # try to kill whole process group
        except ProcessLookupError:
            pass # nothing to do, already exited
        proc.communicate() # collect whatever's left and let the OS clean up dead process
        raise CompileError(f"compilation timed out after {TIMEOUT // 60} minutes")

    return subprocess.CompletedProcess(args, proc.returncode, out, err) # finished in time


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
SIMP_TRACE = re.compile(r"\[Meta\.Tactic\.simp\.rewrite\]\s+([A-Za-z_][\w.'\u2019]*)")


# the lemmas simp used, paired with the declaration that used them.
# the trace names the lemma, the position tells us who it was for
def simp_edges(messages, nodes):
    owned = {n["name"] for n in nodes}
    # smallest range first, so the innermost declaration wins
    ranges = sorted(
        ((n["lineStart"], n["lineEnd"] or n["lineStart"], n["name"]) for n in nodes if n["lineStart"]),
        key=lambda r: r[1] - r[0]
    )

    edges = set()
    for message in messages:
        lemma = SIMP_TRACE.search(message.get("data", ""))
        if lemma is None or lemma.group(1) not in owned:
            continue # a mathlib lemma, we only graph the proof's own
        at = message.get("pos", {}).get("line")
        user = next((name for lo, hi, name in ranges if lo <= at <= hi), None)
        if user is not None and user != lemma.group(1): # no self loops
            edges.add((user, lemma.group(1)))
    return edges


# write the proof, compile it, run the extractor, return graph json
def compile_and_extract(file, version):
    env_dir = COMPILE_ENV / version # lean version dir
    upload = env_dir / "Upload.lean"
    out = env_dir / ".upload.json"
    olean = env_dir / ".lake" / "build" / "lib" / "lean" / "Upload.olean"
    upload.write_text(file) # write the uploaded proof into Upload.lean
    olean.parent.mkdir(parents=True, exist_ok=True) # lake makes this, but not on a fresh box

    build = run(["lake", "env", "lean", "--json", "-D", "trace.Meta.Tactic.simp.rewrite=true", "-o", str(olean), "Upload.lean"], env_dir) # compile the proof
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
