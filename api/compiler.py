import json
import os
import re
import shlex
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent # repo root
COMPILE_ENV = ROOT / "compile-env"
EXTRACTOR = COMPILE_ENV / "extract.lean"
ELAN_BIN = str(Path.home() / ".elan" / "bin")
MODULE = "Upload" # the uploaded proof is compiled as this module


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

    command = "ulimit -s unlimited; exec " + shlex.join(args)

    return subprocess.run( # run to completion, however long it takes
        ["bash", "-c", command], cwd=cwd, env=env, text=True,
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

# typeclass resolution finds an instance by the shape of the goal, and the elaborator can apply
# it and then erase it: a coercion becomes the projection it unfolds to, so the proof term never
# names the instance.  the trace names every step the search applied, and the tick marks the
# ones that worked -- the file's own instance sits in the middle of a chain of core ones
SYNTH_APPLY = re.compile(r"\[Meta\.synthInstance\.apply\] \u2705\ufe0f? apply @?([A-Za-z_][\w.'\u2019]*)")


def traced_names(data):
    return SIMP_TRACE.findall(data) + SYNTH_APPLY.findall(data)


# the declarations the tactics used, paired with the declaration that used them
# the trace names them, the position says who used them
def simp_edges(messages, nodes):
    owned = {n["name"] for n in nodes}
    by_suffix = {}
    for name in owned:
        parts = name.split(".")
        for i in range(len(parts)):
            by_suffix.setdefault(".".join(parts[i:]), []).append(name)
    # which declaration owns each line, widest first so the innermost one wins the slot. ownership
    # is settled once here rather than searched through the ranges again for every message
    owner_of_line = {}
    for start, end, name in sorted(
        ((n["lineStart"], n["lineEnd"] or n["lineStart"], n["name"]) for n in nodes if n["lineStart"]),
        key=lambda r: r[1] - r[0], reverse=True
    ):
        for line in range(start, end + 1):
            owner_of_line[line] = name

    edges = set()
    for message in messages:
        user = owner_of_line.get(message.get("pos", {}).get("line"))
        if user is None:
            continue
        for lemma in traced_names(message.get("data", "")): # one message can hold several
            candidates = by_suffix.get(lemma, [])
            if len(candidates) > 1 and user: # ambiguous suffix: the nearest namespace wins
                candidates = sorted(candidates, key=lambda c: -shared_prefix(c, user))
            full = candidates[0] if candidates else None
            if full and full != user: # only the proof's own, and no self loops
                edges.add((user, full))
    return edges


# lean writes the language server's reference table when asked for an ilean: every identifier
# it resolved, as a full name and the module it came from, with the declaration that wrote it.
# these are the file's dependencies on the page, which the proof term does not always keep:
# a lemma handed to simp that never fires, dot notation, a name used only in a statement
PRIVATE = re.compile(rf"^_private\.{MODULE}\.\d+\.")


def ilean_edges(path, nodes):
    if not path.exists():
        return set()
    data = json.loads(path.read_text())
    owned = {n["name"] for n in nodes}
    plain = lambda n: PRIVATE.sub("", n or "") # a private declaration is mangled here, not in the environment
    edges = set()
    for key, entry in data.get("references", {}).items():
        const = json.loads(key).get("c")
        if not const or const.get("m") != MODULE:
            continue
        to = plain(const["n"])
        if to not in owned:
            continue
        for usage in entry.get("usages", []):
            user = plain(usage[4]) if len(usage) > 4 else None
            if user in owned and user != to:
                edges.add((user, to))
    return edges


# one command can write several declarations on the same lines: `@[to_additive]` derives an
# additive twin, `notation` adds a macro rule, `deriving` an instance.  lean knows each of those
# comes from the other, and the file cannot hold one without the other, so record it as a
# dependency both ways -- otherwise the twin looks like a second conclusion of the proof
def kin_edges(nodes):
    spans = [(n["lineStart"], n["lineEnd"] or n["lineStart"], n["name"]) for n in nodes if n["lineStart"]]
    edges = set()
    for start, end, name in spans:
        for other_start, other_end, other in spans:
            if other == name:
                continue
            if other_start <= start and end <= other_end:
                edges.add((name, other))
                edges.add((other, name))
    # `elab_rules` and `macro_rules` land in a declaration lean names after the syntax it
    # implements, and the two can sit on different lines, so read the name it embeds
    flat = {n["name"].replace(".", "_"): n["name"] for n in nodes}
    for node in nodes:
        aux = node["name"]
        if "_aux_" not in aux:
            continue
        written = [full for key, full in flat.items() if full != aux and key in aux]
        if written:
            longest = max(written, key=len)
            edges.add((aux, longest))
            edges.add((longest, aux))
    return edges


# how many leading dotted components two names share, for picking between same-suffix candidates
def shared_prefix(a, b):
    a, b = a.split("."), b.split(".")
    n = 0
    while n < min(len(a), len(b)) and a[n] == b[n]:
        n += 1
    return n


# write the proof, compile it, run the extractor, return graph json
def compile_and_extract(file, version):
    env_dir = COMPILE_ENV / version # lean version dir
    upload = env_dir / "Upload.lean"
    out = env_dir / ".upload.json"
    olean = env_dir / ".lake" / "build" / "lib" / "lean" / "Upload.olean"
    upload.write_text(file) # write the uploaded proof into Upload.lean
    olean.parent.mkdir(parents=True, exist_ok=True) # lake makes this, but not on a fresh box

    refs = env_dir / ".upload.ilean"
    # weak. so an option an older toolchain does not know is skipped instead of failing the build
    flags = ["-D", "maxHeartbeats=0", "-D", "maxErrors=0",
             "-D", "weak.trace.Meta.Tactic.simp.rewrite=true",
             "-D", "weak.trace.Meta.synthInstance.apply=true"]
    build = run(["lake", "env", "lean", "--json", *flags, "-i", str(refs), "-o", str(olean), "Upload.lean"], env_dir) # compile the proof, and write the reference table
    messages = parse_messages(build)
    if build.returncode != 0:
        raise CompileError(error_text(messages) or clean_output(build) or f"lean exited with code {build.returncode} and no output")

    extract = run(["lake", "env", "lean", "--run", str(EXTRACTOR), "-o", str(out), "Upload"], env_dir) # extract info from .olean files
    if extract.returncode != 0:
        raise CompileError(clean_output(extract)
                           or f"extractor exited with code {extract.returncode} and no output")

    graph = json.loads(out.read_text()) # parse json the extractor wrote

    known = {(e["from"], e["to"]) for e in graph["edges"]}
    found = (simp_edges(messages, graph["nodes"]) | ilean_edges(refs, graph["nodes"])
             | kin_edges(graph["nodes"])) - known
    for user, lemma in sorted(found): # edges the term did not keep
        graph["edges"].append({"from": user, "to": lemma})
    return graph
