import collections
import re
import sys
from pathlib import Path

from sqlalchemy import text

from api.db import engine

proof_id = int(sys.argv[1])
path = Path(sys.argv[2])
root = sys.argv[3]

with engine.connect() as conn:
    decls = {
        r.id: (r.name, r.is_generated, r.line_start, r.line_end)
        for r in conn.execute(
            text("SELECT id, name, is_generated, line_start, line_end FROM declaration WHERE proof_id = :p"),
            {"p": proof_id}
        )
    }
    edges = [
        (r.from_id, r.to_id)
        for r in conn.execute(text("SELECT from_id, to_id FROM edge WHERE proof_id = :p"), {"p": proof_id})
    ]
    stored = conn.execute(text("SELECT file FROM proof WHERE id = :p"), {"p": proof_id}).scalar()

if stored is None:
    sys.exit(f"no proof {proof_id}")
if path.read_text() != stored:
    sys.exit(f"{path} is not the file uploaded as proof {proof_id}")
original = stored.splitlines()
lines = list(original)

by_name = {v[0]: k for k, v in decls.items()}
if root not in by_name:
    sys.exit(f"{root} is not among the extracted declarations")

uses = collections.defaultdict(set)
for frm, to in edges:
    uses[frm].add(to)
reachable, stack = set(), [by_name[root]]
while stack:
    n = stack.pop()
    if n in reachable:
        continue
    reachable.add(n)
    stack.extend(uses[n] - reachable)

MODIFIER = re.compile(r"^\s*(omit|set_option|open|attribute|local\s+\w+)\b.*\bin\s*$")
KEYWORD = r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|axiom|opaque|example)"
NOT_NAME_CHAR = r"(?![A-Za-z0-9_'!?])"
FIRST_KEYWORD = re.compile(rf"(?:^|\s)({KEYWORD})\s")
ATTRIBUTE = re.compile(r"^\s*@\[")


def declares(start, name):
    short = re.escape(name.split(".")[-1])
    head = "\n".join(lines[start - 1:start + 15])
    return re.search(rf"(?:^|\s){KEYWORD}\s+(_root_\.)?(\S+\.)?{short}{NOT_NAME_CHAR}", head, re.M) is not None


def is_instance(start):
    for line in lines[start - 1:start + 15]:
        m = FIRST_KEYWORD.search(line)
        if m:
            return m.group(1) == "instance"
    return False


def tagged(start):
    for line in lines[start - 1:start + 15]:
        if ATTRIBUTE.match(line):
            return True
        if FIRST_KEYWORD.search(line):
            break
    k = start
    while k >= 1:
        line = lines[k - 1]
        if ATTRIBUTE.match(line):
            return True
        if k == start:
            k -= 1
            continue
        if MODIFIER.match(line) or line.strip().startswith("--") or not line.strip():
            k -= 1
            continue
        if line.rstrip().endswith("-/"):
            j = k
            while j >= 1 and "/-" not in lines[j - 1]:
                j -= 1
            k = j - 1
            continue
        return False
    return False


dead, untrusted, attributed, instances = {}, 0, 0, 0
for i, (name, generated, start, end) in decls.items():
    if i in reachable or generated or not start:
        continue
    if not declares(start, name):
        untrusted += 1
        continue
    if is_instance(start):
        instances += 1
        continue
    if tagged(start):
        attributed += 1
        continue
    span = set(range(start, end + 1))
    k = start - 1
    while k >= 1:
        line = lines[k - 1]
        if MODIFIER.match(line):
            span.add(k)
        elif line.strip().startswith("--") or not line.strip():
            span.add(k)
        else:
            break
        k -= 1
    dead[name] = span

TOKEN = re.compile(r"[^\W\d][\w.'!?₀-₉]*")
MUTUAL = re.compile(r"^mutual\b")
BARE_END = re.compile(r"^end\s*$")
blocks, b = [], 0
while b < len(lines):
    if MUTUAL.match(lines[b]):
        j = b + 1
        while j < len(lines) and not BARE_END.match(lines[j]):
            j += 1
        if j < len(lines):
            blocks.append((b + 1, j + 1))
        b = j
    b += 1

merged = 0
for m, e in blocks:
    inside = [n for n, s in dead.items() if m < min(s) and max(s) < e]
    members = [d for d in decls.values() if d[2] and m < d[2] < e]
    for n in inside:
        del dead[n]
    if members and len(inside) == len(members):
        dead["\x00".join(inside)] = set(range(m, e + 1))
        merged += 1
if blocks:
    print(f"mutual blocks {len(blocks)}  dropped whole {merged}, kept intact {len(blocks) - merged}")

rescued, drop, rounds = set(), set(), 0
while True:
    rounds += 1
    drop = set().union(set(), *(s for n, s in dead.items() if n not in rescued))
    named = set()
    for i, line in enumerate(lines, 1):
        if i in drop:
            continue
        named.update(part for t in TOKEN.findall(line) for part in t.split("."))
    fresh = {n for n in dead if n not in rescued
             and any(part.split(".")[-1] in named for part in n.split("\x00"))}
    if not fresh:
        break
    rescued |= fresh

print(f"declarations {len(decls)}  reachable {len(reachable)}  dead {len(dead)}  "
      f"rescued by name {len(rescued)} in {rounds} rounds"
      + (f"  kept {attributed} attribute-carrying" if attributed else "")
      + (f", {instances} instances" if instances else "")
      + (f"  (skipped {untrusted} whose line range does not match their header)" if untrusted else ""))
lines = [l for i, l in enumerate(lines, 1) if i not in drop]
print(f"dropped {len(drop):,} lines")

NAMESPACE = re.compile(r"^namespace ")
SECTION = re.compile(r"^(noncomputable\s+)?section\b")
END = re.compile(r"^end(\s+[A-Za-z_].*)?$")
OPEN = re.compile(r"^\s*(?:open|export)\b\s*(?:scoped\s+)?(.*)$") # \b not \s+: a bare `open` continues on the next lines
NAME = re.compile(r"[A-Za-z_][\w.']*")
CONT = re.compile(r"^\s+[A-Za-z_][\w.']*\s*$") # a namespace on its own line after a bare `open`
emptied = 0
for _ in range(10):
    opened_names = set()
    for i, line in enumerate(lines):
        m = OPEN.match(line)
        if m:
            payload = m.group(1)
            # `open` with nothing after it continues on the following lines, one
            # namespace per line.  without this the names are never collected and the
            # namespace looks unopened, so an emptied one gets deleted out from under
            # a live `open`, leaving `unknown namespace`.
            if not payload.strip():
                j = i + 1
                while j < len(lines) and CONT.match(lines[j]):
                    payload += " " + lines[j]
                    j += 1
            for tok in NAME.findall(re.sub(r"\bin\b.*$", "", payload.split("--")[0])):
                opened_names.add(tok)
                opened_names.update(tok.split("."))
    stack, kill, comment = [], set(), 0
    empties, occupied_at = [], {}
    for i, line in enumerate(lines, 1):
        inside = comment > 0
        comment = max(0, comment + line.count("/-") - line.count("-/"))
        if inside:
            continue
        if NAMESPACE.match(line):
            stack.append(["namespace", i, False])
        elif SECTION.match(line):
            stack.append(["section", i, False])
        elif MUTUAL.match(line):
            stack.append(["mutual", i, False])
        elif END.match(line):
            if not stack:
                print(f"  warning: unmatched end at line {i}")
                continue
            kind, opened, occupied = stack.pop()
            if kind == "namespace":
                ns = lines[opened - 1].split()[1]
                if occupied:
                    occupied_at.setdefault(ns, opened)
                else:
                    empties.append((ns, opened, i))
            if stack and occupied:
                stack[-1][2] = True
        elif stack and line.strip():
            stack[-1][2] = True
    for ns, opened, closed in empties:
        if occupied_at.get(ns, opened) < opened:
            kill |= {opened, closed}
        elif ns not in opened_names and ns.split(".")[-1] not in opened_names:
            kill |= {opened, closed}
    if stack:
        print(f"  warning: {len(stack)} scopes left open")
    if not kill:
        break
    emptied += len(kill) // 2
    lines = [l for i, l in enumerate(lines, 1) if i not in kill]

out, blanks, collapsed = [], 0, 0
for line in lines:
    if line.strip():
        blanks = 0
    else:
        blanks += 1
        if blanks > 1:
            collapsed += 1
            continue
    out.append(line)
print(f"also: {emptied} empty namespaces, {collapsed} blank lines")

i = 0
for line in out:
    while i < len(original) and original[i] != line:
        i += 1
    if i == len(original):
        sys.exit(f"refusing to write: line was rewritten, not deleted: {line!r}")
    i += 1

path.write_text("\n".join(out) + "\n")
removed = len(original) - len(out)
print(f"{len(original):,} -> {len(out):,} lines ({100 * removed / len(original):.1f}% removed)")
