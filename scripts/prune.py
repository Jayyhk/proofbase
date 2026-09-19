import collections
import re
import sys
from pathlib import Path

from sqlalchemy import text

from api.db import engine

args = [a for a in sys.argv[1:] if not a.startswith("--")]
explain = "--explain" in sys.argv
proof_id = int(args[0])
path = Path(args[1])
root = args[2] if len(args) > 2 else None

with engine.connect() as conn:
    decls = {
        r.id: (r.name, r.is_generated, r.line_start, r.line_end)
        for r in conn.execute(
            text("SELECT id, name, is_generated, line_start, line_end FROM declaration WHERE proof_id = :p"),
            {"p": proof_id}
        )
    }
    magic = {
        r.id: (r.is_instance, r.is_simp)
        for r in conn.execute(
            text("SELECT id, is_instance, is_simp FROM declaration WHERE proof_id = :p"),
            {"p": proof_id}
        )
    }
    edges = [
        (r.from_id, r.to_id)
        for r in conn.execute(text("SELECT from_id, to_id FROM edge WHERE proof_id = :p"), {"p": proof_id})
    ]
    row = conn.execute(
        text("SELECT file, simp_trace FROM proof WHERE id = :p"), {"p": proof_id}
    ).mappings().first()
    stored = row["file"] if row else None
    traced = bool(row["simp_trace"]) if row else False

if stored is None:
    sys.exit(f"no proof {proof_id}")
if path.read_text() != stored:
    sys.exit(f"{path} is not the file uploaded as proof {proof_id}")
original = stored.splitlines()
lines = list(original)

by_name = {v[0]: k for k, v in decls.items()}
if root is None:
    m = re.fullmatch(r"Erdos(\d+)", path.stem)
    guess = f"Erdos{m.group(1)}.erdos_{m.group(1)}" if m else None
    if guess not in by_name:
        sys.exit(f"pass the root theorem: cannot infer one from {path.name}"
                 + (f" (tried {guess})" if guess else ""))
    root = guess
    print(f"root: {root} (inferred from the file name)")
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

MODIFIER = re.compile(r"^\s*(omit|set_option|open|attribute|include|variable|local\s+\w+)\b.*\bin\s*$")
MODIFIER_HEAD = re.compile(r"^\s*(omit|set_option|open|attribute|include|variable|local\s+\w+)\b")
ENDS_IN = re.compile(r"\bin\s*$")
NAMESPACE = re.compile(r"^namespace ")
SECTION = re.compile(r"^(noncomputable\s+)?section\b")
MUTUAL = re.compile(r"^mutual\b")
END = re.compile(r"^end(\s+[A-Za-z_].*)?$")


def modifier_head(k):
    if MODIFIER.match(lines[k - 1]):
        return k
    if not ENDS_IN.search(lines[k - 1]):
        return None
    j = k
    while j > 1 and lines[j - 1][:1].isspace() and lines[j - 1].strip():
        j -= 1
    return j if MODIFIER_HEAD.match(lines[j - 1]) else None


KEYWORD = r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|axiom|opaque|example)"
NOT_NAME_CHAR = r"(?![A-Za-z0-9_'!?])"
FIRST_KEYWORD = re.compile(rf"(?:^|\s)({KEYWORD})\s")
ATTRIBUTE = re.compile(r"^\s*@\[")


def blank_code(src):
    out, depth = [], 0
    for line in src:
        buf, i, n = [], 0, len(line)
        while i < n:
            if depth:
                if line.startswith("/-", i):
                    depth += 1; buf.append("  "); i += 2
                elif line.startswith("-/", i):
                    depth -= 1; buf.append("  "); i += 2
                else:
                    buf.append(" "); i += 1
            elif line.startswith("/-", i):
                depth = 1; buf.append("  "); i += 2
            elif line.startswith("--", i):
                buf.append(" " * (n - i)); i = n
            elif line[i] == '"':
                j = i + 1
                while j < n and line[j] != '"':
                    j += 2 if line[j] == "\\" else 1
                j = min(j + 1, n)
                buf.append('"' + " " * max(0, j - i - 2) + ('"' if j - i >= 2 else "")); i = j
            else:
                buf.append(line[i]); i += 1
        out.append("".join(buf))
    return out


BLANK = blank_code(lines)


def code_window(start):
    return BLANK[start - 1:start + 15]


def declares(start, name):
    short = re.escape(name.split(".")[-1])
    head = "\n".join(code_window(start))
    return re.search(rf"(?:^|\s){KEYWORD}\s+(_root_\.)?(\S+\.)?{short}{NOT_NAME_CHAR}", head, re.M) is not None


def is_instance(start):
    for line in code_window(start):
        m = FIRST_KEYWORD.search(line)
        if m:
            return m.group(1) == "instance"
    return False


def tagged(start):
    for line in code_window(start):
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
        head = modifier_head(k)
        if head is not None:
            k = head - 1
            continue
        if line.strip().startswith("--") or not line.strip():
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
unused_magic = []
for i, (name, generated, start, end) in decls.items():
    if i in reachable or generated or not start:
        continue
    is_inst, is_simp = magic.get(i, (False, False))
    if is_inst or is_instance(start):
        instances += 1
        unused_magic.append((name, "instance"))
        continue
    if is_simp or tagged(start):
        attributed += 1
        unused_magic.append((name, "simp lemma" if is_simp else "attribute"))
        continue
    if not declares(start, name):
        untrusted += 1
        continue
    span = set(range(start, end + 1))
    k = start - 1
    while k >= 1:
        line = lines[k - 1]
        head = modifier_head(k)
        if head is not None:
            span.update(range(head, k + 1))
            k = head
        elif line.strip().startswith("--") or not line.strip():
            span.add(k)
        else:
            break
        k -= 1
    dead[name] = span

TOKEN = re.compile(r"[^\W\d][\w.'!?₀-₉]*")
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


def namespace_by_line(src):
    out, stack, comment = [], [], 0
    for line in src:
        inside = comment > 0
        comment = max(0, comment + line.count("/-") - line.count("-/"))
        out.append(".".join(stack))
        if inside:
            continue
        if NAMESPACE_DECL.match(line):
            stack.extend(line.split()[1].split("."))
        elif END_NAMED.match(line):
            for _ in line.split()[1].split("."):
                if stack:
                    stack.pop()
    return out


NAMESPACE_DECL = re.compile(r"^namespace\s+(\S+)")
END_NAMED = re.compile(r"^end\s+(\S+)\s*$")
NS_AT = namespace_by_line(BLANK)

by_short = collections.defaultdict(list)
for _, (nm, _, st, _) in decls.items():
    by_short[nm.split(".")[-1]].append(nm)

own_header = {(st, nm.split(".")[-1]) for nm, _, st, _ in decls.values() if st}


def shared_prefix(a, b):
    a, b = a.split("."), b.split(".")
    n = 0
    while n < min(len(a), len(b)) and a[n] == b[n]:
        n += 1
    return n


rescued, drop, rounds, saved_by = set(), set(), 0, {}
while True:
    rounds += 1
    drop = set().union(set(), *(s for n, s in dead.items() if n not in rescued))
    named = {}
    for i, line in enumerate(BLANK, 1):
        if i in drop:
            continue
        for t in TOKEN.findall(line):
            short = t.split(".")[-1]
            if (i, short) in own_header:
                continue
            candidates = [c for c in by_short.get(short, [])
                          if t.count(".") == 0 or c.endswith("." + t) or c == t]
            if not candidates:
                continue
            best = max(shared_prefix(c, NS_AT[i - 1]) for c in candidates)
            for c in candidates:
                if shared_prefix(c, NS_AT[i - 1]) == best:
                    named.setdefault(c, i)
    fresh = {}
    for n in dead:
        if n in rescued:
            continue
        for part in n.split("\x00"):
            at = named.get(part)
            if at is not None:
                fresh[n] = (part, at)
                break
    if not fresh:
        break
    rescued |= set(fresh)
    saved_by.update(fresh)

if explain:
    for n in sorted(dead):
        if n in rescued:
            part, at = saved_by[n]
            print(f"  kept {part}: named on line {at}: {lines[at - 1].strip()[:90]}")
        else:
            print(f"  dropping {n.replace(chr(0), ' + ')}")

dropped_names = {part for n, s in dead.items() if n not in rescued for part in n.split("\x00")}
kept_lines = set()
for name, generated, start, end in decls.values():
    if start and name not in dropped_names:
        kept_lines.update(range(start, (end or start) + 1))
overlap = drop & kept_lines
if overlap:
    drop -= overlap
    print(f"  kept {len(overlap)} lines where a dead span overlapped a live declaration")

if unused_magic:
    kinds = collections.Counter(k for _, k in unused_magic)
    print("  nothing uses " + ", ".join(f"{n} {k}{'s' if n > 1 else ''}" for k, n in kinds.items())
          + " -- kept because simp and typeclass resolution find them without a name")

if rescued and not traced:
    print(f"  {len(rescued)} kept only because the text still names them; this graph was built "
          f"without simp tracing, so a lemma simp closed by rfl has no edge. re-upload with "
          f"simp_trace to prune those")

print(f"declarations {len(decls)}  reachable {len(reachable)}  dead {len(dead)}  "
      f"rescued by name {len(rescued)} in {rounds} rounds"
      + (f"  kept {attributed} attribute-carrying" if attributed else "")
      + (f", {instances} instances" if instances else "")
      + (f"  (skipped {untrusted} whose line range does not match their header)" if untrusted else ""))
lines = [l for i, l in enumerate(lines, 1) if i not in drop]
print(f"dropped {len(drop):,} lines")

OPEN = re.compile(r"^\s*(?:open|export)\b\s*(?:scoped\s+)?(.*)$")
NAME = re.compile(r"[A-Za-z_][\w.']*")
CONT = re.compile(r"^\s+[A-Za-z_][\w.']*\s*$")
emptied = 0
for _ in range(10):
    opened_names = set()
    for i, line in enumerate(lines):
        m = OPEN.match(line)
        if m:
            payload = m.group(1)
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
            if stack:
                stack[-1][2] = True
            parent = next((e[3] for e in reversed(stack) if e[0] == "namespace"), "")
            written = line.split()[1]
            stack.append(["namespace", i, False, f"{parent}.{written}" if parent else written])
        elif SECTION.match(line):
            stack.append(["section", i, False, None])
        elif MUTUAL.match(line):
            stack.append(["mutual", i, False, None])
        elif END.match(line):
            if not stack:
                print(f"  warning: unmatched end at line {i}")
                continue
            kind, opened, occupied, full = stack.pop()
            if kind == "namespace":
                ns = lines[opened - 1].split()[1]
                if occupied:
                    occupied_at.setdefault(full, opened)
                else:
                    empties.append((ns, full, opened, i))
            if stack and occupied:
                stack[-1][2] = True
        elif stack and line.strip():
            stack[-1][2] = True
    for ns, full, opened, closed in empties:
        if occupied_at.get(full, opened) < opened:
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


def modifier_at(src, k):
    line = src[k - 1]
    if MODIFIER.match(line):
        return True
    if not ENDS_IN.search(line):
        return False
    j = k
    while j > 1 and src[j - 1][:1].isspace() and src[j - 1].strip():
        j -= 1
    return MODIFIER_HEAD.match(src[j - 1]) is not None


def structural_problems(src):
    problems, stack, comment = [], [], 0
    for i, line in enumerate(src, 1):
        inside = comment > 0
        comment = max(0, comment + line.count("/-") - line.count("-/"))
        if inside:
            continue
        if NAMESPACE.match(line):
            stack.append(("namespace", line.split()[1], i))
        elif SECTION.match(line):
            parts = line.split()
            stack.append(("section", parts[1] if len(parts) > 1 else None, i))
        elif MUTUAL.match(line):
            stack.append(("mutual", None, i))
        elif END.match(line):
            named = line.split()[1] if len(line.split()) > 1 else None
            if not stack:
                problems.append(f"line {i}: `end` with no open scope")
                continue
            kind, name, opened = stack.pop()
            if kind == "namespace" and named != name:
                problems.append(f"line {i}: `end {named or ''}`".rstrip()
                                + f" closes `namespace {name}` from line {opened}")
            elif kind != "namespace" and named is not None and named != name:
                problems.append(f"line {i}: `end {named}` closes the {kind} opened at line {opened}")
        elif modifier_at(src, i):
            j = i + 1
            while j <= len(src) and (not src[j - 1].strip() or src[j - 1].lstrip().startswith("--")):
                j += 1
            if j > len(src) or END.match(src[j - 1]):
                problems.append(f"line {i}: `{line.strip()[:40]}` modifies nothing")
    for kind, name, opened in stack:
        problems.append(f"line {opened}: {kind} {name or ''}".rstrip() + " is never closed")
    return problems


problems = structural_problems(out)
if problems:
    print(f"refusing to write: pruning left {len(problems)} structural problems")
    for p in problems[:20]:
        print(f"  {p}")
    sys.exit(1)

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
