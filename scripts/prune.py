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
    instances = {
        r.id for r in conn.execute(
            text("SELECT id FROM declaration WHERE proof_id = :p AND is_instance"), {"p": proof_id})
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

# a command can produce more than one declaration on the same lines: `notation` adds a macro
# rule, `deriving` an instance, `@[to_additive]` an additive twin.  only the widest span is a
# thing the file writes -- the rest live or die with it, so point the container at them and let
# reachability carry what they use
spans = [(st, en or st, i) for i, (nm, gen, st, en) in decls.items() if st]
owner_of = {}
for st, en, i in spans: # declarations sharing a span: the one the file wrote owns the others
    twins = [j for a, b, j in spans if (a, b) == (st, en)]
    owner_of[(st, en)] = min(twins, key=lambda j: (decls[j][1], j))
inside = {}
for st, en, i in spans:
    same = owner_of[(st, en)]
    if same != i:
        inside[i] = same
        continue
    wider = [(a, b, j) for a, b, j in spans
             if (a, b) != (st, en) and a <= st and en <= b]
    if wider:
        inside[i] = owner_of[min(wider, key=lambda h: h[1] - h[0])[:2]]
for i, holder in inside.items():
    uses[holder].add(i)
# the theorem is the one root that matters, but an instance has to be kept even when nothing
# points at it: the elaborator applies a coercion or a `deriving` handler and then erases the
# instance from the term, so the file needs it again on the way back in while the graph, which
# reads the finished term, cannot see that
# a `notation`, `elab_rules` or `deriving` command puts its work in a declaration lean generates.
# the pruner never deletes a generated declaration, and one whose lines are its own -- not inside
# some other declaration's span -- therefore always survives, so whatever it uses has to stay
written = [(st, en or st) for nm, gen, st, en in decls.values() if st and not gen]
standalone = [
    i for i, (nm, gen, st, en) in decls.items()
    if gen and st and not any(a <= st and (en or st) <= b for a, b in written)
]
reachable, stack = set(), [by_name[root], *instances, *standalone]
while stack:
    n = stack.pop()
    if n in reachable:
        continue
    reachable.add(n)
    stack.extend(uses[n] - reachable)

MODIFIER = re.compile(r"^\s*(omit|set_option|open|attribute|include|variable|local\s+\w+)\b.*\bin\s*$")
MODIFIER_HEAD = re.compile(r"^\s*(omit|set_option|open|attribute|include|variable|local\s+\w+)\b")
ENDS_IN = re.compile(r"\bin\s*$")
NAMESPACE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|public|meta)\s+)*namespace ")
SECTION = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|public|meta)\s+)*section\b")
MUTUAL = re.compile(r"^mutual\b")
END = re.compile(r"^end(\s+[A-Za-z_].*)?$")
NAMESPACE_NAME = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|public|meta)\s+)*namespace\s+(\S+)")
SECTION_NAME = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|public|meta)\s+)*section\s+(\S+)\s*$")


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
# a notation command declares `termX` and a macro rule, neither of which it writes down
NOTATION = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?"
                      r"(?:(?:scoped(?:\s*\[[^\]]*\])?|local|protected|private)\s+)*"
                      r"(?:notation|macro|macro_rules|syntax|infixl|infixr|infix|prefix|postfix|elab)\b")
LITERAL = re.compile(r'"([^"]+)"')
# `instance : Coe A B where ...` is named by lean, not by the file, so the name is not on the page
ANONYMOUS = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?"
                       r"(?:(?:scoped|local|private|protected|noncomputable)\s+)*"
                       r"(?:instance|example)\b")
DERIVING = re.compile(r"^\s*deriving\s+instance\b")
NOT_NAME_CHAR = r"(?![A-Za-z0-9_'!?])"
FIRST_KEYWORD = re.compile(rf"(?:^|\s)({KEYWORD})\s")
ATTRIBUTE = re.compile(r"^\s*@\[")


def blank_code(src, depths=None):
    out, depth = [], 0
    for line in src:
        if depths is not None:
            depths.append(depth)
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
            elif line.startswith("'\"'", i):
                buf.append("   "); i += 3
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


DEPTH = []
BLANK = blank_code(lines, DEPTH)


def code_window(start):
    return BLANK[start - 1:start + 15]


def comment_only(k):
    return not BLANK[k - 1].strip() and bool(lines[k - 1].strip())


def code_head(start, end):
    # line_start can point at the doc comment above the command, so find the first real line
    for k in range(start, (end or start) + 1):
        if BLANK[k - 1].strip():
            return k
    return start


def command_line(start, end):
    return BLANK[code_head(start, end) - 1]


def declares(start, end, name):
    short = re.escape(name.split(".")[-1])
    head = "\n".join(code_window(code_head(start, end)))
    if re.search(rf"(?:^|\s){KEYWORD}\s+(_root_\.)?(\S+\.)?{short}{NOT_NAME_CHAR}", head, re.M):
        return True
    head = command_line(start, end)
    if DERIVING.match(head):
        return True # `deriving instance Fintype for M` declares instFintypeM, unwritten
    written = ANONYMOUS.match(head)
    return bool(written) and not re.match(r"\s*[A-Za-z_]", head[written.end():])


dead, untrusted = {}, 0
for i, (name, generated, start, end) in decls.items():
    if i in reachable or generated or not start or i in inside:
        continue # a declaration inside another's span goes with it, it is not deletable alone
    if not declares(start, end, name) and not NOTATION.match(command_line(start, end)):
        untrusted += 1
        continue
    span = set(range(start, (end or start) + 1))
    k = start - 1
    while k >= 1:
        head = modifier_head(k)
        if head is not None:
            span.update(range(head, k + 1))
            k = head
        elif not lines[k - 1].strip():
            span.add(k)
        elif comment_only(k):
            j = k
            while j > 1 and DEPTH[j - 1] and comment_only(j):
                j -= 1
            if DEPTH[j - 1] or not comment_only(j):
                break
            span.update(range(j, k + 1))
            k = j
        else:
            break
        k -= 1
    dead[name] = span

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



tokens = {
    name: set(LITERAL.findall(command_line(decls[i][2], decls[i][3])))
    for i, name in ((i, decls[i][0]) for i in decls)
    if name in dead and NOTATION.match(command_line(decls[i][2], decls[i][3]))
}

rescued, drop, clashed, spoken = set(), set(), set(), set()
while True:
    going = {part for n in dead if n not in rescued for part in n.split("\x00")}
    kept_lines = set()
    for name, generated, start, end in decls.values():
        if start and not generated and name not in going:
            kept_lines.update(range(start, (end or start) + 1))
    clash = {n for n, s in dead.items() if n not in rescued and (s & kept_lines)}
    if tokens:
        live = "\n".join(l for i, l in enumerate(BLANK, 1)
                          if i not in set().union(set(), *(sp for n, sp in dead.items() if n not in rescued)))
        clash |= {n for n, lits in tokens.items()
                  if n not in rescued and any(lit in live for lit in lits)}
    if not clash:
        break
    rescued |= clash
    clashed |= clash
    spoken |= {n for n in clash if n in tokens}
    # whatever stays has to keep what it uses, even though the root cannot reach it
    stack = [by_name[part] for n in clash for part in n.split("\x00") if part in by_name]
    need = set()
    while stack:
        d = stack.pop()
        if d in need:
            continue
        need.add(d)
        stack.extend(uses[d] - need)
    wanted = {decls[d][0] for d in need}
    also = {n for n in dead if n not in rescued and any(p in wanted for p in n.split("\x00"))}
    rescued |= also
    clashed |= also
drop = set().union(set(), *(s for n, s in dead.items() if n not in rescued))

if explain:
    for n in sorted(dead):
        print(f"  {'kept, its lines overlap one that stays' if n in clashed else 'dropping'}"
              f" {n.replace(chr(0), ' + ')}")

if clashed:
    print(f"  {len(clashed)} kept because their lines overlap a declaration that stays")

ambient = sum(1 for i in instances if not any(t == i for _, t in edges))
print(f"declarations {len(decls)}  reachable {len(reachable)}  dead {len(dead)}"
      + (f"  ({ambient} instances kept that nothing points at)" if ambient else "")
      + (f"  (skipped {untrusted} whose line range does not match their header)" if untrusted else ""))
# `variable {f : CS n E}` and `attribute [simp] foo` are commands, not declarations, so nothing
# points at them.  when every declaration of that name is gone, the line has to go too
BINDER = re.compile(r"^\s*(?:variable|attribute)\b")
WORD = re.compile(r"[^\W\d][\w.'!?\u2080-\u2089]*")
deleted_names = {part.split(".")[-1] for n in dead if n not in rescued for part in n.split("\x00")}
surviving_names = {nm.split(".")[-1] for nm, _, st, _ in decls.values() if st and st not in drop}
vanished = deleted_names - surviving_names
GROUP = re.compile(r"[\[{(\u2983]([^\]})\u2984]*)[\]})\u2984]")


def mentions(line):
    # `variable {M : Type*} [AddCommMonoid M]` introduces M, it does not refer to a declaration
    # named M.  only what follows a colon inside a binder group is a reference
    bound = set()
    for group in GROUP.findall(line):
        head = group.split(":")[0] if ":" in group else ""
        bound.update(WORD.findall(head))
    return {t.split(".")[-1] for t in WORD.findall(line)} - bound


def command_at(k):
    # a variable command can run over several lines, each continuation indented
    j = k
    while j < len(BLANK) and BLANK[j][:1].isspace() and BLANK[j].strip():
        j += 1
    return range(k, j + 1)


orphaned = set()
for i, line in enumerate(BLANK, 1):
    if i in drop or not BINDER.match(line):
        continue
    span = command_at(i)
    if any(mentions(BLANK[k - 1]) & vanished for k in span):
        orphaned.update(span)
if orphaned:
    print(f"  dropping {len(orphaned)} variable or attribute lines naming something deleted")
    drop |= orphaned

lines = [l for i, l in enumerate(lines, 1) if i not in drop]
print(f"dropped {len(drop):,} lines")

OPEN = re.compile(r"^\s*(?:open|export)\b\s*(?:scoped\s+)?(.*)$")
NAME = re.compile(r"[A-Za-z_][\w.']*")
CONT = re.compile(r"^\s+[A-Za-z_][\w.']*\s*$")
emptied = 0
for _ in range(10):
    scan = blank_code(lines)
    opened_names = set()
    for i, line in enumerate(scan):
        m = OPEN.match(line)
        if m:
            payload = m.group(1)
            if not payload.strip():
                j = i + 1
                while j < len(scan) and CONT.match(scan[j]):
                    payload += " " + scan[j]
                    j += 1
            for tok in NAME.findall(re.sub(r"\bin\b.*$", "", payload.split("--")[0])):
                opened_names.add(tok)
                opened_names.update(tok.split("."))
    stack, kill = [], set()
    empties, occupied_at = [], {}
    for i, line in enumerate(scan, 1):
        if NAMESPACE.match(line):
            if stack:
                stack[-1][2] = True
            parent = next((e[3] for e in reversed(stack) if e[0] == "namespace"), "")
            written = NAMESPACE_NAME.match(line).group(1)
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
                ns = NAMESPACE_NAME.match(scan[opened - 1]).group(1)
                if occupied:
                    occupied_at.setdefault(full, opened)
                else:
                    empties.append((ns, full, opened, i))
            if stack and occupied:
                stack[-1][2] = True
        elif stack and lines[i - 1].strip():
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


def structural_problems(raw):
    src = blank_code(raw)
    problems, stack = [], []
    for i, line in enumerate(src, 1):
        if NAMESPACE.match(line):
            stack.append(("namespace", NAMESPACE_NAME.match(line).group(1), i))
        elif SECTION.match(line):
            named = SECTION_NAME.match(line)
            stack.append(("section", named.group(1) if named else None, i))
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
