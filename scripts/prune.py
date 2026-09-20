import collections
import os
import re
import subprocess
import sys
from pathlib import Path

from sqlalchemy import text

from api.db import engine

args = [a for a in sys.argv[1:] if not a.startswith("--")]
explain = "--explain" in sys.argv
verify = "--verify" in sys.argv
proof_id = int(args[0])
path = Path(args[1])
root = args[2] if len(args) > 2 else None
forced = set(os.environ.get("PRUNE_FORCED", "").split())

with engine.connect() as conn:
    version = conn.execute(text("SELECT lean_version FROM proof WHERE id = :p"), {"p": proof_id}).scalar()
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
if open(path, newline="").read() != stored:
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

spans = [(st, en or st, i) for i, (nm, gen, st, en) in decls.items() if st]
owner_of = {}
for st, en, i in spans:
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

written = [(st, en or st) for nm, gen, st, en in decls.values() if st and not gen]
standalone = [
    i for i, (nm, gen, st, en) in decls.items()
    if gen and st and not any(a <= st and (en or st) <= b for a, b in written)
]
reachable, stack = set(), [by_name[root], *standalone]
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

KEYWORD = (r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque"
           r"|example|alias|initialize|builtin_initialize|irreducible_def|unif_hint|lrat_proof"
           r"|simproc_decl|simproc|dsimproc_decl|dsimproc|coinductive|mk_iff_of_inductive_prop"
           r"|proof_wanted|def_wanted|theorem_wanted|instance_wanted"
           r"|register_builtin_option|register_option)")

NOTATION = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?"
                      r"(?:(?:scoped(?:\s*\[[^\]]*\])?|local|protected|private)\s+)*"
                      r"(?:notation3|notation|macro_rules|macro|syntax|infixl|infixr|infix|prefix|postfix"
                      r"|elab_rules|elab|declare_syntax_cat|binder_predicate)\b")
LITERAL = re.compile(r'"([^"]+)"')
BINDER = re.compile(r"^\s*(?:#[A-Za-z_][\w?!]*"
                    r"|variable|attribute|export|add_decl_doc|seal|unseal|recall"
                    r"|assert_not_exists|assert_no_sorry|extend_docs|library_note|deprecate"
                    r"|initialize_simps_projections\??|add_aesop_rules|erase_aesop_rules"
                    r"|grind_pattern|grind_annotated|norm_cast_add_elim|deprecated_syntax"
                    r"|to_dual_insert_cast_fun|to_dual_insert_cast|to_dual_name_hint"
                    r"|to_additive_name_hint|insert_to_additive_translation|recommended_spelling)\b")
WORD_TOKEN = re.compile(r"[^\W\d][\w.'!?\u2080-\u2089]*")
CATEGORY = re.compile(r"^\s*declare_syntax_cat\s+(\S+)")
CHAR_LITERAL = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\])'")
RAW_STRING = re.compile(r'r(#*)"')
IDENT_CHAR = re.compile(r"[A-Za-z0-9_]")

ANONYMOUS = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?"
                       r"(?:(?:scoped|local|private|protected|noncomputable)\s+)*"
                       r"(?:instance|example)\b")
DERIVING = re.compile(r"^\s*deriving\s+instance\b")
NOT_NAME_CHAR = r"(?![A-Za-z0-9_'!?])"


def blank_code(src, depths=None):
    out, depth, stack = [], 0, []
    for line in src:
        if depths is not None:
            depths.append(depth)
        buf, i, n = [], 0, len(line)
        while i < n:
            here = stack[-1] if stack else None
            if depth:
                if line.startswith("/-", i):
                    depth += 1; buf.append("  "); i += 2
                elif line.startswith("-/", i):
                    depth -= 1; buf.append("  "); i += 2
                else:
                    buf.append(" "); i += 1
            elif here and here[0] == "string":
                _, hashes, interp = here
                closing = '"' + "#" * hashes if hashes >= 0 else '"'
                if hashes < 0 and line[i] == "\\" and i + 1 < n:
                    buf.append("  "); i += 2
                elif interp and line[i] == "{":
                    stack.append(["code", 0]); buf.append("{"); i += 1
                elif line.startswith(closing, i):
                    stack.pop(); buf.append(closing); i += len(closing)
                else:
                    buf.append(" "); i += 1
            elif here and here[0] == "code" and line[i] in "{}":
                if line[i] == "{":
                    here[1] += 1
                elif here[1]:
                    here[1] -= 1
                else:
                    stack.pop()
                buf.append(line[i]); i += 1
            elif line.startswith("/-", i):
                depth = 1; buf.append("  "); i += 2
            elif line.startswith("--", i):
                buf.append(" " * (n - i)); i = n
            elif line[i] == "\u00ab":
                close = line.find("\u00bb", i)
                close = n if close < 0 else close + 1
                buf.append(line[i:close]); i = close
            elif line[i] == "'" and CHAR_LITERAL.match(line, i):
                width = CHAR_LITERAL.match(line, i).end() - i
                buf.append(" " * width); i += width
            elif line[i] == '"':
                interp = line[i - 1:i] == "!" and IDENT_CHAR.match(line[i - 2:i - 1] or " ") is not None
                stack.append(["string", -1, interp]); buf.append('"'); i += 1
            elif line[i] == "r" and not IDENT_CHAR.match(line[i - 1:i] or " ") and RAW_STRING.match(line, i):
                opener = RAW_STRING.match(line, i)
                stack.append(["string", len(opener.group(1)), False])
                buf.append(" " * (opener.end() - i - 1) + '"'); i = opener.end()
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
    for k in range(start, (end or start) + 1):
        if BLANK[k - 1].strip():
            return k
    return start

def command_line(start, end):
    return BLANK[code_head(start, end) - 1]

def declares(start, end, name):
    short = re.escape(name.split(".")[-1])
    head = "\n".join(code_window(code_head(start, end)))
    if re.search(rf"(?:^|\s){KEYWORD}\s+(_root_\.)?(\S+\.)?\u00ab?{short}\u00bb?{NOT_NAME_CHAR}", head, re.M):
        return True
    head = command_line(start, end)
    if DERIVING.match(head):
        return True
    written = ANONYMOUS.match(head)
    return bool(written) and not re.match(r"\s*[A-Za-z_]", head[written.end():])

dead, untrusted = {}, 0
for i, (name, generated, start, end) in decls.items():
    if name in forced:
        continue
    if i in reachable or generated or not start or i in inside:
        continue
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
    members_dead = [n for n, s in dead.items() if m < min(s) and max(s) < e]
    members = [d for d in decls.values() if d[2] and m < d[2] < e]
    for n in members_dead:
        del dead[n]
    if members and len(members_dead) == len(members):
        dead["\x00".join(members_dead)] = set(range(m, e + 1))
        merged += 1
if blocks:
    print(f"mutual blocks {len(blocks)}  dropped whole {merged}, kept intact {len(blocks) - merged}")

def spelled(start, end):
    written = lines[code_head(start, end) - 1]
    named = CATEGORY.match(written)
    return set(LITERAL.findall(written)) | ({named.group(1)} if named else set())


tokens = {
    name: spelled(decls[i][2], decls[i][3])
    for i, name in ((i, decls[i][0]) for i in decls)
    if name in dead and NOTATION.match(command_line(decls[i][2], decls[i][3]))
}

rescued, drop, clashed, spoken = set(), set(), set(), set()
while True:
    going = {part for n in dead if n not in rescued for part in n.split("\x00")}
    kept_lines = set()
    for i, (name, generated, start, end) in decls.items():
        if not start or generated:
            continue
        holder = i
        while holder in inside:
            holder = inside[holder]
        leaving = name in going or (i not in reachable and decls[holder][0] in going)
        if leaving:
            continue
        kept_lines.update(range(start, (end or start) + 1))
    clash = {n for n, s in dead.items() if n not in rescued and (s & kept_lines)}
    if tokens:
        leaving = set().union(set(), *(sp for n, sp in dead.items() if n not in rescued))
        live = "\n".join(l for i, l in enumerate(lines, 1) if i not in leaving)
        clash |= {n for n, lits in tokens.items()
                  if n not in rescued and any(lit in live for lit in lits)}
    leaving_now = set().union(set(), *(sp for n, sp in dead.items() if n not in rescued))
    surviving = set(WORD_TOKEN.findall(
        "\n".join(l for i, l in enumerate(BLANK, 1) if i not in leaving_now)))
    clash |= {n for n in dead if n not in rescued
              and any(part in surviving for part in n.split("\x00"))}
    if not clash:
        break
    rescued |= clash
    clashed |= clash
    spoken |= {n for n in clash if n in tokens}

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

print(f"declarations {len(decls)}  reachable {len(reachable)}  dead {len(dead)}"
      + (f"  (skipped {untrusted} whose line range does not match their header)" if untrusted else ""))

WORD = re.compile(r"[^\W\d][\w.'!?\u2080-\u2089]*")
deleted_names = {part.split(".")[-1] for n in dead if n not in rescued for part in n.split("\x00")}
surviving_names = {nm.split(".")[-1] for nm, _, st, _ in decls.values() if st and st not in drop}
vanished = deleted_names - surviving_names
GROUP = re.compile(r"[\[{(\u2983]([^\]})\u2984]*)[\]})\u2984]")


def mentions(line):
    bound = set()
    for group in GROUP.findall(line):
        head = group.split(":")[0] if ":" in group else ""
        bound.update(WORD.findall(head))
    return {t.split(".")[-1] for t in WORD.findall(line)} - bound

def command_at(k):
    j = k
    while j < len(BLANK) and BLANK[j][:1].isspace() and BLANK[j].strip():
        j += 1
    return range(k, j + 1)

EXAMPLE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*example\b")

orphaned = set()
for i, line in enumerate(BLANK, 1):
    if i not in drop and EXAMPLE.match(line):
        orphaned.update(command_at(i))
    if i in drop or not BINDER.match(line):
        continue
    span = command_at(i)
    if any(mentions(BLANK[k - 1]) & vanished for k in span):
        orphaned.update(span)
if orphaned:
    print(f"  dropping {len(orphaned)} lines of examples and commands that name something deleted")
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

ending = "\r\n" if "\r\n" in stored else "\n"
path.write_text(ending.join(out) + ending, newline="")
removed = len(original) - len(out)
print(f"{len(original):,} -> {len(out):,} lines ({100 * removed / len(original):.1f}% removed)")

WANTED = re.compile(r"[Uu]nknown (?:identifier|constant) `([^`]+)`")

if verify:
    from api.compiler import COMPILE_ENV, run
    env_dir = COMPILE_ENV / (version or "").split("v")[-1]
    target = env_dir / f".verify-{proof_id}.lean"
    target.write_text(path.read_text())
    try:
        built = run(["lake", "env", "lean", target.name], env_dir)
    finally:
        target.unlink(missing_ok=True)
    trouble = [l for l in (built.stdout + built.stderr).splitlines() if ": error" in l]
    if not trouble:
        print("  verified: the pruned file compiles")
    else:
        asked = {m for line in trouble for m in WANTED.findall(line)}
        fresh = {n for n in asked if n not in forced} | {
            d for n in asked for d in [next((x for x in by_name if x.endswith("." + n) or x == n), None)] if d
        }
        path.write_text(stored, newline="")
        if fresh - forced:
            print(f"  lean wanted {len(fresh - forced)} back, pruning again")
            os.execve(sys.executable, [sys.executable, *sys.argv],
                      {**os.environ, "PRUNE_FORCED": " ".join(forced | fresh)})
        print(f"  refusing to prune: the result did not compile and lean did not name what is missing")
        for line in trouble[:3]:
            print(f"    {line[:110]}")
        sys.exit(1)
