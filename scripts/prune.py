import bisect
import collections
import os
import re
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
        r.id: (r.name, r.is_generated, r.line_start, r.line_end, r.is_instance)
        for r in conn.execute(
            text("SELECT id, name, is_generated, line_start, line_end, is_instance FROM declaration WHERE proof_id = :p"),
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

spans = [(st, en or st, i) for i, (nm, gen, st, en, _) in decls.items() if st]
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

written = [(st, en or st) for nm, gen, st, en, _ in decls.values() if st and not gen]
standalone = [
    i for i, (nm, gen, st, en, _) in decls.items()
    if gen and st and not any(a <= st and (en or st) <= b for a, b in written)
]
SEARCH_ATTR = re.compile(r"@\[[^\]]*\b(?:ext|aesop|grind|fun_prop|norm_cast|push_cast|coe|elab_as_elim"
                         r"|continuity|measurability|positivity|gcongr|bound|mono|refl|symm|trans"
                         r"|simps|to_additive|reducible_and_instances)\b")


def tagged_for_search(st):
    if SEARCH_ATTR.search(lines[st - 1]):
        return True
    k = st - 1
    while k >= 1 and lines[k - 1].lstrip().startswith("@["):
        if SEARCH_ATTR.search(lines[k - 1]):
            return True
        k -= 1
    return False


# typeclass resolution and the attribute-driven tactics find these by shape rather than by
# name, so nothing points at them and reachability alone would delete them. the ones lean
# generates for a type are not seeded: they exist only to serve that type and go with it
found_by_search = [i for i, (nm, gen, st, en, inst) in decls.items()
                   if not gen and (inst or (st and tagged_for_search(st)))]
reachable, stack = set(), [by_name[root], *standalone, *found_by_search]
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
for i, (name, generated, start, end, _) in decls.items():
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
    members = [d for d in decls.values() if d[2] and not d[1] and m < d[2] < e]
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
    for i, (name, generated, start, end, _) in decls.items():
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
# a name stops existing exactly when the lines that wrote it go, which covers the generated
# ones too: a structure's projections leave with the structure
deleted_full = ({part for n in dead if n not in rescued for part in n.split("\x00")}
                | {nm for nm, _, st, _, _ in decls.values() if st and st in drop})
surviving_full = {nm for nm, _, st, _, _ in decls.values() if st and st not in drop}
gone = deleted_full - surviving_full
GROUP = re.compile(r"[\[{(\u2983]([^\]})\u2984]*)[\]})\u2984]")

OPENED = re.compile(r"^\s*(open|export)\b(?!.*\bin\b)\s*(?:scoped\s+)?(.*)$")
# `open A B in <command>` is in scope for that one command, whether the command follows on the
# same line or the next
JUST_FOR_NEXT = re.compile(r"^\s*open\s+(?:scoped\s+)?(.*?)\bin\b")
CARRIES_ON = re.compile(r"^\s+\S")
LISTED = re.compile(r"\(([^)]*)\)")
mine = {nm for nm, _, _, _, _ in decls.values()}
# PRUNE_NAMES points at a dump of the environment lean compiled against: every constant the
# library defines, `p` for protected and `i` for an instance. without it the pruner has to
# assume any name it cannot see is the library's, which is a guess in both directions
library, library_spaces, guarded = set(), set(), set()
elsewhere = os.environ.get("PRUNE_NAMES")
if elsewhere and Path(elsewhere).exists():
    for entry in Path(elsewhere).read_text().splitlines():
        name, _, flags = entry.partition(" ")
        if "n" in flags: # a namespace exists in its own right, with or without constants in it
            library_spaces.add(name)
            continue
        library.add(name)
        if "p" in flags:
            guarded.add(name)
    print(f"  environment: {len(library):,} library names, {len(library_spaces):,} namespaces, "
          f"{len(guarded):,} protected")
else:
    print("  no environment dump: set PRUNE_NAMES to check that every name still resolves")
PROTECTED = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|noncomputable|unsafe|partial|nonrec)\s+)*protected\b")
guarded |= {nm for nm, _, st, _, _ in decls.values() if st and PROTECTED.match(BLANK[st - 1])}
known_names = mine | library
def spaces_the_file_opens():
    """namespaces the source declares, which a `namespace` line creates even when it holds
    nothing: those cannot be found by looking at declaration names"""
    declared, chain = set(), []
    for line in BLANK:
        if NAMESPACE.match(line):
            chain.extend(NAMESPACE_NAME.match(line).group(1).split("."))
            declared.add(".".join(part for part in chain if part))
        elif SECTION.match(line) or MUTUAL.match(line):
            chain.append(None)
        elif END.match(line):
            for _ in (line.split()[1].split(".") if len(line.split()) > 1 else [None]):
                if not chain:
                    break
                if chain.pop() is None:
                    break
    return {name for name in declared if name}


known_spaces = ({".".join(nm.split(".")[:k])
                 for nm in known_names for k in range(1, len(nm.split(".")))}
                | library_spaces | spaces_the_file_opens())


def space_here(chain, space, already_open=()):
    if space.startswith("_root_."): # names the root outright, so the enclosing chain is not tried
        return space[len("_root_."):]
    # lean's resolveNamespace: the innermost enclosing namespace that has one by this name wins,
    # and a name matching none of them is the library's, or nobody's
    for depth in range(len(chain), 0, -1):
        full = ".".join(chain[:depth]) + "." + space
        if full in known_spaces:
            return full
    if space in known_spaces:
        return space
    for under in already_open:
        if f"{under}.{space}" in known_spaces:
            return f"{under}.{space}"
    return space

def command_span(k):
    j = k
    while j < len(BLANK) and not BLANK[j].strip(): # the command may start a line or two below
        j += 1
    j += 1
    while j < len(BLANK) and BLANK[j][:1].isspace() and BLANK[j].strip():
        j += 1
    return range(k, min(j, len(BLANK)) + 1)


def command_at(k):
    j = k
    while j < len(BLANK) and BLANK[j][:1].isspace() and BLANK[j].strip():
        j += 1
    return range(k, j + 1)


BINDS_NAMES = re.compile(r"^\s*(?:variable|universe)\b")
DELIMITED = re.compile(r"([\[{(\u2983])([^\]})\u2984]*)[\]})\u2984]")


def binders_written(span):
    """the names a variable or universe command introduces, which shadow anything global"""
    names = set()
    for k in span:
        line = BLANK[k - 1]
        bare = BINDS_NAMES.match(line)
        for opener, group in DELIMITED.findall(line):
            if ":" in group:
                names.update(WORD.findall(group.split(":")[0]))
            elif opener != "[": # `[Foo x]` is an anonymous instance: a type, nothing bound
                names.update(WORD.findall(group))
        if bare: # `universe u v` and `variable x` write names with no delimiter at all
            names.update(WORD.findall(DELIMITED.sub(" ", line))[1:])
    return names


prefix_at, scope_at, for_line, binders_at = {}, {}, {}, {}
namespace_stack, scope_stack, binder_stack = [], [[]], [set()]
for i, line in enumerate(BLANK, 1):
    if NAMESPACE.match(line):
        for part in NAMESPACE_NAME.match(line).group(1).split("."):
            namespace_stack.append(part)
            scope_stack.append([])
            binder_stack.append(set())
    elif SECTION.match(line) or MUTUAL.match(line):
        namespace_stack.append(None)
        scope_stack.append([])
        binder_stack.append(set())
    elif END.match(line):
        for _ in (line.split()[1].split(".") if len(line.split()) > 1 else [None]):
            if not namespace_stack:
                break
            if len(scope_stack) > 1:
                scope_stack.pop()
                binder_stack.pop()
            if namespace_stack.pop() is None:
                break
    else:
        command = OPENED.match(line)
        if command:
            payload, j = command.group(2), i
            while not payload.strip() and j < len(BLANK) and CARRIES_ON.match(BLANK[j]):
                payload = BLANK[j]
                j += 1
            while j < len(BLANK) and CARRIES_ON.match(BLANK[j]):
                payload += " " + BLANK[j]
                j += 1
            payload = payload.split("--")[0]
            chain_here = [p for p in namespace_stack if p]
            open_here = [o[1] for level in scope_stack for o in level if o[0] == "simple"]
            listed = LISTED.search(payload)
            names = WORD.findall(payload[:listed.start()] if listed else payload)
            if listed: # open A (x y), and export A (x y), bring in only those names
                for space in names:
                    full = space_here(chain_here, space, open_here)
                    scope_stack[-1].extend(("alias", member, full + "." + member)
                                           for member in WORD.findall(listed.group(1)))
            elif " hiding " in f" {payload} ":
                head, _, rest = payload.partition("hiding")
                for space in WORD.findall(head):
                    scope_stack[-1].append(("simple", space_here(chain_here, space, open_here),
                                            frozenset(WORD.findall(rest))))
            else:
                for space in names:
                    scope_stack[-1].append(
                        ("simple", space_here(chain_here, space, open_here), frozenset()))
    if BINDS_NAMES.match(line):
        binder_stack[-1] |= binders_written(command_at(i))
    prefix_at[i] = [p for p in namespace_stack if p]
    scope_at[i] = [entry for level in scope_stack for entry in level]
    binders_at[i] = set().union(*binder_stack)
    just_here = JUST_FOR_NEXT.match(line)
    if just_here:
        chain_now = [p for p in namespace_stack if p]
        already = [o[1] for level in scope_stack for o in level if o[0] == "simple"]
        brought = [("simple", space_here(chain_now, space, already), frozenset())
                   for space in WORD.findall(just_here.group(1).split("--")[0])]
        # the command may be written after the `in` or on the lines below it
        here = command_at(i) if line[just_here.end():].strip() else command_span(i)
        for k in here:
            for_line.setdefault(k, []).extend(brought)


def qualified(space, name):
    # lean's resolveQualifiedName: does `space ++ name` exist, and is it reachable from a bare name
    full = f"{space}.{name}" if space else name
    if full not in known_names:
        return None
    if "." not in name and full in guarded: # atomic reference to a protected declaration
        return None
    return full


def referent(k, name, seen=()):
    """what lean's resolveGlobalName would land on, over this file's declarations and, when a
    dump of the environment was given, the library's"""
    if name in seen:
        return None
    chain = prefix_at.get(k, [])
    for depth in range(len(chain), 0, -1): # resolveUsingNamespace: innermost first, first wins
        found = qualified(".".join(chain[:depth]), name)
        if found:
            return found
    if "." in name: # resolveExact, with _root_ stripped
        exact = name[len("_root_."):] if name.startswith("_root_.") else name
        if exact in known_names:
            return exact
    if name in known_names:
        return name
    reachable_here = list(scope_at.get(k, ())) + for_line.get(k, [])
    for kind, *rest in reversed(reachable_here): # resolveOpenDecls, latest first
        if kind == "simple":
            space, hidden = rest
            if name not in hidden:
                found = qualified(space, name)
                if found:
                    return found
        else:
            opened, resolved = rest
            if opened == name:
                if resolved in known_names: # a stale alias does not stop the other opens
                    return resolved
                continue
            if name.startswith(opened + "."):
                candidate = resolved + name[len(opened):]
                if candidate in known_names:
                    return candidate
    if "." in name: # dot notation: the last component is a projection, resolve the owner
        return referent(k, name.rsplit(".", 1)[0], (*seen, name))
    return None


def mentions(line):
    bound = set()
    for group in GROUP.findall(line):
        head = group.split(":")[0] if ":" in group else ""
        bound.update(WORD.findall(head))
    return set(WORD.findall(line)) - bound


def names_something_gone(k, bound):
    for tok in mentions(BLANK[k - 1]) - bound - binders_at.get(k, set()):
        landed = referent(k, tok)
        if landed in gone:
            return True
    return False


ATTRIBUTES = re.compile(r"@\[([^\]]*)\]|^\s*attribute\s+\[([^\]]*)\]")


def bound_across(span):
    """names a command writes rather than refers to: its binders and the attributes it applies"""
    names, binder = set(), BINDS_NAMES.match(BLANK[span[0] - 1])
    for k in span:
        line = BLANK[k - 1]
        for wrapped in ATTRIBUTES.findall(line):
            for entry in "".join(wrapped).split(","):
                leading = WORD.findall(entry) # `@[to_additive foo]` names foo, `simp` is not one
                names.update(leading[:1])
        for opener, group in DELIMITED.findall(line):
            if ":" in group:
                names.update(WORD.findall(group.split(":")[0]))
            elif binder and opener != "[": # `[Foo x]` is an anonymous instance: a type, not a binding
                names.update(WORD.findall(group))
    return names


EXAMPLE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*example\b")

orphaned = set()
for i, line in enumerate(BLANK, 1):
    if i not in drop and EXAMPLE.match(line):
        orphaned.update(command_at(i))
    if i in drop or not BINDER.match(line):
        continue
    span = command_at(i)
    bound = bound_across(span)
    if any(names_something_gone(k, bound) for k in span):
        orphaned.update(span)
if orphaned:
    print(f"  dropping {len(orphaned)} lines of examples and commands that name something deleted")
    drop |= orphaned

# the guard below asks which original lines are still standing, so their numbers travel too
origin = [i for i in range(1, len(lines) + 1) if i not in drop]
lines = [l for i, l in enumerate(lines, 1) if i not in drop]
print(f"dropped {len(drop):,} lines")

OPEN = re.compile(r"^\s*(?:open|export)\b\s*(?:scoped\s+)?(.*)$")
FILLER = re.compile(r"^\s*(?:open|export|variable|universe)\b")
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
    empties = []
    for i, line in enumerate(scan, 1):
        if NAMESPACE.match(line):
            if stack:
                stack[-1][2] = True
            parent = next((e[4] for e in reversed(stack) if e[0] == "namespace"), "")
            written, fulls = NAMESPACE_NAME.match(line).group(1), []
            for part in written.split("."):
                parent = f"{parent}.{part}" if parent else part
                fulls.append(parent)
            for nth, full in enumerate(fulls):
                stack.append(["namespace", i, False, nth == 0, full, written])
        elif SECTION.match(line):
            stack.append(["section", i, False, False, None, None])
        elif MUTUAL.match(line):
            stack.append(["mutual", i, False, False, None, None])
        elif END.match(line):
            closing = line.split()[1].split(".") if len(line.split()) > 1 else [None]
            for _ in closing:
                if not stack:
                    print(f"  warning: unmatched end at line {i}")
                    break
                kind, opened, occupied, outermost, full, ns = stack.pop()
                if kind != "namespace":
                    if stack and occupied:
                        stack[-1][2] = True
                    break
                if not occupied and outermost:
                    empties.append((ns, opened, i))
                if stack and occupied:
                    stack[-1][2] = True
        elif stack and lines[i - 1].strip() and not FILLER.match(line):
            stack[-1][2] = True
    for ns, opened, closed in empties:
        if any(part in opened_names for part in [ns, *ns.split(".")]):
            continue
        kill |= set(range(opened, closed + 1))
    if stack:
        print(f"  warning: {len(stack)} scopes left open")
    if not kill:
        break
    emptied += len(kill) // 2
    origin = [o for i, o in enumerate(origin, 1) if i not in kill]
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
            for part in NAMESPACE_NAME.match(line).group(1).split("."):
                stack.append(("namespace", part, i))
        elif SECTION.match(line):
            named = SECTION_NAME.match(line)
            stack.append(("section", named.group(1) if named else None, i))
        elif MUTUAL.match(line):
            stack.append(("mutual", None, i))
        elif END.match(line):
            named = line.split()[1] if len(line.split()) > 1 else None
            for part in reversed(named.split(".") if named else [None]):
                if not stack:
                    problems.append(f"line {i}: `end` with no open scope")
                    break
                kind, name, opened = stack.pop()
                if kind != "namespace":
                    if named is not None and named != name:
                        problems.append(f"line {i}: `end {named}` closes the {kind} opened at line {opened}")
                    break
                if part != name:
                    problems.append(f"line {i}: `end {named or ''}`".rstrip()
                                    + f" closes `namespace {name}` from line {opened}")
        elif modifier_at(src, i):
            j = i + 1
            while j <= len(src) and (not src[j - 1].strip() or src[j - 1].lstrip().startswith("--")):
                j += 1
            if j > len(src) or END.match(src[j - 1]):
                problems.append(f"line {i}: `{line.strip()[:40]}` modifies nothing")
    for kind, name, opened in stack:
        problems.append(f"line {opened}: {kind} {name or ''}".rstrip() + " is never closed")
    return problems

def holds_a_namespace(catalogue, space):
    """is anything still called `space.something`, without building every prefix of every name"""
    at = bisect.bisect_left(catalogue, space + ".")
    return at < len(catalogue) and catalogue[at].startswith(space + ".")


def dangling_references(kept):
    """every name a command still writes down has to still resolve, which is the check lean
    would make. it needs a dump of the environment: without one a library name cannot be told
    from a deleted local one. proof bodies are left alone -- the identifiers in them are mostly
    binders lean introduces locally, which no name table can account for"""
    if not library:
        return []
    left_standing = set(kept)
    staying = sorted(nm for nm, _, st, _, _ in decls.values() if st and st in left_standing)
    # an emptied namespace still exists as long as its `namespace` line is kept, which is what
    # the hollow pass does whenever something opens it
    shells = set()
    for i in kept:
        if NAMESPACE.match(BLANK[i - 1]):
            chain = prefix_at.get(i, [])
            for depth in range(1, len(chain) + 1):
                shells.add(".".join(chain[:depth]))
    broken, seen = [], set()
    for i in kept:
        line = BLANK[i - 1]
        if not line.strip() or line.lstrip().startswith("--"):
            continue
        brought_in = OPENED.match(line) or JUST_FOR_NEXT.match(line)
        if brought_in:
            # an open names a namespace, which lives as long as anything inside it does
            payload = brought_in.group(brought_in.re.groups).split("--")[0]
            listed = LISTED.search(payload) # `open A (x y)`: only A is a namespace
            payload = payload[:listed.start()] if listed else payload.partition("hiding")[0]
            for tok in WORD.findall(payload):
                space = space_here(prefix_at.get(i, []), tok,
                                   [o[1] for o in scope_at.get(i, ()) if o[0] == "simple"])
                if space in library_spaces or space in shells or holds_a_namespace(staying, space):
                    continue
                if space not in seen:
                    seen.add(space)
                    broken.append(f"line {i}: `{tok}` opens {space}, which will be empty")
            continue
        if not BINDER.match(line):
            continue
        skip = bound_across(command_at(i)) | binders_at.get(i, set())
        for tok in mentions(line) - skip:
            landed = referent(i, tok)
            if landed in gone and landed not in seen:
                seen.add(landed)
                broken.append(f"line {i}: `{tok}` still names {landed}, which is being deleted")
    return broken


dangling = dangling_references(origin)
if dangling:
    print(f"refusing to write: {len(dangling)} references would not resolve")
    for note in dangling[:5]:
        print(f"  {note}")
    sys.exit(1)

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
# a namespace exists only while something in it does, and one built from qualified names alone
# leaves no `namespace` line to keep, so the first declaration under it has to stay
EMPTIED = re.compile(r"[Uu]nknown namespace `([^`]+)`")

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
        for space in {m for line in trouble for m in EMPTIED.findall(line)}:
            inhabitant = next((n for n in sorted(by_name)
                               if f".{space}." in n or n.startswith(space + ".")), None)
            if inhabitant:
                asked.add(inhabitant)
        fresh = {n for n in asked if n not in forced} | {
            d for n in asked for d in [next((x for x in by_name if x.endswith("." + n) or x == n), None)] if d
        }
        path.write_text(stored, newline="")
        rounds = int(os.environ.get("PRUNE_REPAIRS", "0"))
        if fresh - forced and rounds < 5: # each round is another full compile, so do not spiral
            print(f"  lean wanted {len(fresh - forced)} back, pruning again (round {rounds + 1})")
            os.execve(sys.executable, [sys.executable, *sys.argv],
                      {**os.environ, "PRUNE_FORCED": " ".join(forced | fresh),
                       "PRUNE_REPAIRS": str(rounds + 1)})
        if fresh - forced:
            print(f"  giving up after {rounds} repairs: lean still wants {len(fresh - forced)} back")
            sys.exit(1)
        print("  refusing to prune: the result did not compile and lean did not name what is missing")
        for line in trouble[:3]:
            print(f"    {line[:110]}")
        sys.exit(1)
