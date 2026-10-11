import json
import os
import re
import sys
import tempfile
from pathlib import Path

from api.compiler import COMPILE_ENV, run

DUMPER = COMPILE_ENV / "deps.lean"

args = [a for a in sys.argv[1:] if not a.startswith("--")]
if not args:
    sys.exit("usage: python -m scripts.prune FILE [ROOT]")
path = Path(args[0]).resolve()
root = args[1] if len(args) > 1 else None


def toolchain_of(file):
    for folder in [file.parent, *file.parents]:
        pinned = folder / "lean-toolchain"
        if pinned.exists():
            return pinned.read_text().strip().rsplit("v", 1)[-1]
    sys.exit(f"no lean-toolchain beside {file}, so there is no telling which lean to use")


version = toolchain_of(path)
env_dir = COMPILE_ENV / version
if not env_dir.is_dir():
    sys.exit(f"no compile environment for lean {version} at {env_dir}")
if root is None:
    named = re.fullmatch(r"Erdos(\d+)", path.stem)
    if not named:
        sys.exit(f"pass the root theorem: cannot infer one from {path.name}")
    root = f"Erdos{named.group(1)}.erdos_{named.group(1)}"


def lean(file, mode):
    handle, name = tempfile.mkstemp(suffix=".json")
    os.close(handle)
    out = Path(name)
    try:
        done = run(["lake", "env", "lean", "--run", str(DUMPER), str(file), str(out), mode, root],
                   env_dir)
        text = out.read_text(encoding="utf-8")
    finally:
        out.unlink(missing_ok=True)
    if done.returncode != 0 or not text.strip():
        said = (done.stderr.strip() or done.stdout.strip())[-300:]
        sys.exit(f"lean stopped before the end of {file.name} (exit {done.returncode}): {said}")
    return [json.loads(line) for line in text.split("\n") if line.strip()]


stored = open(path, newline="", encoding="utf-8").read()
ending = "\r\n" if "\r\n" in stored else "\n"
lines = [line.rstrip("\r") for line in stored.split("\n")]
*rows, original = lean(path, "--root")
rows = [r for r in rows if not r["kind"].endswith(".eoi")]
broken = sum(r["errors"] for r in rows)
if broken:
    sys.exit(f"{path.name} has {broken} errors as it stands, so there is nothing sound to prune")
if original["statement"] is None:
    sys.exit(f"{root} is not defined in {path.name}")
if "sorryAx" in original["axioms"]:
    sys.exit(f"{root} rests on sorry as it stands, so there is nothing sound to prune")
print(f"root: {root}   lean {version}   {len(rows)} commands")

needs = [set(r["needs"]) for r in rows]
for x, r in enumerate(rows):
    if r["lossy"]:
        needs[x] |= {k for k in range(x) if rows[k]["traced"]}
    if r["divergent"]:
        needs[x] |= set(range(x))
role = [r["role"] for r in rows]


def observe():
    for k, r in enumerate(rows):
        if r["observable"] and role[k] in {"prunable", "follows", "drop"}:
            role[k] = "keep"
            r["unaccounted"] = r["unaccounted"] + r["observable"]
            stack.append(k)


def prefixes(name):
    parts = name.split(".")
    return {".".join(parts[:i]) for i in range(1, len(parts) + 1)}


def lines_of(k):
    stop = rows[k + 1]["start"] if k + 1 < len(rows) else len(lines) + 1
    return range(rows[k]["start"], max(stop, rows[k]["finish"] + 1, rows[k]["start"] + 1))


extent = []
for k in range(len(rows)):
    depth, j = 0, k + 1
    while j < len(rows) and depth + rows[j]["delta"] >= 0:
        depth += rows[j]["delta"]
        j += 1
    extent.append(range(k + 1, j))
touch = {}
for k in range(len(rows)):
    for i in lines_of(k):
        touch.setdefault(i, set()).add(k)
under = {}
for k, r in enumerate(rows):
    for name in r["defines"]:
        for space in prefixes(name) - {name}:
            under.setdefault(space, []).append(k)
    for space in r["registers"]:
        under.setdefault(space, []).append(k)


def gone(reachable, forced):
    going = {k for k in range(len(rows))
             if role[k] in {"drop", "prunable"} and k not in reachable and k not in forced}
    while True:
        grown = {k for k in range(len(rows)) if k not in going and k not in forced
                 and role[k] == "follows" and (rows[k]["targets"] and set(rows[k]["targets"]) <= going
                                               or not rows[k]["targets"] and needs[k] and needs[k] <= going
                                               or not needs[k] and rows[k]["local"]
                                               and not any(j not in going and role[j] != "scope"
                                                           for j in extent[k]))}
        if not grown:
            break
        going |= grown
    while True:
        pairs, blocks = set(), []

        def idle(opener, closed):
            return (not any(occupied for _, occupied, _ in closed)
                    or rows[opener]["plain"] and not any(undone for _, _, undone in closed))

        for k, r in enumerate(rows):
            if k in going:
                continue
            if r["delta"] > 0:
                blocks += [[k, False, False] for _ in range(r["delta"])]
            elif r["delta"] < 0:
                closed = blocks[r["delta"]:]
                del blocks[r["delta"]:]
                openers = {opener for opener, _, _ in closed}
                (opener,) = openers if len(openers) == 1 else (None,)
                whole = opener is not None and rows[opener]["delta"] == -r["delta"]
                if (whole and idle(opener, closed) and not {opener, k} & forced
                        and not (rows[opener]["scope"] == "namespace"
                                 and registers(opener, k, going | pairs))):
                    pairs |= {opener, k}
                    if blocks and any(occupied for _, occupied, _ in closed):
                        blocks[-1][1] = True
                elif blocks:
                    blocks[-1][1] = True
            elif blocks:
                blocks[-1][1] = True
                blocks[-1][2] = blocks[-1][2] or r["local"]
        inner = False
        for opener in reversed(list(dict.fromkeys(opener for opener, _, _ in blocks))):
            closed = [b for b in blocks if b[0] == opener]
            if inner:
                closed[-1][1] = True
            if (len(closed) == rows[opener]["delta"] and idle(opener, closed)
                    and opener not in forced
                    and not (rows[opener]["scope"] == "namespace"
                             and registers(opener, None, going | pairs))):
                pairs.add(opener)
                inner = any(occupied for _, occupied, _ in closed)
            else:
                inner = True
        if not pairs:
            return going
        going |= pairs


def registers(opener, end, going):
    staying = set(range(len(rows))) - going - {opener, end}
    return any(ns in prefixes(rows[opener]["namespace"]) and not registered(ns, j, staying)
               for j in staying for ns in rows[j]["opens"])


def registered(ns, k, staying):
    return any(j < k and j in staying for j in under.get(ns, ())) or any(
        j < k and j in staying and rows[j]["scope"] == "namespace"
        and ns in prefixes(rows[j]["namespace"]) for j in range(k))


reachable, forced, observed = set(), set(), False
stack = [k for k, r in enumerate(rows) if root in r["defines"] or r["role"] == "keep"]
while True:
    while stack:
        k = stack.pop()
        if k not in reachable:
            reachable.add(k)
            stack.extend(needs[k] - reachable)
    going = gone(reachable, forced)
    staying = set(range(len(rows))) - going
    wanted = []
    for k in sorted(staying):
        if role[k] == "follows":
            wanted += [(k, j) for j in needs[k] - reachable]
        for c in rows[k]["choices"]:
            if c and not set(c) & staying:
                wanted.append((k, min(c)))
        for ns in rows[k]["opens"]:
            earlier = [j for j in under.get(ns, ()) if j < k]
            if earlier and not registered(ns, k, staying):
                wanted.append((k, min(earlier)))
    pulled = {k for k in going if any(touch[i] - going for i in lines_of(k))}
    spent = 0
    for k in range(len(rows)):
        if k in going and rows[k]["fills"]:
            spent += rows[k]["heartbeats"]
        elif k not in going and rows[k]["limit"] and rows[k]["heartbeats"] + spent > rows[k]["limit"]:
            wanted += [(k, j) for j in range(k) if j in going and rows[j]["fills"]]
    wanted = [(k, j) for k, j in wanted if j not in reachable]
    if not observed and any(rows[k]["observes"] for k in staying):
        observed = True
        observe()
        continue
    if not wanted and not pulled:
        break
    forced |= pulled
    for k in pulled:
        stack.extend(needs[k])
    for k, j in wanted:
        if j != k:
            needs[k].add(j)
        stack.append(j)

header = rows[0]["start"] if rows else len(lines) + 1
out = [line for i, line in enumerate(lines, 1)
       if i < header or not touch.get(i) or not touch[i] <= going]
body = ending.join(out).rstrip("\r\n") + ending
kept = [k for k in range(len(rows)) if k not in going]
removed = len(lines) - len(out)
print(f"{len(kept)} of {len(rows)} commands kept")
print(f"{len(lines):,} -> {len(out):,} lines ({100 * removed / max(len(lines), 1):.1f}% removed)")

handle, name = tempfile.mkstemp(suffix=".lean", dir=path.parent)
os.close(handle)
candidate = Path(name)
candidate.write_text(body, newline="", encoding="utf-8")
os.chmod(candidate, path.stat().st_mode)
try:
    [result] = lean(candidate, "--check")
    if result["errors"] or result["statement"] != original["statement"]:
        what = (f"the result has {result['errors']} errors" if result["errors"]
                else f"{root} no longer states the same thing in the result")
        sys.exit(f"  refusing to prune: {what}, {path.name} is left as it was")
    if "sorryAx" in result["axioms"]:
        sys.exit(f"  refusing to prune: {root} rests on sorry in the result, "
                 f"{path.name} is left as it was")
    os.replace(candidate, path)
finally:
    candidate.unlink(missing_ok=True)
used = set().union(*(needs[k] for k in kept))
extra = [min(rows[k]["defines"], key=len) if rows[k]["defines"] else f"line {rows[k]['start']}"
         for k in kept if role[k] == "prunable" and k not in used and root not in rows[k]["defines"]
         and k not in forced]
print(f"  verified: compiles, proves the same {root} without sorry, {1 + len(extra)} root"
      + ("" if not extra else "s: " + ", ".join(extra[:5])))
unknown = sorted({e for k in kept for e in rows[k]["unaccounted"]})
if unknown:
    print(f"  kept whatever adds to what lean records no use of: {', '.join(unknown)}")
if forced:
    print(f"  kept because they share a line with what stays: {len(forced)} commands")
