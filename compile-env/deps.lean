import Lean
import Lean.Server.InfoUtils

open Lean Elab Frontend

/-!
Elaborates a file one command at a time and writes, for every command, the lines it spans, the
constants it defines and everything it relies on. Everything comes from lean itself: the parser
decides where a command starts and ends, the info trees say what each identifier resolved to, the
finished terms say what each declaration is made of, and lean's traces and diagnostics say what
elaboration used on the way without leaving it in any term.

    lake env lean --run deps.lean Upload.lean deps.jsonl
    lake env lean --run deps.lean Upload.lean result.json --check Root.theorem
-/

/-- a private name as it is written, rather than as the environment mangles it -/
def shown (n : Name) : Name := (privateToUserName? n).getD n

structure Found where
  defs : NameSet := {}
  uses : NameSet := {}
  named : NameSet := {}
  routes : Array (String × Nat) := #[]
  choices : Array (Array (String × Nat)) := #[]
  kinds : NameSet := {}
  levels : NameSet := {}
  attrs : NameSet := {}
  seen : Std.HashSet (Name × Nat) := {}
  expanded : Array Syntax := #[]
  resolvedAt : Std.HashSet Nat := {}
  quotedNs : NameSet := {}
  shadows : NameSet := {}

/-- the attributes a piece of syntax applies, by the name they are registered under, and those it
takes off, with a `-` in front -/
partial def attributes (stx : Syntax) (acc : NameSet) : NameSet :=
  let acc := if stx.getKind == ``Parser.Term.attrInstance then
      let attr := stx[1]
      acc.insert (if attr.getKind == ``Parser.Attr.simple then attr[0].getId.eraseMacroScopes
        else attr.getKind.componentsRev.head!)
    else if stx.getKind == ``Parser.Command.eraseAttr then
      acc.insert (.mkSimple ("-" ++ stx[1].getId.eraseMacroScopes.toString))
    else acc
  stx.getArgs.foldl (fun acc a => attributes a acc) acc

/-- what makes an identifier resolve to `name` where it stands, among the `open`s in effect and the
aliases this file exported: those it would not resolve to `name` without, one by one, and when it
has several that each suffice without the others of their kind, all of those as a choice. an
`open` can lead to `name` through an alias in the namespace it opens. lean's own name resolution is asked
again with each taken away. each comes with how many times it is in effect there, since the same
`open` made twice, once perhaps by the command itself, is needed from neither while the other stays -/
def routes (ctx : ContextInfo) (lctx : LocalContext) (id name : Name) :
    IO (Array (String × Nat) × Array (Array (String × Nat))) := do
  let resolves (c : ContextInfo) : IO Bool := do
    let found ← c.runMetaM lctx (resolveGlobalName id)
    return found.any (·.1 == name)
  unless ← resolves ctx do return (#[], #[])
  let plain := (privateToUserName? name).getD name
  let aliasOf (n : Name) := ((getAliasState ctx.env).find? n).any (·.contains name)
  let opens := ctx.openDecls.eraseDups.filter fun
    | .simple ns _ => ns.isPrefixOf plain || aliasOf (ns ++ id)
    | .explicit _ decl => decl == name || decl == plain || aliasOf decl ||
      decl.isPrefixOf name || decl.isPrefixOf plain
  let aliases := (getAliasState ctx.env).map₂.toList.filter (·.2.contains name)
  let without (drop : List OpenDecl) (gone : List (Name × List Name)) : ContextInfo :=
    { ctx with
      openDecls := ctx.openDecls.filter (!drop.contains ·)
      env := gone.foldl (fun env (a, targets) =>
        aliasExtension.modifyState env fun s => s.insert a (targets.erase name)) ctx.env }
  let times (d : OpenDecl) := (ctx.openDecls.filter (· == d)).length
  let mut needed := #[]
  for d in opens do
    unless ← resolves (without [d] []) do needed := needed.push (s!"open {d}", times d)
  for a in aliases do
    unless ← resolves (without [] [a]) do needed := needed.push (s!"alias {a.1}", 1)
  if !needed.isEmpty || (opens.isEmpty && aliases.isEmpty) then return (needed, #[])
  if ← resolves (without opens aliases) then return (needed, #[])
  let mut alone := #[]
  for d in opens do
    if ← resolves (without (opens.erase d) []) then alone := alone.push (s!"open {d}", times d)
  for a in aliases do
    if ← resolves (without [] (aliases.erase a)) then alone := alone.push (s!"alias {a.1}", 1)
  return (needed, #[alone])

/-- every identifier node in a piece of syntax -/
partial def identNodes (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  let acc := if stx.isIdent then acc.push stx else acc
  stx.getArgs.foldl (fun acc a => identNodes a acc) acc

/-- every syntax kind a command is written with. a notation or syntax declared in the file is a
parser constant of that name. of the readings of syntax that parses more than one way, only those
elaboration went on with count, where it is known which -/
partial def kinds (stx : Syntax) (acc : NameSet := {}) (seen : Std.HashSet (Name × Nat) := {})
    (only : Option Name := none) : NameSet :=
  let args := if stx.isOfKind choiceKind then
      let taken := stx.getArgs.filter fun a => match a.getPos? with
        | some p => seen.contains (a.getKind, p.byteIdx)
        | none => false
      let named := stx.getArgs.filter fun a => only.any (·.isSuffixOf a.getKind)
      if !taken.isEmpty then taken else if !named.isEmpty then named else stx.getArgs
    else stx.getArgs
  -- atoms, identifiers and literals are not kinds anything declares
  let literal := [`num, `str, `char, `scientific, `name, `fieldIdx, `hygieneInfo]
  let counts := match stx with
    | .node _ k _ => k != nullKind && k != choiceKind && !literal.contains k
    | _ => false
  args.foldl (fun acc a => kinds a acc seen only) (if counts then acc.insert stx.getKind else acc)

/-- every atom a piece of syntax is written with -/
partial def atomsOf (stx : Syntax) (acc : Array String := #[]) : Array String :=
  match stx with
  | .atom _ v => acc.push v
  | _ => stx.getArgs.foldl (fun acc a => atomsOf a acc) acc

/-- every syntax node of a piece of syntax that has a position, by kind and position -/
partial def kindNodes (stx : Syntax) (acc : Array (Name × Nat) := #[]) : Array (Name × Nat) :=
  let acc := match stx, stx.getPos? with
    | .node _ k _, some p => if k != nullKind && k != choiceKind then acc.push (k, p.byteIdx) else acc
    | _, _ => acc
  stx.getArgs.foldl (fun acc a => kindNodes a acc) acc

/-- the names a `simp [-foo]` takes out of the simp set -/
partial def erased (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  let acc := if stx.getKind.componentsRev.head? == some `simpErase then acc ++ identNodes stx[1]
    else acc
  stx.getArgs.foldl (fun acc a => erased a acc) acc

/-- whether a command that declares macros or elaborators runs code of its own when they are used,
rather than putting quotations in place: any elaborator does, and so does a macro whose right-hand
side is not a quotation, which can ask what the environment holds -/
partial def runsCode (stx : Syntax) : Bool :=
  let k := stx.getKind
  if k == ``Parser.Command.elab || k == ``Parser.Command.elab_rules then true
  else if k == ``Parser.Command.macro then !stx.getArgs.back!.getArgs.back!.isQuot &&
    !(stx.getArgs.back!.getArgs.back![0]).isQuot
  else if k == ``Parser.Term.matchAlt then !stx[3].isQuot
  else stx.getArgs.any runsCode

/-- the kind a `macro_rules` or `elab_rules` says it is for, as `(kind := k)` -/
partial def explicitKind (stx : Syntax) : Option Name :=
  let args := stx.getArgs
  match (List.range args.size).find? fun i => args[i]!.isAtom && args[i]!.getAtomVal == "kind" with
  | some i => (args.toList.drop (i + 1)).findSome? fun a => if a.isIdent then some a.getId else none
  | none => args.toList.findSome? explicitKind

/-- the identifiers of a piece of syntax that could be names of constants, leaving out those in places
lean reads as something else: case and alternative tags, argument and field names, attributes and
options -/
partial def nameNodes (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  let k := stx.getKind
  if [``Parser.Tactic.caseArg, ``Parser.Tactic.inductionAltLHS, ``Parser.Term.structInstLVal,
      ``Parser.Term.attrInstance, ``Parser.Command.set_option].contains k then acc
  -- a `set_option ... in` in a tactic or term names an option, then wraps what it applies to
  else if k == ``Parser.Tactic.set_option || k == ``Parser.Term.set_option then nameNodes stx[5] acc
  else if k == ``Parser.Term.namedArgument then nameNodes stx[3] acc
  else if stx.isIdent then acc.push stx
  else stx.getArgs.foldl (fun acc a => nameNodes a acc) acc

/-- what makes a constant resolve where it is written: the identifier itself, or, for a name read off
a type's namespace as field notation and a leading dot read it, with no namespace current, the
names the `open`s and aliases in effect let it be found by -/
def record (ctx : ContextInfo) (lctx : LocalContext) (stx : Syntax) (name : Name) :
    StateT Found IO Unit := do
  let direct := stx.isIdent &&
    (← ctx.runMetaM lctx (resolveGlobalName stx.getId)).any (·.1 == name)
  let ids : List (Name × ContextInfo) := if direct then [(stx.getId, ctx)] else
    let bare := { ctx with currNamespace := .anonymous }
    -- the name is found as a type's namespace and a field, so only an `open` that leaves both
    -- parts to find can be what found it
    let viaOpens := ctx.openDecls.filterMap fun
      | .simple ns _ => if ns.isPrefixOf name && ns != name &&
          !(name.replacePrefix ns .anonymous).getPrefix.isAnonymous then
          some (name.replacePrefix ns .anonymous) else none
      | _ => none
    let viaAliases := (getAliasState ctx.env).map₂.toList.filterMap fun (a, ts) =>
      if ts.contains name then some a else none
    (viaOpens ++ viaAliases).map (·, bare)
  for (id, c) in ids do
    let (r, ch) ← routes c lctx id name
    modify fun a => { a with routes := a.routes ++ r, choices := a.choices ++ ch }

/-- the identifiers a quotation is written with, outside what it splices in -/
partial def quoted (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  if stx.isAntiquot || stx.isAntiquotSplice || stx.isAntiquotSuffixSplice then acc
  else if stx.isIdent then acc.push stx
  else stx.getArgs.foldl (fun acc a => quoted a acc) acc

/-- what a command's info trees say it defines and uses. only what lies inside the command's own
text counts, since every command elaborates the section variables again, with their info. a term is
recorded before its instances are synthesized, so it is read through the metavariable context of
its own node, where those assignments live. macros are looked through, so attributes a command
expands into are seen. an identifier in a quotation is resolved where the quotation is written,
through the `open`s in effect there, and leaves no info of its own -/
def collect (header : Environment) (range : Nat × Nat) (within : Array ((Nat × Nat) × List OpenDecl))
    (t : InfoTree) : StateT Found IO Unit :=
  t.visitM' fun ctx info _ => do
    -- lean records a command's context once, so what an `open ... in` inside its terms and tactics
    -- puts in effect is added back for what it wraps
    let ctx := match info.stx.getPos? with
      | some p => { ctx with openDecls := within.foldl (fun acc ((lo, hi), ds) =>
          if lo ≤ p.byteIdx && p.byteIdx < hi then ds ++ acc else acc) ctx.openDecls }
      | none => ctx
    let inside := match info.stx.getPos? with
      | some p => range.1 ≤ p.byteIdx && p.byteIdx < range.2
      | none => true
    if inside then
      if let some p := info.stx.getPos? then
        modify fun a => { a with seen := a.seen.insert (info.stx.getKind, p.byteIdx) }
    match info with
    | .ofTermInfo ti =>
      let e := (instantiateMVarsCore ctx.mctx ti.expr).1
      if (ti.stx.isIdent || ti.stx.getKind == ``Parser.Term.dotIdent ||
          ti.stx.getKind == Parser.Term.identProjKind) && (ti.isBinder || e.isConst || e.isFVar) then
        for part in identNodes ti.stx #[ti.stx] do
          if let some p := part.getPos? then
            modify fun a => { a with resolvedAt := a.resolvedAt.insert p.byteIdx }
      -- the section variables are elaborated anew for every command, under what is in effect where
      -- it stands, so what their names resolve through is needed there too
      if !inside then
        if let .const name _ := e then
          if ti.stx.isIdent && !ti.isBinder then record ctx ti.lctx ti.stx name
        unless ti.elaborator.isAnonymous do
          modify fun a => { a with uses := a.uses.insert ti.elaborator }
        return true
      -- a name bound in a pattern is a variable only while nothing makes it a constructor there, as
      -- what it would otherwise resolve to is shadowed by a constant or a variable of the file
      if ti.isBinder && ti.stx.isIdent then
        let id := ti.stx.getId
        let ctor := [header, ctx.env].any fun e => (ResolveName.resolveGlobalName e ctx.options
          ctx.currNamespace ctx.openDecls id).any fun (n, fs) => fs.isEmpty && (e.find? n).any (·.isCtor)
        if ctor then
          modify fun a => { a with shadows := a.shadows.insert id.eraseMacroScopes }
          for (n, _) in ← ctx.runMetaM ti.lctx (resolveGlobalName id) do
            modify fun a => { a with uses := a.uses.insert n }
            let (r, c) ← routes ctx ti.lctx id n
            modify fun a => { a with routes := a.routes ++ r, choices := a.choices ++ c }
      if ti.stx.isQuot then
        let body := if ti.stx.getKind == ``Parser.Term.dynamicQuot then ti.stx[3] else ti.stx[1]
        for id in (quoted body).toList do
          -- an identifier a quotation opens is resolved as a namespace where it is written
          for ns in ResolveName.resolveNamespace ctx.env ctx.currNamespace ctx.openDecls id.getId do
            modify fun a => { a with quotedNs := a.quotedNs.insert ns }
          let found ← ctx.runMetaM ti.lctx (resolveGlobalName id.getId)
          for (name, _) in found do
            let (r, c) ← routes ctx ti.lctx id.getId name
            modify fun a => { a with routes := a.routes ++ r, choices := a.choices ++ c }
      let levels := (CollectLevelParams.main e {}).params
      modify fun a => { a with levels := levels.foldl (·.insert ·) a.levels }
      match e with
      | .const name _ =>
        if ti.isBinder then modify fun a => { a with defs := a.defs.insert name }
        else
          modify fun a => { a with uses := a.uses.insert name }
          if ti.stx.isIdent || ti.stx.getKind == ``Parser.Term.dotIdent ||
              ti.stx.getKind == Parser.Term.identProjKind then
            modify fun a => { a with named := a.named.insert name }
            record ctx ti.lctx ti.stx name
      | e => modify fun a => { a with uses := e.foldConsts a.uses fun c s => s.insert c }
    | .ofFieldInfo fi => if inside then modify fun a => { a with uses := a.uses.insert fi.projName }
    -- what a tactic assigned the goals it was given, which a branch that then failed keeps here
    -- though not in the term
    | .ofTacticInfo ti =>
      if inside then
        for g in ti.goalsBefore do
          if let some v := ti.mctxAfter.getExprAssignmentCore? g then
            modify fun a => { a with uses := v.foldConsts a.uses fun c s => s.insert c }
    | .ofMacroExpansionInfo mi =>
      if !inside then modify fun a => { a with expanded := a.expanded.push mi.output }
      if inside then
        modify fun a => { a with attrs := attributes mi.output a.attrs,
                                 expanded := a.expanded.push mi.output }
    | _ => pure ()
    if inside then
      if let some ei := info.toElabInfo? then
        unless ei.elaborator.isAnonymous do
          modify fun a => { a with uses := a.uses.insert ei.elaborator }
    return true

/-- constants lean hands to whichever later command asks for the same thing: auxiliary lemmas it
caches by statement, match compilers it caches by shape along with the equations and splitters
it derives from them, and sparse case splits it caches by constructor set. a command that reuses
one depends on what it is made of, not on the declaration that happened to create it first,
which lean would recreate for it were that declaration gone -/
def cached (env : Environment) : NameSet :=
  (Meta.auxLemmasExt.getState env).lemmas.foldl (fun acc _ (n, _) => acc.insert n) {}

def isShared (env : Environment) (lemmas : NameSet) (name : Name) : Bool :=
  lemmas.contains name || Meta.isMatcherCore env name ||
  Meta.isMatcherCore env (privateToUserName? name.getPrefix |>.getD name.getPrefix) ||
  isSparseCasesOn env name

/-- what the constants a command added refer to, through their finished types and values.
elaboration can leave a dependency there that no source identifier stands for, such as an
instance it inserted or a lemma a tactic found by itself, and it can put a proof in an auxiliary
constant of its own, so every constant new to this command is followed, not only the named ones,
and so is every shared constant it reused -/
partial def finished (before env : Environment) (lemmas : NameSet) (name : Name) (seen : NameSet) :
    NameSet :=
  if seen.contains name then seen
  else if before.contains name && !isShared before lemmas name then seen.insert name else
  match env.find? name with
  | none => seen.insert name
  | some ci =>
    let refs := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map
      Expr.getUsedConstants |>.getD #[])
    refs.foldl (fun acc c => finished before env lemmas c acc) (seen.insert name)

/-- a name as lean prints it, up to where the line goes on, reading through `«»` quotes -/
partial def spell : List Char → Bool → List Char → List Char × List Char
  | [], _, acc => (acc.reverse, [])
  | c :: cs, quoted, acc =>
    if quoted then spell cs (c != '»') (c :: acc)
    else if c == '«' then spell cs true (c :: acc)
    else if c.isWhitespace || c == ':' || c == ',' then (acc.reverse, c :: cs)
    else spell cs false (c :: acc)

/-- the name a printed one stands for, component by component: a quoted one as its contents, and
one that is all digits as the number it is, as in the names hygiene gives what a macro declares -/
def parse (cs : List Char) : Name := Id.run do
  let mut name := Name.anonymous
  let mut part : List Char := []
  let mut quoted := false
  for c in cs ++ ['.'] do
    if quoted then
      if c == '»' then quoted := false else part := part ++ [c]
    else if c == '«' then quoted := true
    else if c == '.' then
      let text := String.mk part
      name := if !part.isEmpty && part.all Char.isDigit then .num name text.toNat! else .str name text
      part := []
    else part := part ++ [c]
  return name.replacePrefix `_root_ .anonymous

def spelled (text : String) : Name × List Char :=
  let (name, rest) := spell text.toList false []
  (if name.isEmpty then .anonymous else parse name, rest)

/-- what one message says elaboration used, all of it fully qualified since `pp.fullNames` is
set for the run:
* simp's rewrite trace names every lemma it rewrote with, including those that vanish from the
  term because they hold by `rfl`. one it tried and turned down is traced too, with a reason
  after a comma where a used one has its result after a colon
* the diagnostics simp reports list the lemmas and simprocs it used
* the unification hint trace names each hint that matched
* norm_num's trace names each extension that evaluated something, and says `failed` otherwise
* the diagnostics type class search reports list every instance it tried, which is the only
  record of an instance that elaboration then unfolds away, as it does coercions -/
def evidence (text : String) (used tried : NameSet) : NameSet × NameSet := Id.run do
  let mut used := used
  let mut tried := tried
  for piece in text.splitOn "[Meta.Tactic.simp.rewrite] " |>.drop 1 do
    let unfolded := piece.startsWith "unfold "
    let piece := if unfolded then piece.drop 7 else piece
    let piece := toString (piece.dropWhile fun c => c == '←' || c == '↓' || c == ' ')
    let (name, rest) := spelled piece
    let rest := match rest with
      | ':' :: more => more.dropWhile Char.isDigit
      | more => more
    let rest := if rest.take 5 == ":perm".toList then rest.drop 5 else rest
    if !name.isAnonymous && (unfolded || rest.head? == some ':') then
      used := used.insert name
  let mut heading := ""
  for line in text.splitOn "\n" do
    let line := toString (line.dropWhile (· == ' '))
    if line.startsWith "[" && (line.splitOn " ↦ ").length > 1 then
      let (name, _) := spelled (toString ((line.dropWhile (· != ']')).drop 2))
      if heading == "[simp] used theorems" then used := used.insert name
      if heading == "[type_class] used instances" then tried := tried.insert name
    else if line.startsWith "[" && line.endsWith ":" then
      heading := toString ((toString (line.takeWhile (· != '('))).dropRightWhile (· == ' '))
    if line.startsWith "[Meta.isDefEq.hint] " && (line.splitOn " succeeded, applying").length > 1 then
      used := used.insert (spelled (toString (line.drop 20))).1
    -- what instance search applied, which simp and others can throw away with the rest of their
    -- state, while traces stay
    if line.startsWith "[Meta.synthInstance.apply] " then
      match (line.splitOn "apply ").drop 1 |>.head? with
      | some rest =>
        let rest := if rest.startsWith "@" then rest.drop 1 else rest
        tried := tried.insert (spelled (toString rest)).1
      | none => pure ()
    if line.startsWith "[Tactic.norm_num] " then
      let (name, rest) := spelled (toString (line.drop 18))
      if rest.head? == some ':' then used := used.insert name
  return (used.erase .anonymous, tried.erase .anonymous)

def shownAll (s : NameSet) : NameSet := s.toList.foldl (fun acc n => acc.insert (shown n)) {}

/-- the command inside a chain of `a in b in cmd`, and the scope commands wrapped around it -/
partial def unwrap (stx : Syntax) (outer : Array Syntax := #[]) : Syntax × Array Syntax :=
  if stx.getKind == `Lean.Parser.Command.in then unwrap stx[2] (outer.push stx[0]) else (stx, outer)

/-- every `open ... in` a command's terms and tactics contain, as a command of its own -/
partial def inner (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  let acc := if stx.getKind == `Lean.Parser.Term.open || stx.getKind == `Lean.Parser.Tactic.open
    then acc.push (Syntax.node .none `Lean.Parser.Command.open #[stx[0], stx[1]]) else acc
  stx.getArgs.foldl (fun acc arg => inner arg acc) acc

/-- every `open ... in` inside a command's terms and tactics, as a command of its own, with the bytes
of what it wraps -/
partial def wrapping (stx : Syntax) (acc : Array (Syntax × Nat × Nat) := #[]) :
    Array (Syntax × Nat × Nat) :=
  let acc := if stx.getKind == `Lean.Parser.Term.open || stx.getKind == `Lean.Parser.Tactic.open then
      match stx[3].getPos?, stx[3].getTailPos? with
      | some lo, some hi => acc.push
          (Syntax.node .none `Lean.Parser.Command.open #[stx[0], stx[1]], lo.byteIdx, hi.byteIdx)
      | _, _ => acc
    else acc
  stx.getArgs.foldl (fun acc arg => wrapping arg acc) acc

/-- the namespaces named in every `open scoped` a command contains, which switch on what is scoped
to them without adding anything lean records as opened -/
partial def scopedIds (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  let acc := if stx.getKind == ``Parser.Command.openScoped then acc ++ stx[1].getArgs else acc
  stx.getArgs.foldl (fun acc arg => scopedIds arg acc) acc

/-- every namespace an `open` names, as written -/
partial def namespaceIds (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  let k := stx.getKind
  let acc := if k == ``Parser.Command.openSimple then acc ++ stx[0].getArgs
    else if k == ``Parser.Command.openScoped then acc ++ stx[1].getArgs
    else if k == ``Parser.Command.openOnly || k == ``Parser.Command.openHiding
      || k == ``Parser.Command.openRenaming then acc.push stx[0]
    else if k == ``Parser.Command.export then acc.push stx[1]
    else acc
  stx.getArgs.foldl (fun acc arg => namespaceIds arg acc) acc

/-- every name an `export`, `open ... (...)`, `open ... renaming` or `open ... hiding` takes from a
namespace, beside the namespace as written -/
partial def members (stx : Syntax) (acc : Array (Syntax × Syntax) := #[]) :
    Array (Syntax × Syntax) :=
  let k := stx.getKind
  let acc := if k == ``Parser.Command.export then acc ++ stx[3].getArgs.map (stx[1], ·)
    else if k == ``Parser.Command.openOnly || k == ``Parser.Command.openHiding then
      acc ++ stx[2].getArgs.map (stx[0], ·)
    else if k == ``Parser.Command.openRenaming then
      acc ++ stx[2].getSepArgs.map (stx[0], ·[0])
    else acc
  stx.getArgs.foldl (fun acc arg => members arg acc) acc

structure Opened where
  own : List Name
  introduced : Array OpenDecl
  scopedIn : Array Name
  routes : Array (String × Nat)
  through : Array (Name × String × Nat)
  vars : List Name
  wrapped : Command.Scope

/-- what a command opens: the namespaces only this file declares, as lean resolved them, whether it
opens anything besides, what it puts in effect, and which `open` already in effect each namespace
it names needs to resolve. a plain `open` leaves its declarations in the scope; the scope commands
of an `in` chain are undone once their command is elaborated, and so is an `open ... in` inside a
term or tactic, so those are elaborated again here and the state put back -/
def opened (header : Environment) (scope : Command.Scope) (stx : Syntax) : FrontendM Opened := do
  let before := scope.openDecls
  let (cmd, outer) := unwrap stx
  let saved ← get
  let mut routes := #[]
  let mut through := #[]
  let mut safe : List Name := []
  for id in namespaceIds stx do
    let base ← runCommandElabM do try resolveNamespace ⟨id⟩ catch _ => pure []
    -- the namespace the current one leads to comes first and alone, so one the file declares
    -- there must stay declared, or the name falls through to another
    let env := saved.commandState.env
    let throughScope := ResolveName.resolveNamespaceUsingScope? env id.getId scope.currNamespace
    if base.any header.isNamespace then safe := safe ++ base.filter (some · != throughScope)
    for d in before.eraseDups do
      let alt ← runCommandElabM do
        Command.modifyScope fun sc => { sc with openDecls := sc.openDecls.filter (· != d) }
        try resolveNamespace ⟨id⟩ catch _ => pure []
      set saved
      -- without `d` the namespace would not resolve at all, or would resolve to fewer, which only
      -- matters to what is then used through those
      let key := (s!"open {d}", (before.filter (· == d)).length)
      if alt.isEmpty && !base.isEmpty then routes := routes.push key
      else for ns in base.filter (!alt.contains ·) do through := through.push (ns, key)
  -- a name taken from a namespace may be there only as an alias an earlier `export` made
  for (space, member) in members stx do
    let spaces ← runCommandElabM do try resolveNamespace ⟨space⟩ catch _ => pure []
    let env := (← get).commandState.env
    for ns in spaces do
      let full := ns ++ member.getId
      if !env.contains full && ((getAliasState env).find? full).isSome then
        routes := routes.push (s!"alias {full}", 1)
  for wrapper in outer ++ inner cmd do
    runCommandElabM (Command.elabCommand wrapper)
  let wrapped := (← get).commandState.scopes.head!
  let after := wrapped.openDecls
  -- the section variables an `include` or `omit` it is wrapped in names
  let vars := (wrapped.includedVars.filter (!scope.includedVars.contains ·)) ++
    (wrapped.omittedVars.filter (!scope.omittedVars.contains ·))
  let mut named := #[]
  for id in scopedIds stx do
    named := named ++ (← runCommandElabM do
      try resolveNamespace ⟨id⟩ catch _ => pure [])
  set saved
  let fresh := after.take (after.length - before.length)
  -- a namespace only this file declares must stay declared before it, unless the same name also
  -- resolves to one imported, so the `open` cannot fail
  let own := fresh.filterMap fun
    | .simple ns _ => if header.isNamespace ns || safe.contains ns then none else some ns
    | .explicit .. => none
  let also := named.toList.filter fun ns => !header.isNamespace ns && !safe.contains ns
  return { own := own ++ also, routes, through, introduced := fresh.toArray, scopedIn := named, vars,
           wrapped }

/-- the keys a persistent map has gained or changed since an earlier version of it. the two share
every part neither changed, so only the parts whose pointers differ are walked -/
unsafe def changed (a b : PersistentHashMap.Node Name ConstantInfo) (acc : Array Name) :
    Array Name := Id.run do
  if ptrAddrUnsafe a == ptrAddrUnsafe b then return acc
  match b with
  | .collision ks _ _ => return acc ++ ks
  | .entries es =>
    let old : Array (PersistentHashMap.Entry Name ConstantInfo
        (PersistentHashMap.Node Name ConstantInfo)) := match a with
      | .entries es => es
      | .collision .. => #[]
    let mut acc := acc
    for i in [0:es.size] do
      let e := es[i]!
      if let some o := old[i]? then
        if ptrAddrUnsafe o == ptrAddrUnsafe e then continue
      match e, old[i]? with
      | .entry k _, _ => acc := acc.push k
      | .ref n, some (.ref m) => acc := changed m n acc
      | .ref n, _ => acc := changed (.entries #[]) n acc
      | .null, _ => pure ()
    return acc

/-- the names of the binders a declaration writes before its type, in order, with none for one it
leaves unnamed -/
def ownBinders (cmd : Syntax) : List (Option Name) := Id.run do
  let some sig := cmd[1].getArgs.find? fun a =>
      a.getKind == ``Parser.Command.declSig || a.getKind == ``Parser.Command.optDeclSig
    | return []
  let name (i : Syntax) : Option Name :=
    if i.isIdent && !i.getId.hasMacroScopes then some i.getId else none
  let one (b : Syntax) : List (Option Name) :=
    if b.getKind == ``Parser.Term.instBinder then [if b[1].isNone then none else name b[1][0]]
    else if [``Parser.Term.explicitBinder, ``Parser.Term.implicitBinder,
        ``Parser.Term.strictImplicitBinder].contains b.getKind then b[1].getArgs.toList.map name
    else [name b]
  return sig[0].getArgs.toList.flatMap one

/-- the section variables, by their unique ids, that a command took in. lean elaborates them
afresh for every command, as is done here once more: a declaration's type opens with the ones it
took in, in the order they were declared, so they are matched against those binders by type, and
by name where they have one. a `variable` command takes in those its own binders mention -/
def sectionVars (decls : List (ConstantInfo × List (Option Name))) (fresh : List Name)
    (wrapped : Command.Scope) : FrontendM (List Name × List Name) := do
  let saved ← get
  -- the variables are those in effect for the command, inside whatever `in` chain it comes in
  modify fun st => { st with commandState.scopes := wrapped :: st.commandState.scopes.tail }
  let taken ← runCommandElabM <| Command.runTermElabM fun xs => do
    let mut byFVar : NameMap Name := {}
    for (u, x) in (← read).sectionFVars do
      byFVar := byFVar.insert x.fvarId!.name u
    let uid (x : Expr) := byFVar.find? x.fvarId!.name
    let mut taken : List Name := []
    let mut alone : List Name := []
    for x in xs do
      if let some u := uid x then
        if fresh.contains u then
          let used := (CollectFVars.main (← Meta.inferType x) {}).fvarIds
          taken := taken ++ used.toList.filterMap (byFVar.find? ·.name)
    for (ci, own) in decls do
      let mut ty : Expr ← instantiateMVars ci.type
      let mut j := 0
      let us ← ci.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
      ty := ty.instantiateLevelParams ci.levelParams us
      -- the binders the declaration writes come after those it took in, so those end where the
      -- declaration's own first appear
      -- one it leaves unnamed gets a name hygiene makes, and where that leaves the place they start
      -- open, the latest place is taken, which can only take in more
      let names := (ty.getForallBinderNames).toArray
      let fits (q : Nat) := own.length + q ≤ names.size && (own.zipIdx.all fun (o, i) =>
        match o with
        | some o => o == names[q + i]!
        | none => names[q + i]!.hasMacroScopes)
      let fitting := (List.range (names.size + 1)).filter fits
      let limit := if own.isEmpty then names.size
        else if own.any (·.isNone) then fitting.getLast?.getD names.size
        else fitting.head?.getD names.size
      let mut matched := 0
      let mut picked : List Expr := []
      while ty.isForall && j < xs.size && matched < limit do
        let .forallE n t b bi := ty | break
        let mut found := none
        -- of two with one name, the one declared last is the one the name means. those without
        -- one are taken in the order they were declared
        let order := if n.hasMacroScopes then List.range' j (xs.size - j)
          else (List.range' j (xs.size - j)).reverse
        for k in order do
          let x := xs[k]!
          let decl ← x.fvarId!.getDecl
          if decl.binderInfo != bi then continue
          if !decl.userName.hasMacroScopes && decl.userName != n then continue
          if ← Meta.isDefEq (← Meta.inferType x) t then
            found := some k
            break
        match found with
        | none => break
        | some k =>
          if let some u := uid xs[k]! then taken := u :: taken
          picked := xs[k]! :: picked
          ty := b.instantiate1 xs[k]!
          j := k + 1
          matched := matched + 1
      -- one that nothing else it took in mentions, nor what it then states, was taken in only
      -- because an `include` said so
      for x in picked do
        let others ← picked.filterM fun y => do
          return y != x && !(← y.fvarId!.getDecl).binderInfo.isInstImplicit &&
            (← Meta.inferType y).containsFVar x.fvarId!
        if others.isEmpty && !ty.containsFVar x.fvarId! then
          if let some u := uid x then alone := u :: alone
    return (taken, alone)
  set saved
  return taken

/-- a name and every name it is made under -/
partial def prefixesOf (n : Name) : List Name :=
  if n.isAnonymous then [] else n :: prefixesOf n.getPrefix

/-- every identifier a piece of syntax is written with -/
partial def idents (stx : Syntax) (acc : NameSet := {}) : NameSet :=
  let acc := if stx.isIdent then acc.insert stx.getId.eraseMacroScopes else acc
  stx.getArgs.foldl (fun acc a => idents a acc) acc

/-- the section variables of a scope by unique id, each with the name it was declared under and the
binder that declares it, one binder declaring several -/
def binders (scope : Command.Scope) : FrontendM (Array (Name × Name × Syntax)) := do
  let saved ← get
  let ids ← runCommandElabM do
    let mut ids := #[]
    for b in scope.varDecls do
      ids := ids ++ (← Command.getBracketedBinderIds b).map (·, b.raw)
    return ids
  set saved
  return (scope.varUIds.zip ids).map fun (u, (n, b)) => (u, n, b)

/-- the extensions of lean's environment, across every toolchain this is run with, through which a
command can be deleted, each read from the code that reads it:
* those whose every use by a later command is recorded: by a constant in the terms it leaves, by
  simp's rewrite trace, by the instances type class search tried, by the unification hint and
  `norm_num` traces, by the syntax kinds and elaborators a command is written with, or by name
  resolution
* those that only describe the constants of the declaration that adds to them, so a later command
  affected by them uses those constants
* those that cannot change whether a later command elaborates: documentation, linting, printing,
  statistics, the editor
an extension anywhere else, such as one whose entries a tactic runs or searches with and leaves no
record of, as simprocs outside simp itself, `grind`'s theorems, aesop's rules, `positivity`'s
extensions and `csimp` do, keeps any command that adds to it, and so does one this list has never
seen -/
def accounted : List String := [
  "Batteries.CodeAction.tacticCodeActionExt", "Batteries.CodeAction.tacticSeqCodeActionExt",
  "Batteries.Linter.UnnecessarySeqFocus.multigoalAttr", "Batteries.Tactic.Alias.aliasExt",
  "Batteries.Tactic.Lint.batteriesLinterExt", "Batteries.Tactic.transExt",
  "Batteries.machineApplicableDeprecated", "Lean.Attr.algebraizeAttr",
  "Lean.CodeAction.cmdCodeActionExt", "Lean.CodeAction.holeCodeActionExt",
  "Lean.Compiler.LCNF.Specialize.specCacheExt",
  "Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt", "Lean.Compiler.LCNF.baseExt",
  "Lean.Compiler.LCNF.impureSigExt", "Lean.Compiler.LCNF.monoExt",
  "Lean.Compiler.LCNF.monoTypeExt", "Lean.Compiler.LCNF.postponedCompileDeclsExt",
  "Lean.Compiler.LCNF.specExtension", "Lean.Compiler.LCNF.taggedReturnAttr",
  "Lean.Compiler.implementedByAttr", "Lean.Compiler.inlineAttrs",
  "Lean.Compiler.nospecializeAttr", "Lean.Compiler.specializeAttr",
  "Lean.Compiler.weakSpecializeAttr", "Lean.Doc.DeferredCheck.handlerExt",
  "Lean.Doc.deferredCheckExt", "Lean.Elab.Command.commandElabAttribute",
  "Lean.Elab.ComputedFields.computedFieldAttr", "Lean.Elab.Do.doElemElabAttribute",
  "Lean.Elab.PartialFixpoint.eqnInfoExt", "Lean.Elab.Structural.eqnInfoExt",
  "Lean.Elab.Tactic.BVDecide.Frontend.bvNormalizeExt",
  "Lean.Elab.Tactic.BVDecide.Frontend.intToBitVecExt",
  "Lean.Elab.Tactic.Do.SpecAttr.mvcgenSimpExt", "Lean.Elab.Tactic.Grind.grindAnnotatedExt",
  "Lean.Elab.Tactic.Grind.grindTacElabAttribute", "Lean.Elab.Tactic.Omega.bitvec_to_nat",
  "Lean.Elab.Tactic.Omega.bvOmegaSimpExtension", "Lean.Elab.Tactic.noFallbackAttr",
  "Lean.Elab.Tactic.tacticElabAttribute", "Lean.Elab.Term.elabAsElim",
  "Lean.Elab.Term.elabWithoutExpectedTypeAttr", "Lean.Elab.Term.termElabAttribute",
  "Lean.Elab.WF.eqnInfoExt", "Lean.Elab.WF.wfPreprocessSimpExtension",
  "Lean.Elab.deprecatedArgExt", "Lean.Elab.incrementalAttr", "Lean.Elab.macroAttribute",
  "Lean.IR.ToIR.taggedReturnAttr", "Lean.IR.UnboxResult.unboxAttr",
  "Lean.IR.UnreachableBranches.functionSummariesExt", "Lean.IR.declMapExt",
  "Lean.LibrarySuggestions.librarySuggestionsAttr", "Lean.Linter.deprecatedAttr",
  "Lean.Linter.lintLogExt", "Lean.Meta.Grind.casesExt", "Lean.Meta.Grind.normExt",
  "Lean.Meta.Match.Extension.extension", "Lean.Meta.Monotonicity.monotoneExt",
  "Lean.Meta.NormCast.normCastExt.down", "Lean.Meta.NormCast.normCastExt.squash",
  "Lean.Meta.NormCast.normCastExt.up", "Lean.Meta.NormCast.pushCastExt", "Lean.Meta.Rfl.reflExt",
  "Lean.Meta.Sym.Simp.symSimpExtension", "Lean.Meta.Symm.symmExt",
  "Lean.Meta.Tactic.BVDecide.bvNormalizeExt", "Lean.Meta.Tactic.BVDecide.intToBitVecExt",
  "Lean.Meta.Tactic.BVDecide.metaIntToBitVecExt", "Lean.Meta.coeDeclAttr", "Lean.Meta.coeExt",
  "Lean.Meta.completionBlackListExt", "Lean.Meta.congrKindsExt", "Lean.Meta.customEliminatorExt",
  "Lean.Meta.Ext.extExtension",
  "Lean.Meta.eqnOptionsExt", "Lean.Meta.funIndInfoExt", "Lean.Meta.globalInstanceExtension",
  "Lean.Meta.instanceExtension", "Lean.Meta.matcherLikeExt", "Lean.Meta.recursorAttribute",
  "Lean.Meta.sevalSimpExtension", "Lean.Meta.simpExtension", "Lean.Meta.unificationHintExtension",
  "Lean.Parser.Tactic.Doc.tacticAlternativeExt", "Lean.Parser.parserExtension",
  "Lean.Server.codeActionProviderExt", "Lean.aliasExtension", "Lean.auxParentProjInfoExt",
  "Lean.auxRecExt", "Lean.backwardDefeqAttr", "Lean.bool_to_prop", "Lean.builtinInitAttr",
  "Lean.classExtension", "Lean.declRangeExt", "Lean.defeqAttr", "Lean.docStringExt",
  "Lean.exportAttr", "Lean.externAttr", "Lean.extraModUses",
  "Lean.identifierSuggestForAttr.existingToIncorrect", "Lean.indirectModUseExt",
  "Lean.isExtraRevModUseExt", "Lean.metaExt", "Lean.methodSpecsAttr", "Lean.namespacesExt",
  "Lean.neverExtractAttr", "Lean.noConfusionExt", "Lean.noncomputableExt", "Lean.ppNoDotAttr",
  "Lean.ppUsingAnonymousConstructorAttr", "Lean.projectionFnInfoExt", "Lean.protectedExt",
  "Lean.regularInitAttr", "Lean.versoDocStringExt", "Mathlib.Command.Variable.variableAliasAttr",
  "Mathlib.Meta.FunProp.funPropDeclsExt", "Mathlib.Meta.FunProp.functionTheoremsExt",
  "Mathlib.Meta.FunProp.lambdaTheoremsExt", "Mathlib.Meta.FunProp.morTheoremsExt",
  "Mathlib.Meta.FunProp.transitionTheoremsExt", "Mathlib.Meta.NormNum.normNumExt",
  "Mathlib.Tactic.GCongr.gcongrExt", "Mathlib.Tactic.Polynomial.polynomialPostExt",
  "Mathlib.Tactic.Polynomial.polynomialPreExt", "Mathlib.Tactic.Push.pullExt",
  "Mathlib.Tactic.Push.pushExt", "Mathlib.Tactic.ToAdditive.argInfoAttr",
  "Mathlib.Tactic.ToAdditive.doTranslateAttr", "Mathlib.Tactic.ToAdditive.ignoreArgsAttr",
  "Mathlib.Tactic.ToDual.doTranslateAttr", "Mathlib.Tactic.ToDual.ignoreArgsAttr",
  "Mathlib.Tactic.Translate.changeNumeralAttr", "Mathlib.Tactic.higherOrderAttr",
  "ProofWidgets.exprPresenters", "Std.Internal.treeTacExt", "Tactic.higherOrderAttr",
  "ToAdditive.changeNumeralAttr", "ToAdditive.dontTranslateAttr", "ToAdditive.ignoreArgsAttr",
  "ToAdditive.relevantArgAttr", "ToAdditive.reorderAttr",
  "_private.Batteries.Util.ProofWanted.0.wantedArityExt",
  "_private.Batteries.Util.ProofWanted.0.wantedInstancesExt",
  "_private.Lean.AddDecl.0.Lean.privateConstKindsExt",
  "_private.Lean.AuxRecursor.0.Lean.sparseCasesOnExt",
  "_private.Lean.Compiler.LCNF.MonoTypes.0.Lean.Compiler.LCNF.trivialStructureInfoExt",
  "_private.Lean.Compiler.LCNF.Specialize.0.Lean.Compiler.LCNF.Specialize.specCacheExt",
  "_private.Lean.Compiler.LCNF.ToImpure.0.Lean.Compiler.LCNF.taggedReturnAttr",
  "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.ctorLayoutExt",
  "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTrivialStructureInfoExt",
  "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTypeExt",
  "_private.Lean.Compiler.MetaAttr.0.Lean.declMetaExt",
  "_private.Lean.Compiler.MetaAttr.0.Lean.metaExt",
  "_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt",
  "_private.Lean.DocString.Extension.0.Lean.inheritDocStringExt",
  "_private.Lean.Elab.Tactic.Grind.Annotated.0.Lean.Elab.Tactic.Grind.grindAnnotatedExt",
  "_private.Lean.ExtraModUses.0.Lean.extraModUses",
  "_private.Lean.ExtraModUses.0.Lean.isExtraRevModUseExt",
  "_private.Lean.Meta.Constructions.SparseCasesOn.0.Lean.Meta.sparseCasesOnInfoExt",
  "_private.Lean.Meta.MethodSpecs.0.Lean.methodSpecsAttr",
  "_private.Lean.Meta.Tactic.Grind.EMatchTheorem.0.Lean.Meta.Grind.symbolPrioExt",
  "_private.Lean.Namespace.0.Lean.namespacesExt",
  "_private.Lean.OriginalConstKind.0.Lean.privateConstKindsExt",
  "_private.Lean.Structure.0.Lean.structureExt",
  "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt",
  "_private.Lean.Widget.UserWidget.0.Lean.Widget.panelWidgetsExt", "aesop_Bound",
  "aesop_CStarAlgebra", "aesop_CategoryTheory", "aesop_Continuous", "aesop_IsMultiplicative",
  "aesop_Matroid", "aesop_Measurable", "aesop_Restrict", "aesop_SetLike", "aesop_SetLike!",
  "aesop_SimpleGraph", "aesop_Sym2", "aesop_builtin", "aesop_default", "aesop_finiteness",
  "aesop_finsetNonempty", "boolToPropSimps", "bool_to_prop", "enat_to_nat_coe", "enat_to_nat_top",
  "envLinterSnapshotExt", "eqnsAttribute",
  "ext._@.Mathlib.Tactic.Attr.Register.1086225606._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.1131139975._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.1133190711._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.1503578496._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.1568842782._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.1988518680._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.2016062075._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.2133673922._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.2336186397._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.2552594532._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.2899626838._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.3021440532._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.3059584346._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.3215534580._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.3369699945._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.3849875863._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.479538640._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.612238087._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.668879677._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.Attr.Register.85691930._hygCtx._hyg.3", "fin_omega", "functor_norm",
  "ghost_simps", "integral_simps", "is_poly", "mfld_simps", "mon_tauto", "monad_norm", "mono",
  "nontriviality", "parity_simps", "pnat_to_nat_coe", "qify_simps", "rclike_simps", "recExt",
  "reduceModCharExt", "reducibilityCore", "rify_simps", "simpsAttr", "sineQueNon",
  "symbolFrequency", "treeTacExt", "typevec", "zify_simps"]

/-- the extensions that record where things are and which modules they came from, which nothing that
is elaborated reads -/
def bookkeeping : List String := [
  "Lean.declRangeExt", "Lean.extraModUses", "_private.Lean.ExtraModUses.0.Lean.extraModUses",
  "Lean.isExtraRevModUseExt", "_private.Lean.ExtraModUses.0.Lean.isExtraRevModUseExt",
  "Lean.indirectModUseExt"]

/-- the extensions that change only what lean says: how terms and syntax print, what linters warn,
what reporting commands list. nothing depends on them unless the file compares what lean says, with
`#guard_msgs` or `#guard_panic`, or turns warnings into errors -/
def observable : List String := [
  "Aesop.statsExtension", "Batteries.Util.LibraryNote.libraryNoteExt",
  "Lean.Doc.codeBlockSuggestionExt", "Lean.Doc.codeSuggestionExt", "Lean.Doc.docBlockMdExt",
  "Lean.Doc.docInlineMdExt", "Lean.Elab.Command.assertExistsExt",
  "Lean.Elab.Tactic.Grind.muteExt", "Lean.Elab.deprecatedSyntaxExt",
  "Lean.Linter.MissingDocs.missingDocsExt", "Lean.Linter.unusedVariablesIgnoreFnsExt",
  "Lean.Parser.Tactic.Doc.tacticDocExtExt", "Lean.Parser.Tactic.Doc.tacticTagExt",
  "Lean.Parser.Term.Doc.recommendedSpellingByNameExt",
  "Lean.Parser.Term.Doc.recommendedSpellingExt",
  "Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute",
  "Lean.PrettyPrinter.Delaborator.delabAttribute",
  "Lean.PrettyPrinter.categoryParenthesizerAttribute", "Lean.PrettyPrinter.formatterAttribute",
  "Lean.PrettyPrinter.mkCombinatorFormatterAttribute",
  "Lean.PrettyPrinter.mkCombinatorParenthesizerAttribute",
  "Lean.PrettyPrinter.parenthesizerAttribute", "Lean.deprecatedModuleExt",
  "Lean.identifierSuggestForAttr.incorrectToExisting", "Lean.matchPatternAttr",
  "Mathlib.AssertNotExist.assertExistsExt", "Mathlib.CrossRef.tagExt",
  "Mathlib.Linter.UnusedTactic.allowedUnusedTacticExt", "Mathlib.Linter.deprecatedModuleExt",
  "Mathlib.StacksTag.tagExt", "_private.Lean.DocString.Extension.0.Lean.moduleDocExt",
  "_private.Lean.Elab.Tactic.Grind.Lint.0.Lean.Elab.Tactic.Grind.skipSuffixExt"]

/-- the extensions read and found to leave no record of a later command's use, so anything a command
adds to them keeps it -/
def unrecorded : List String := [
  "Batteries.Tactic.Lint.nolintAttr", "Bound", "CStarAlgebra", "CategoryTheory", "Continuous",
  "IsMultiplicative", "Lean.Compiler.CSimp.ext", "Lean.Compiler.LCNF.Simp.ConstantFold.folderExt",
  "Lean.Compiler.LCNF.passManagerExt", "Lean.Doc.docCodeBlockExt", "Lean.Doc.docCommandExt",
  "Lean.Doc.docDirectiveExt", "Lean.Doc.docRoleExt", "Lean.Elab.Command.inductiveElabAttr",
  "Lean.Elab.Do.controlInfoElemAttribute",
  "Lean.Elab.Tactic.BVDecide.Frontend.bvNormalizeSimprocExt",
  "Lean.Elab.Tactic.Do.Internal.VCGen.frameProcExt",
  "Lean.Elab.Tactic.Do.SpecAttr.specInvariantAttr", "Lean.Elab.Tactic.Grind.skipExt",
  "Lean.Elab.Tactic.Grind.skipSuffixExt", "Lean.Elab.Tactic.Grind.symDSimprocElabAttribute",
  "Lean.Elab.Tactic.Grind.symDischargerElabAttribute",
  "Lean.Elab.Tactic.Grind.symSimprocElabAttribute", "Lean.Elab.Tactic.Try.trySuggestionExtension",
  "Lean.Elab.Tactic.Try.tryTacticElabAttribute", "Lean.Elab.Term.Quotation.precheckAttribute",
  "Lean.LibrarySuggestions.SineQuaNon.triggerDenyListExt",
  "Lean.LibrarySuggestions.librarySuggestionsExt", "Lean.LibrarySuggestions.moduleDenyListExt",
  "Lean.LibrarySuggestions.nameDenyListExt", "Lean.LibrarySuggestions.typePrefixDenyListExt",
  "Lean.Linter.EnvLinter.envLinterExt", "Lean.Linter.linterSetsExt",
  "Lean.Meta.Grind.extTheoremsExt", "Lean.Meta.Grind.grindExt", "Lean.Meta.Grind.liaExt",
  "Lean.Meta.Simp.simprocDeclExt", "Lean.Meta.Simp.simprocExtension",
  "Lean.Meta.Simp.simprocSEvalExtension", "Lean.Meta.Tactic.BVDecide.bvNormalizeSimprocExt",
  "Lean.Meta.Tactic.BVDecide.symIntToBitVecExt", "Lean.Meta.Tactic.Cbv.cbvSimprocDeclExt",
  "Lean.Meta.congrExtension", "Lean.Meta.defaultInstanceExtension",
  "Lean.Parser.Tactic.Doc.knownTacticTagExt", "Lean.Parser.Tactic.Doc.tacticNameExt",
  "Lean.Server.userRpcProcedures", "Lean.attributeExtension", "Lean.errorExplanationExt",
  "Lean.methodSpecsSimpExtension", "Mathlib.Meta.Positivity.positivityExt",
  "Mathlib.Meta.SetNotationForOrder.setNotationExt", "Mathlib.Tactic.GCongr.forwardExt",
  "Mathlib.Tactic.Hint.hintExtension", "Mathlib.Tactic.Polynomial.polynomialExt",
  "Mathlib.Tactic.ToAdditive.translations", "Mathlib.Tactic.ToDual.argInfoAttr",
  "Mathlib.Tactic.ToDual.translations", "Mathlib.Tactic.UnfoldBoundary.registerUnfoldBoundaryExt",
  "Mathlib.TacticAnalysis.tacticAnalysisExt", "Matroid", "Measurable", "Restrict", "SetLike",
  "SetLike!", "SimpleGraph", "Simps.notationClassAttr", "Simps.structureExt", "Sym2",
  "ToAdditive.translations", "_private.Lean.DocString.Extension.0.Lean.versoModuleDocExt",
  "_private.Lean.Elab.Tactic.Grind.Lint.0.Lean.Elab.Tactic.Grind.muteExt",
  "_private.Lean.Elab.Tactic.Grind.Lint.0.Lean.Elab.Tactic.Grind.skipExt",
  "_private.Lean.LibrarySuggestions.SineQuaNon.0.Lean.LibrarySuggestions.SineQuaNon.triggerDenyListExt",
  "_private.Lean.Meta.MethodSpecs.0.Lean.methodSpecsSimpExtension",
  "_private.Lean.Meta.Tactic.Grind.EMatchTheorem.0.Lean.Meta.Grind.ematchTheoremsExt",
  "_private.Lean.Meta.Tactic.Grind.FunCC.0.Lean.Meta.Grind.funCCExt",
  "_private.Lean.Meta.Tactic.Grind.Injective.0.Lean.Meta.Grind.injectiveTheoremsExt",
  "_private.Lean.Widget.UserWidget.0.Lean.Widget.moduleRegistry", "aesop_Bound_proc",
  "aesop_CStarAlgebra_proc", "aesop_CategoryTheory_proc", "aesop_Continuous_proc",
  "aesop_IsMultiplicative_proc", "aesop_Matroid_proc", "aesop_Measurable_proc",
  "aesop_Restrict_proc", "aesop_SetLike!_proc", "aesop_SetLike_proc", "aesop_SimpleGraph_proc",
  "aesop_Sym2_proc", "aesop_builtin_proc", "aesop_default_proc", "aesop_finiteness_proc",
  "aesop_finsetNonempty_proc", "builtin", "cbvEvalExt", "cbvOpaqueExt", "cbvSimprocExt",
  "default", "enat_to_nat_coe_proc", "enat_to_nat_top_proc",
  "ext._@.Mathlib.Tactic.GrindAttrs.2614774725._hygCtx._hyg.3",
  "ext._@.Mathlib.Tactic.GrindAttrs.943899233._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.1086225606._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.1131139975._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.1133190711._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.1503578496._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.1568842782._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.1988518680._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.2016062075._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.2133673922._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.2336186397._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.2552594532._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.2899626838._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.3021440532._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.3059584346._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.3215534580._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.3369699945._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.3849875863._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.479538640._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.612238087._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.668879677._hygCtx._hyg.3",
  "extProc._@.Mathlib.Tactic.Attr.Register.85691930._hygCtx._hyg.3", "fieldSimpExt",
  "fin_omega_proc", "finiteness", "finsetNonempty", "functor_norm_proc", "ghost_simps_proc",
  "integral_simps_proc", "internalSpecMap", "mfld_simps_proc", "mon_tauto_proc",
  "monad_norm_proc", "nontriviality_proc", "parity_simps_proc", "pnat_to_nat_coe_proc",
  "qify_simps_proc", "rclike_simps_proc", "reducibilityExtra", "rify_simps_proc", "specMap",
  "symDSimpVariantExtension", "symSimpVariantExtension", "typevec_proc", "zify_simps_proc"]

/-- whether any persistent extension's state changed at all, scoped ones switched on by an `open`
included. the others are caches lean fills again when asked -/
unsafe def touched (before env : Environment) : IO Bool := do
  for ext in (← persistentEnvExtensionsRef.get) do
    let a := (ext.toEnvExtension.getState before).state
    let b := (ext.toEnvExtension.getState env).state
    if ptrAddrUnsafe a != ptrAddrUnsafe b then return true
  return false

/-- the extensions a command added to. a scoped one changes whenever a namespace is opened, so for
those, unless the command opened one or a scope, only the entries it added count -/
unsafe def added (before env : Environment) (activates : Bool) : IO (Array Name) := do
  let mut scopedNames : NameSet := {}
  let mut out := #[]
  for ext in (← scopedEnvExtensionsRef.get) do
    scopedNames := scopedNames.insert ext.ext.name
    let a := ext.ext.getState before
    let b := ext.ext.getState env
    -- an entry only for the current scope, as a `local` attribute adds, changes that scope's state
    -- and nothing else, as switching on what is scoped to a namespace does too
    let scopeOnly := !activates && match a.stateStack, b.stateStack with
      | x :: _, y :: _ => ptrAddrUnsafe x != ptrAddrUnsafe y
      | _, _ => false
    if ptrAddrUnsafe a.newEntries != ptrAddrUnsafe b.newEntries || scopeOnly then
      out := out.push ext.ext.name
  for ext in (← persistentEnvExtensionsRef.get) do
    unless scopedNames.contains ext.name do
      let a := (ext.toEnvExtension.getState before).state
      let b := (ext.toEnvExtension.getState env).state
      -- the compiler's constant folders keep their entries beside a table of all folders, so only
      -- the entries say whether a command added one
      let folders := Compiler.LCNF.Simp.ConstantFold.folderExt
      let differs := if ext.name == folders.name then
          ptrAddrUnsafe (folders.getState before).1 != ptrAddrUnsafe (folders.getState env).1
        else ptrAddrUnsafe a != ptrAddrUnsafe b
      if differs then out := out.push ext.name
  return out

/-- whether a command added to what only its own scope sees, as a `local` attribute, instance or
notation does, or switched on what is scoped to a namespace -/
unsafe def addedLocally (before env : Environment) : IO Bool := do
  for ext in (← scopedEnvExtensionsRef.get) do
    let a := ext.ext.getState before
    let b := ext.ext.getState env
    if ptrAddrUnsafe a.newEntries == ptrAddrUnsafe b.newEntries then
      match a.stateStack, b.stateStack with
      | x :: _, y :: _ => if ptrAddrUnsafe x != ptrAddrUnsafe y then return true
      | _, _ => pure ()
  return false

/-- whether a type can describe code that does IO: it is made of `IO.RealWorld` once the
definitions it is written with are unfolded, as `IO`, `CoreM`, `MetaM`, the elaborator monads and
the types of tactics, simprocs and elaborators all are -/
partial def worldly (env : Environment) (seen : NameSet) (e : Expr) : Bool × NameSet :=
  e.getUsedConstants.foldl (fun (found, seen) c =>
    if found || seen.contains c then (found, seen)
    else if c == ``IO.RealWorld then (true, seen)
    else match env.find? c with
      | some (.defnInfo d) =>
        -- only what builds a type is unfolded, as a monad is: its value says what the type is made
        -- of, where the value of anything else says nothing about the type it is in
        if d.type.getForallBody.isSort then worldly env (seen.insert c) d.value
        else (found, seen.insert c)
      | some (.inductInfo i) =>
        -- a structure holds what its fields hold, as an extension or a linter holds its code
        i.ctors.foldl (fun (found, seen) k => if found then (found, seen) else
          match env.find? k with
          | some ck => worldly env seen ck.type
          | none => (found, seen)) (worldly env (seen.insert c) i.type)
      | some _ => (found, seen.insert c)
      | none => (false, seen.insert c)) (false, seen)

/-- whether a constant is code that can do IO -/
def effectful (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some ci => ci.hasValue && (worldly env {} ci.type).1
  | none => false

/-- whether a constant is an instance of a class lean's coercions unfold, read off the `coe_decl`
marking of the class's fields. elaboration unfolds such an instance where it inserts it, so its
use can leave no constant in any term -/
def unfoldedAway (env : Environment) (n : Name) : Bool :=
  Meta.isInstanceCore env n && match env.find? n with
    | some ci => match ci.type.getForallBody.getAppFn.constName? with
      | some c => (getStructureFields env c).any fun f => Meta.isCoeDecl env (c ++ f)
      | none => false
    | none => false

/-- the constants the entries a command added to `grind`'s theorem sets are for, where they are for
one -/
def grindDecls (before env : Environment) : List (Option Name) := Id.run do
  let decl : Meta.Grind.Entry → Option Name
    | .ext n | .funCC n | .cases n _ => some n
    | .ematch t => match t.origin with | .decl n .. => some n | _ => none
    | .inj t => match t.origin with | .decl n .. => some n | _ => none
  let mut out := []
  for ext in [Meta.Grind.grindExt, Meta.Grind.liaExt] do
    let a := (ext.ext.getState before).newEntries
    let b := (ext.ext.getState env).newEntries
    for e in b.take (b.length - a.length) do
      out := (match e with | .global x => decl x | .«scoped» _ x => decl x) :: out
  return out

/-- the scoped extensions whose entries say by name what they put in place: instances, syntax,
macros and elaborators, and simp sets. a later command's use of any of those is recorded by that
name, in the instances it tried, the syntax kinds and elaborators it is written with, or simp's
trace -/
def introspected : IO NameSet := do
  let mut acc : NameSet := {}
  for n in [Meta.instanceExtension.ext.name, Parser.parserExtension.ext.name,
      macroAttribute.ext.ext.name, Term.termElabAttribute.ext.ext.name,
      Tactic.tacticElabAttribute.ext.ext.name, Command.commandElabAttribute.ext.ext.name] do
    acc := acc.insert n
  for (_, ext) in (← Meta.simpExtensionMapRef.get) do
    acc := acc.insert ext.ext.name
  return acc

def keyedNames {γ : Type} (ext : KeyedDeclsAttribute.Extension γ) (env : Environment) (ns : Name)
    (acc : NameSet) : NameSet :=
  match (ext.ext.getState env).scopedEntries.map.find? ns with
  | some es => es.foldl (fun acc e => (acc.insert e.key).insert e.declName) acc
  | none => acc

/-- the names of everything scoped to a namespace in those extensions, imported or declared here,
which opening the namespace switches on -/
def scopedNames (env : Environment) (ns : Name) : IO NameSet := do
  let mut acc : NameSet := {}
  if let some es := (Meta.instanceExtension.ext.getState env).scopedEntries.map.find? ns then
    acc := es.foldl (fun acc e => match e.globalName? with
      | some n => acc.insert n
      | none => acc) acc
  if let some es := (Parser.parserExtension.ext.getState env).scopedEntries.map.find? ns then
    acc := es.foldl (fun acc e => match e with
      | .kind k => acc.insert k
      | .parser _ d .. => acc.insert d
      | .category _ d _ => acc.insert d
      | .token _ => acc) acc
  acc := keyedNames macroAttribute.ext env ns acc
  acc := keyedNames Term.termElabAttribute.ext env ns acc
  acc := keyedNames Tactic.tacticElabAttribute.ext env ns acc
  acc := keyedNames Command.commandElabAttribute.ext env ns acc
  for (_, ext) in (← Meta.simpExtensionMapRef.get) do
    if let some es := (ext.ext.getState env).scopedEntries.map.find? ns then
      acc := es.foldl (fun acc e => match e with
        | .thm t => match t.origin with
          | .decl n .. => acc.insert n
          | _ => acc
        | .toUnfold n => acc.insert n
        | .toUnfoldThms n thms => thms.foldl (·.insert ·) (acc.insert n)) acc
  return acc

/-- the other scoped extensions with anything scoped to a namespace. opening it switches that on,
and no record says whether anything then used it -/
def foreignScoped (env : Environment) (ns : Name) (known : NameSet) : IO (Array Name) := do
  let mut out := #[]
  for ext in (← scopedEnvExtensionsRef.get) do
    if !known.contains ext.ext.name && (ext.ext.getState env).scopedEntries.map.contains ns then
      out := out.push ext.ext.name
  return out

/-- the namespaces a command scoped something to in those other extensions. lean switches such an
entry on at once in every scope where its namespace is open -/
def scopedTo (before env : Environment) (known : NameSet) : IO (Array Name) := do
  let mut out := #[]
  for ext in (← scopedEnvExtensionsRef.get) do
    unless known.contains ext.ext.name do
      let a := (ext.ext.getState before).newEntries
      let b := (ext.ext.getState env).newEntries
      for e in b.take (b.length - a.length) do
        if let .«scoped» ns _ := e then out := out.push ns
  return out

def namesJson (s : NameSet) : Json :=
  Json.arr (s.toList.toArray.map fun n => Json.str n.toString)

/-- what the commands so far have put in place, each against the command that did it: the
constants each defined, under the names lean gives them and as written, the text each spans, and
per scope still open the `open`s, namespaces switched on and universes in effect, plus the aliases
exported, the instances lean named itself, what each attribute command gave an attribute, and the
section variables by their unique ids -/
structure Book where
  owners : NameMap Nat := {}
  exact : NameMap Nat := {}
  printed : NameMap (List Nat) := {}
  spans : Array (Nat × Nat) := #[]
  opens : List (List (OpenDecl × Nat)) := [[]]
  actives : List (List (Name × Nat)) := [[]]
  universes : List (List (Name × Nat)) := [[]]
  aliases : NameMap Nat := {}
  auto : NameMap Nat := {}
  targets : NameMap (List (Nat × Bool)) := {}
  via : Std.HashMap (Nat × Name) (List (List Nat)) := {}
  byLast : NameMap (List Nat) := {}
  includes : NameMap Nat := {}
  quotCtxs : NameMap Nat := {}
  syntaxRows : Array Nat := #[]
  realizedBy : NameMap Nat := {}
  simpsFirst : Array Nat := #[]
  simpsRows : Array Nat := #[]
  coded : Std.HashSet Nat := {}
  sharedBy : Std.HashMap Nat (List Nat) := {}
  coercions : Bool := false
  normNum : Bool := false
  vars : NameMap Nat := {}
  hints : Bool := false
  fileOpts : List (List (Name × DataValue)) := [[]]

/-- a name hygiene made, as lean prints it with its scopes: what it was written as, then the number
of each scope -/
def printedAs (n : Name) : Name :=
  let v := extractMacroScopes n
  v.scopes.foldl Name.mkNum v.name

/-- the command a constant came from: the one that defined it, or else the one that defined the
nearest name it is made under, as lean names what it generates for a declaration under it. a name
hygiene made is known also as lean prints it -/
partial def Book.owner (b : Book) (n : Name) : Option Nat :=
  match b.owners.find? n <|> (b.printed.find? n).bind (·.head?) with
  | some k => some k
  | none => if n.isAnonymous then none else b.owner n.getPrefix

/-- every command a printed hygienic name may stand for, since printing drops the context that
tells two apart -/
def Book.printedAll (b : Book) (n : Name) : List Nat :=
  if b.owners.contains n then [] else (b.printed.find? n).getD []

/-- the commands whose quotation contexts a hygienic name's context was pushed past. lean starts a
command's context at a hash of its text and moves on while that one is taken, so one such name
keeps it only while the commands that took the ones before stay -/
def Book.pushedPast (b : Book) (n : Name) : List Nat := Id.run do
  -- the context is written into the name after `_@`, as the module, its index and `_hygCtx`
  let parts := n.components
  let some ctxAt := parts.findIdx? (· == `_hygCtx) | return []
  let some start := parts.findIdx? (· == .mkSimple "_@") | return []
  let .num _ idx := parts[ctxAt - 1]! | return []
  let m := (parts.drop (start + 1)).take (ctxAt - 1 - (start + 1)) |>.foldl (· ++ ·) .anonymous
  let mut out := []
  let mut i := idx
  while i > 0 do
    i := i - 1
    match b.quotCtxs.find? (.str (.num m i) "_hygCtx") with
    | some k => out := k :: out
    | none => break
  return out

/-- the command whose text contains a byte -/
def Book.at (b : Book) (pos : Nat) : Option Nat :=
  b.spans.findIdx? fun (lo, hi) => lo ≤ pos && pos < hi

/-- the commands in effect that put a route in place, any one of which would do -/
def Book.providers (b : Book) (key : String) : List Nat :=
  if key.startsWith "alias " then (b.aliases.find? (parse (toString (key.drop 6)).toList)).toList
  else b.opens.flatMap fun level => (level.filter (s!"open {·.1}" == key)).map (·.2)

/-- what the one command that put a route in place needed to open the namespace it opens -/
def Book.behind (b : Book) (key : String) (k : Nat) : List (List Nat) :=
  b.opens.flatMap fun level => (level.filter fun (d, j) => j == k && s!"open {d}" == key).flatMap
    fun | (.simple ns _, _) => (b.via.get? (k, ns)).getD [] | _ => []

/-- lean names an instance nobody named after what it is an instance of, adding `_1`, `_2`, ... while
that name is taken by any constant, private or not, so one such instance keeps its name only while
what took the names before it stays -/
def Book.renumbered (b : Book) (n : Name) : List Nat :=
  match n with
  | .str p s =>
    let parts := s.splitOn "_"
    let digits := parts.getLast!
    if !b.auto.contains n || parts.length < 2 || digits.isEmpty || !digits.all Char.isDigit then []
    else
      let base := toString (s.dropRight (digits.length + 1))
      let taken := Name.str p base ::
        (List.range digits.toNat!).tail.map fun i => Name.str p s!"{base}_{i}"
      taken.filterMap b.exact.find?
  | _ => []

/-- whether a command gave a syntax kind declared outside this file another macro or elaborator.
such a kind is written in commands that never name the rule, and run from code that keeps no
record, as aesop's rules and derived instances are -/
def newKeys {γ : Type} (ext : KeyedDeclsAttribute.Extension γ) (before env : Environment) :
    List Name :=
  let a := (ext.ext.getState before).newEntries
  let b := (ext.ext.getState env).newEntries
  (b.take (b.length - a.length)).map fun
    | .global e => e.key
    | .«scoped» _ e => e.key

/-- the declarations of every macro and elaborator for a kind -/
def rulesFor (env : Environment) (k : Name) : List Name :=
  (macroAttribute.getEntries env k).map (·.declName) ++
    (Term.termElabAttribute.getEntries env k).map (·.declName) ++
    (Tactic.tacticElabAttribute.getEntries env k).map (·.declName) ++
    (Command.commandElabAttribute.getEntries env k).map (·.declName)

unsafe def extendsForeign (before env : Environment) (book : Book) (own written : NameSet) :
    Bool :=
  -- a rule whose pattern is written with a kind the same command declares is only ever run where
  -- that kind is written, so a command using it needs this one anyway
  !written.toList.any own.contains && (
  (newKeys macroAttribute.ext before env ++ newKeys Term.termElabAttribute.ext before env ++
    newKeys Tactic.tacticElabAttribute.ext before env ++
    newKeys Command.commandElabAttribute.ext before env).any
      (fun k => (book.owner k).isNone && !own.contains k) ||
  written.toList.any fun k => (book.owner k).isNone && !own.contains k && (
    (macroAttribute.getEntries before k).length != (macroAttribute.getEntries env k).length ||
    (Tactic.tacticElabAttribute.getEntries before k).length !=
      (Tactic.tacticElabAttribute.getEntries env k).length ||
    (Term.termElabAttribute.getEntries before k).length !=
      (Term.termElabAttribute.getEntries env k).length ||
    (Command.commandElabAttribute.getEntries before k).length !=
      (Command.commandElabAttribute.getEntries env k).length))

/-- what a command does to the rest of the file, from what it changed:
* `scope` opens or closes a namespace or section: the scopes lean keeps grew or shrank
* `prunable` puts in place what others use: constants, section variables, universes, an `open`
  or an alias. it stays only while something uses it
* `follows` changes nothing but how what it names behaves, as an attribute, `include`, `omit` or
  `set_option` does. it can go once what it names has
* `keep` changes what the file has no record of anyone using, so stays with all it needs
* `drop` changes nothing at all, as `#check`, `#print` and `example` do, so it can go unless
  something later uses it after all -/
def role (scopes defines introduces inert unaccounted : Bool) : String :=
  if scopes then "scope"
  else if defines || introduces then if unaccounted then "keep" else "prunable"
  else if unaccounted then "keep"
  else if inert then "drop"
  else "follows"

/-- commands and tactics that run what they wrap and then throw its messages away, the traces that
say what it used among them, by the names they are declared under -/
def silencing : List String :=
  ["guardMsgsCmd", "guardPanicCmd", "defeqAbuseCmd", "defeqAbuse", "postprocessTracesCmd", "says"]

/-- tactics that run tactics of their own and keep a result while losing the record of what those
used, so a command that uses one may rely on anything only that record would have shown -/
def lossy : List Name := [`Lean.Parser.Tactic.tryTrace, `Lean.Parser.Tactic.tryTraceWith,
  `Lean.Parser.Tactic.attemptAllPar, `Lean.Parser.Tactic.firstPar, `Mathlib.Tactic.Hint.hintStx,
  `Lean.PostprocessTraces.postprocessTracesCmd, `Lean.Parser.Tactic.exact?,
  `Lean.Parser.Tactic.apply?, `Lean.Parser.Syntax.exact?, `Lean.Parser.Tactic.rewrites?,
  `Lean.Parser.Tactic.rename]

/-- the options lean reads to say what elaboration used. a `set_option ... in` that changes one of
these for what it wraps silences it as a wrapper would -/
def quiets (opt : Name) : Bool :=
  [`diagnostics, `diagnostics.threshold, `pp.fullNames, `pp.privateNames, `pp.sanitizeNames].contains opt ||
    (`trace).isPrefixOf opt || (`says).isPrefixOf opt

/-- options that change only what lean says, not what it elaborates: traces, diagnostics, how terms
print, and what linters warn -/
def saysOnly (opt : Name) : Bool :=
  [`trace, `diagnostics, `pp, `linter].any (·.isPrefixOf opt)

/-- the option a `set_option ... in` sets, in a command, a tactic or a term -/
def setsOption (stx : Syntax) : Option Name :=
  if stx.getKind == ``Parser.Command.in && stx[0].getKind == ``Parser.Command.set_option then
    some stx[0][1].getId
  else if stx.getKind == ``Parser.Tactic.set_option || stx.getKind == ``Parser.Term.set_option then
    some stx[1].getId
  else none

/-- a command with every such wrapper taken off, leaving what each wraps: what comes last in it, or
for `says` the tactic it was told to run and otherwise the one before -/
partial def unsilenced (stx : Syntax) : Syntax × Bool :=
  match stx with
  | .node info kind args =>
    if (setsOption stx).any quiets then (unsilenced args.back!).1 |> (·, true)
    else if silencing.contains kind.componentsRev.head!.toString && !args.isEmpty then
      let inner := if kind.componentsRev.head! == `says then
          if args[2]!.getArgs.isEmpty then args[0]! else args[2]![0]!
        else args.back!
      (unsilenced inner).1 |> (·, true)
    else
      let parts := args.map unsilenced
      (.node info kind (parts.map (·.1)), parts.any (·.2))
  | s => (s, false)

/-- what a command's snapshots logged, as constants realized on demand do -/
def snapshotMessages (st : Command.State) : MessageLog :=
  st.snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) .empty) .empty

/-- every heartbeat limit a `set_option maxHeartbeats n` inside a command sets -/
partial def heartbeatLimits (stx : Syntax) (acc : Array Nat := #[]) : Array Nat :=
  let acc := if (setsOption stx) == some `maxHeartbeats then
      let value := if stx.getKind == ``Parser.Command.in then stx[0][3] else stx[3]
      match value.isNatLit? with
      | some n => acc.push n
      | none => acc
    else acc
  stx.getArgs.foldl (fun acc a => heartbeatLimits a acc) acc

/-- whether a command sets a trace option with a `set_option ... in` somewhere inside it -/
partial def setsTrace (stx : Syntax) : Bool :=
  (setsOption stx).any (`trace).isPrefixOf || stx.getArgs.any setsTrace

/-- the text of every doc comment a command has -/
partial def docTexts (stx : Syntax) (acc : Array String := #[]) : Array String :=
  let acc := if stx.getKind == ``Parser.Command.docComment then
      match stx[1] with
      | .atom _ text => acc.push text
      | _ => acc
    else acc
  stx.getArgs.foldl (fun acc a => docTexts a acc) acc

/-- every string literal in a piece of syntax -/
partial def strings (stx : Syntax) (acc : Array String := #[]) : Array String :=
  let acc := match stx.isStrLit? with
    | some t => acc.push t
    | none => acc
  stx.getArgs.foldl (fun acc a => strings a acc) acc

/-- every name literal in a piece of syntax, as `` `foo `` is written -/
partial def nameLits (stx : Syntax) (acc : Array Name := #[]) : Array Name :=
  let acc := match stx.isNameLit? with
    | some n => acc.push n
    | none => acc
  stx.getArgs.foldl (fun acc a => nameLits a acc) acc

/-- the words of a text that could be names, as lean prints them -/
def nameWords (text : String) : List Name :=
  let isPart (c : Char) := c.isAlphanum || c == '_' || c == '.' || c == '\'' || c == '«' ||
    c == '»' || c == '!' || c == '?' || (c.val ≥ 0x80 && !c.isWhitespace)
  let words := (text.toList.splitBy fun a b => isPart a == isPart b).filter fun cs =>
    cs.any isPart
  words.filterMap fun w =>
    let n := parse (w.dropWhile (· == '.'))
    if n.isAnonymous then none else some n

/-- whether a `#guard_msgs` checks nothing at all, as one told to drop everything does -/
partial def dropsAll (stx : Syntax) : Bool :=
  if stx.getKind.componentsRev.head? == some `guardMsgsSpec then
    let words := (stx.getArgs.toList.flatMap fun a => a.getArgs.toList).flatMap fun a =>
      (toString (a.reprint.getD "")).splitOn " " |>.filter (!·.isEmpty)
    let words := words.flatMap (·.splitOn ",") |>.filter (!·.isEmpty)
    words == ["drop", "all"]
  else stx.getArgs.any dropsAll

/-- whether a binder declares a variable another way than an earlier binder for it did -/
def rebinds (b b' : Syntax) : Bool :=
  b.getKind != b'.getKind || !b[2].structEq b'[2] || !b[3].structEq b'[3]

/-- whether a command turns an option on with a `set_option ... in` somewhere inside it -/
partial def turnsOn (stx : Syntax) (opt : Name) : Bool :=
  setsOption stx == some opt || stx.getArgs.any (turnsOn · opt)

/-- the options under which lean says what elaboration used: simp's rewrites, the extensions
`norm_num` ran, every diagnostic counter, and once a file has unification hints of its own, each
hint that matched. `says` is kept from checking itself by running a second time with its messages
thrown away -/
def evidenceOptions (opts : Options) (hints : Bool) (coercions : Bool := false)
    (normNum : Bool := false) : Options :=
  opts |>.set `maxHeartbeats (0 : Nat)
    |>.setBool `trace.Meta.synthInstance.apply coercions
    |>.setBool `pp.fullNames true
    |>.setBool `pp.privateNames true
    |>.setBool `pp.sanitizeNames false
    |>.set `pp.maxSteps (64 : Nat)
    |>.setBool `pp.deepTerms false
    |>.setBool `pp.proofs false
    |>.setBool `trace.Meta.Tactic.simp.rewrite true
    |>.setBool `trace.Tactic.norm_num normNum
    |>.setBool `trace.Meta.isDefEq.hint hints
    |>.setBool `diagnostics true
    |>.set `diagnostics.threshold (0 : Nat)
    |>.setBool `says.no_verify_in_CI true

/-- the options this run sets to make lean say what elaboration used -/
def evidenceKeys : List Name :=
  [`maxHeartbeats, `trace.Meta.synthInstance.apply, `pp.fullNames, `pp.privateNames, `pp.sanitizeNames,
    `pp.maxSteps, `pp.deepTerms, `pp.proofs, `trace.Meta.Tactic.simp.rewrite,
    `trace.Tactic.norm_num, `trace.Meta.isDefEq.hint, `diagnostics, `diagnostics.threshold,
    `says.no_verify_in_CI]

/-- a scope's options as the file had them: those set here put back to what the file set them to,
or taken off where it set nothing -/
def asWritten (opts : Options) (file : List (Name × DataValue)) : Options :=
  evidenceKeys.foldl (fun o k => match file.lookup k with
    | some v => o.insert k v
    | none => o.erase k) opts

/-- a term with every shared constant in it replaced by what it is made of. which command first made
a cached matcher or lemma, and so its name, is not part of what a statement says -/
partial def expandShared (env : Environment) (lemmas : NameSet) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => if isShared env lemmas n then
        (env.find? n).bind fun ci => if ci.hasValue (allowOpaque := true) then
          some (expandShared env lemmas (ci.instantiateValueLevelParams! us)) else none
      else none
    | _ => none

/-- a term with each binder named after how deep it sits, since binder names, hygienic ones from
whichever command made a shared matcher included, are not part of what a term says -/
partial def canonical (depth : Nat := 0) : Expr → Expr
  | .forallE _ t b i => .forallE (.mkSimple s!"v{depth}") (canonical depth t) (canonical (depth + 1) b) i
  | .lam _ t b i => .lam (.mkSimple s!"v{depth}") (canonical depth t) (canonical (depth + 1) b) i
  | .letE _ t v b nd => .letE (.mkSimple s!"v{depth}") (canonical depth t) (canonical depth v)
      (canonical (depth + 1) b) nd
  | .app f a =>
    -- `panic!` puts where it is written into the term, which is not part of what it states
    let e := Expr.app (canonical depth f) (canonical depth a)
    if [``panicWithPosWithDecl, ``panicWithPos].any e.isAppOf then
      mkAppN e.getAppFn (e.getAppArgs.map fun x => if x.isRawNatLit || x.nat?.isSome then mkRawNatLit 0 else x)
    else e
  | .mdata d e => .mdata d (canonical depth e)
  | .proj s i e => .proj s i (canonical depth e)
  | e => e

/-- the global references that only cache what lean would compute again from the imports, read
from the code that fills each: library search's and rewrite search's trees, the frequency of
symbols in the imports, the premises click suggestions offer, the declarations `find` searches, and
the projections of the classes an imported instance is of. one that fills such a cache changes no
result of a later command, only what that command spends on filling it itself -/
def caches : List String := [
  "_private.Lean.Meta.Tactic.LibrarySearch.0.Lean.Meta.LibrarySearch.ext",
  "_private.Lean.Meta.Tactic.Rewrites.0.Lean.Meta.Rewrites.ext",
  "_private.Lean.LibrarySuggestions.SymbolFrequency.0.Lean.LibrarySuggestions.symbolFrequencyMapRef",
  "_private.Lean.LibrarySuggestions.SineQuaNon.0.Lean.LibrarySuggestions.SineQuaNon.sineQuaNonTriggersRef",
  "Mathlib.Tactic.ClickSuggestions.rwRef", "Mathlib.Tactic.ClickSuggestions.grwRef",
  "Mathlib.Tactic.ClickSuggestions.appRef", "Mathlib.Tactic.ClickSuggestions.appAtRef",
  "Mathlib.Tactic.Find.findDeclsPerHead",
  "_private.Mathlib.Tactic.Widget.LibraryRewrite.0.Mathlib.Tactic.LibraryRewrite.importedRewriteLemmasExt",
  "_private.Mathlib.Tactic.Linter.OverlappingInstances.0.Mathlib.Linter.OverlappingInstances.classProjectionsCache"]

/-- the first field of a value with at least two -/
structure Pair where
  first : NonScalar
  second : NonScalar

/-- how to reach the reference a value of a type holds: the value is one, holds one as its only
field or its first, or is an environment extension whose state is one -/
inductive Reach where
  | direct
  | first (inner : Reach)
  | state

partial def reach (env : Environment) (ty : Expr) (depth : Nat := 0) : Option Reach :=
  let ty := ty.consumeMData
  match ty.getAppFn.constName? with
  | some ``ST.Ref | some ``IO.Ref => some .direct
  | some ``EnvExtension => if (reach env ty.appArg!).isSome then some .state else none
  | some s =>
    if depth > 3 then none else
    match getStructureInfo? env s, env.find? (s ++ `mk) with
    | some info, some ctor =>
      let fieldTy := Id.run do
        let mut t := ctor.type
        for _ in [0:ty.getAppNumArgs] do
          if let .forallE _ _ b _ := t then t := b
        match t with
        | .forallE _ d _ _ => if d.hasLooseBVars then none else some d
        | _ => none
      match fieldTy with
      | some d => (reach env d (depth + 1)).map fun r =>
          if info.fieldNames.size == 1 then r else .first r
      | none => none
    | _, _ => none
  | none => none

/-- every global reference lean and the packages keep, found from what lean initializes when it
loads them. one command can leave in one what a later command reads, which is in no environment -/
unsafe def globalRefs (env : Environment) : IO (Array (Name × Reach × NonScalar)) := do
  let mut out := #[]
  let mut seen : NameSet := {}
  -- what lean itself keeps lives in its own code whether or not the file imports where it is
  -- declared, so it is found from lean's own modules as well
  let core ← importModules #[{ module := `Lean }] {}
  for (e, builtinOnly) in [(env, false), (core, true)] do
    for (n, ci) in e.constants.map₁.toList do
      if seen.contains n || (getInitFnNameFor? e n).isNone then continue
      if builtinOnly && (getBuiltinInitFnNameFor? e n).isNone then continue
      let some r := reach e ci.type | continue
      seen := seen.insert n
      match e.evalConst NonScalar {} n with
      | .ok v => out := out.push (n, r, v)
      | .error err => IO.eprintln s!"cannot read {n}: {err}"
  return out

unsafe def Reach.ref (env : Environment) : Reach → NonScalar → IO.Ref NonScalar
  | .direct, v => unsafeCast v
  | .first r, v => r.ref env (unsafeCast v : Pair).first
  | .state, v => unsafeCast ((unsafeCast v : EnvExtension NonScalar).getState env)

unsafe def readRefs (env : Environment) (refs : Array (Name × Reach × NonScalar)) :
    IO (Array NonScalar) :=
  refs.mapM fun (_, r, v) => (r.ref env v).get

unsafe def writeRefs (env : Environment) (refs : Array (Name × Reach × NonScalar))
    (vals : Array NonScalar) : IO Unit := do
  for ((_, r, v), x) in refs.zip vals do (r.ref env v).set x

set_option maxHeartbeats 0 in
unsafe def loop (refs : Array (Name × Reach × NonScalar)) (root : Name) (header : Environment) (fileMap : FileMap) (out : IO.FS.Handle) (book : Book)
    (count : Nat) : FrontendM Nat := do
  let startPos := (← get).parserState.pos
  let held ← readRefs (← get).commandState.env refs
  let pre ← get
  let before := (← get).commandState.env
  let scope := (← get).commandState.scopes.head!
  let done ← processCommand
  let s := (← get)
  let stopPos := s.parserState.pos
  let stx := s.commands.back?.getD .missing
  let book := { book with spans := book.spans.push (startPos.byteIdx, stopPos.byteIdx) }
  let mut within := #[]
  for (o, lo, hi) in wrapping stx do
    let opens := (← get).commandState.scopes.head!.openDecls
    runCommandElabM (Command.elabCommand o)
    let now := (← get).commandState.scopes.head!.openDecls
    set s
    within := within.push ((lo, hi), now.take (now.length - opens.length))
  let ((), found) ← (s.commandState.infoState.trees.toList.forM
    (collect header (startPos.byteIdx, stopPos.byteIdx) within)).run {}
  -- what macros expanded into is read once it is known which readings elaboration went on with
  let expandedKinds := found.expanded.foldl (fun acc o => kinds o acc found.seen) found.kinds
  let found := { found with kinds := expandedKinds }
  -- an identifier that elaboration left no info for may still have been resolved, as a rule a
  -- tactic is told to drop is, so each is taken to mean whatever it resolves to where it stands
  let bareCtx : ContextInfo := {
    env := s.commandState.env, fileMap, options := scope.opts,
    currNamespace := scope.currNamespace, openDecls := scope.openDecls, ngen := {} }
  let ((), found) ← (do
    for id in nameNodes stx do
      let some p := id.getPos? | continue
      if (← get).resolvedAt.contains p.byteIdx then continue
      let inEffect := within.foldl (fun acc ((lo, hi), ds) =>
        if lo ≤ p.byteIdx && p.byteIdx < hi then ds ++ acc else acc) bareCtx.openDecls
      let ctx := { bareCtx with openDecls := inEffect }
      for (name, _) in ← ctx.runMetaM {} (resolveGlobalName id.getId) do
        modify fun a => { a with uses := a.uses.insert name }
        let (r, c) ← routes ctx {} id.getId name
        modify fun a => { a with routes := a.routes ++ r, choices := a.choices ++ c }
    : StateT Found IO Unit).run found
  let env := s.commandState.env
  let lemmas := cached before
  let reached := (found.defs.toList ++ found.uses.toList).foldl
    (fun acc d => finished before env lemmas d acc) {}
  -- constants the command made that no binder names and nothing it refers to reaches still belong
  -- to it, unless lean made them for a declaration from before, under that declaration's name
  let mut defs := found.defs
  let attrs := attributes stx found.attrs
  let mut realized : List Name := []
  for n in changed before.constants.map₂.root env.constants.map₂.root #[] do
    if before.contains n then continue
    -- what lean makes on demand under a constant from before, as equations are, belongs to that
    -- constant, whoever asked for it first
    if before.contains n.getPrefix || before.contains (privateToUserName n).getPrefix ||
        isShared before lemmas n then
      realized := n :: realized
    else unless reached.contains n do
      defs := defs.insert n
  let uses := (kinds stx found.kinds found.seen (explicitKind stx)).toList.foldl (fun u k => u.insert k)
    (reached.toList.foldl (fun acc n => acc.insert n) found.uses)
  -- a shared constant written by name, or reused by what is checked by its text, is used as it is
  let reused := uses.toList.filter fun n => before.contains n && isShared before lemmas n
  let uses := uses.filter fun n => !(before.contains n && isShared before lemmas n) ||
    found.named.contains n
  -- drain this command's messages, which say what elaboration used along the way; left in the log
  -- a large file's traces would pile up past what memory holds
  let mut traced : NameSet := {}
  let mut tried : NameSet := {}
  let mut errors := 0
  -- what a constant realized on demand logged goes to the command's snapshots, not its log
  for msg in s.commandState.messages.toList ++ (snapshotMessages s.commandState).toList do
    if msg.severity == .error then errors := errors + 1
    (traced, tried) := evidence (← msg.data.toString) traced tried
  modify fun st => { st with commandState.messages := {}, commandState.snapshotTasks := #[] }
  -- what a command throws away of its own messages, it is elaborated once more without the
  -- wrappers that do that, from where it began, and that state put aside again
  let (bare, silenced) := unsilenced stx
  let mut divergent := false
  -- what checks the text of what lean says, and what checks only whether it said something
  let early := kinds stx found.kinds found.seen (explicitKind stx)
  let fileSets (opt : Name) := scope.opts.getBool opt false || turnsOn stx opt
  let textual := (early.contains ``guardMsgsCmd && !dropsAll stx) ||
    early.contains `Mathlib.Tactic.successIfFailWithMsg ||
    early.contains `Mathlib.Tactic.Says.says ||
    (fileSets `doc.verso && ((docTexts stx).any (fun t => (t.splitOn "```").length > 1) ||
      ((String.Pos.Raw.extract fileMap.source startPos stopPos).splitOn "```").length > 1))
  let presence := early.contains ``guardPanicCmd || fileSets `warningAsError
  -- and whether what it says includes traces the file switched on, which can name what was tried
  let mut tracing := setsTrace stx
  for (k, v) in scope.opts do
    if (`trace).isPrefixOf k && !evidenceKeys.contains k && v == .ofBool true then tracing := true
  for (k, v) in (book.fileOpts.head?.getD []) do
    if (`trace).isPrefixOf k && v == .ofBool true then tracing := true
  -- the errors of the run the evidence is taken from: a wrapper that checks what lean says fails in
  -- the first run, where the options here add to what it says, so for one the run without it counts
  let mut evidenced := ((s.commandState.messages.toList ++ (snapshotMessages s.commandState).toList).filter
    (·.severity == .error)).length
  if silenced then
    let post ← get
    set { pre with commandState.messages := {}, commandState.snapshotTasks := #[] }
    runCommandElabM (Command.elabCommandTopLevel bare)
    let st := (← get).commandState
    for msg in st.messages.toList ++ (snapshotMessages st).toList do
      (traced, tried) := evidence (← msg.data.toString) traced tried
    evidenced := (st.messages.toList ++ (snapshotMessages st).toList).filter
      (·.severity == .error) |>.length
    set post
  -- the wrappers, and whatever compares what lean says, fail under the options here, which change
  -- what it says, so what the command gets wrong is counted from a run of it as written, under the
  -- file's own options
  -- every command is elaborated once more as the file has it, under its own options, since the
  -- options here change what some of it elaborates to: what lean says without a limit on heartbeats
  -- differs where a tactic reads that limit, diagnostics recheck unifications and keep what they
  -- assigned, and the file's own code can read any option. what it gets wrong and what it makes are
  -- taken from that run, and what was found here is trusted only where it made the same
  let mut global := false
  let mut fills := false
  let mut spent := 0
  let mut limit := 0
  do
    -- what the runs here left in global references is undone, so the run as written starts from
    -- what a plain compile would have there
    writeRefs (← get).commandState.env refs held
    let post ← get
    let fileOpts := List.replicate (pre.commandState.scopes.length - book.fileOpts.length) [] ++
      book.fileOpts
    set { pre with commandState.messages := {}, commandState.snapshotTasks := #[],
                   commandState.scopes := (pre.commandState.scopes.zip fileOpts).map
                     fun ((sc : Command.Scope), file) => { sc with opts := asWritten sc.opts file } }
    let started ← IO.getNumHeartbeats
    runCommandElabM (Command.elabCommandTopLevel stx)
    spent := (← IO.getNumHeartbeats) - started
    -- the smallest limit that applies anywhere in it, a `set_option maxHeartbeats n in` included
    limit := ((heartbeatLimits stx).foldl (fun acc n => if acc == 0 then n else if n == 0 then acc else min acc n)
      (maxHeartbeats.get (← get).commandState.scopes.head!.opts)) * 1000
    let st := (← get).commandState
    errors := (st.messages.toList ++ (snapshotMessages st).toList).filter
      (·.severity == .error) |>.length
    let mine := changed before.constants.map₂.root s.commandState.env.constants.map₂.root #[]
    let theirs := changed before.constants.map₂.root st.env.constants.map₂.root #[]
    let same (n : Name) := match s.commandState.env.find? n, st.env.find? n with
      | some a, some b => a.type == b.type && a.value? (allowOpaque := true) == b.value? (allowOpaque := true)
      | none, none => true
      | _, _ => false
    -- and a command that changes one leaves what nothing records for those after it
    let now ← readRefs st.env refs
    for ((n, _, _), (a, b)) in refs.zip (now.zip held) do
      if ptrAddrUnsafe a != ptrAddrUnsafe b then
        if caches.contains n.toString then fills := true else global := true
    divergent := mine.qsort Name.lt != theirs.qsort Name.lt || !(mine.all same) ||
      evidenced > errors
    -- and what it declares is what that run made, which is what the file makes
    set { post with commandState.env := st.env }
  let mut used := traced.toList.foldl (·.insert ·) uses
  -- a kind the file declares, run where no info was kept of how, as tactics that throw their state
  -- away run what they are given, needs every rule the file has for it
  for (k, p) in kindNodes stx do
    if (book.owner k).isSome && !found.seen.contains (k, p) then
      used := (rulesFor env k).foldl (·.insert ·) used
  -- the command as lean elaborates it, inside whatever wrappers and `in` chains it comes in
  let (cmd, _) := unwrap bare
  let kind := cmd.getKind
  let opens ← opened header scope bare
  let after := (← get).commandState.scopes.head!
  -- every earlier command this one needs, found through the book
  let mut needs : Array Nat := #[]
  -- a name printed without the context hygiene gave it may stand for any constant printed alike
  for u in used.toList do
    needs := needs ++ (book.owner u).toArray ++ (book.printedAll u).toArray
  for t in tried.toList do
    if Meta.isInstanceCore env t then
      needs := needs ++ (book.owner t).toArray ++ (book.printedAll t).toArray
  -- a name lean chose matters only where it is written, where it is in what `root` states, and in
  -- what lean says of it where that is checked
  let written := kinds stx found.kinds found.seen (explicitKind stx)
  let observes := textual || presence
  let stated := defs.toList.foldl (fun acc d => if shown d == root then
      match env.find? d with
      | some ci => (expandShared env lemmas ci.type).getUsedConstants.foldl (·.insert ·) acc
      | none => acc
    else acc) found.named
  if textual then
    for n in reused do used := used.insert n
  -- names a check of what lean says expects, written in its expected text
  let mut expected : NameSet := {}
  if textual then
    for t in docTexts stx ++ strings stx do
      for w in nameWords t do
        -- a name hygiene made is printed whole, context and all, and is that name; a part of one is
        -- no name at all
        if w.hasMacroScopes then
          expected := expected.insert w
          needs := needs ++ (book.owner w).toArray
        else if w.components.any (fun c => c == `_hygCtx || c == `_hyg) then continue
        else
          for (n, _) in ← (bareCtx.runMetaM {} (resolveGlobalName w) : IO _) do
            expected := expected.insert n
            needs := needs ++ (book.owner n).toArray
  let picked := (if textual then used.toList ++ tried.toList ++ expected.toList else stated.toList) ++
    (idents bare).toList ++ (nameLits stx ++ found.expanded.foldl (fun acc o => nameLits o acc) #[]).toList
  for u in picked do
    needs := needs ++ (book.renumbered (shown u)).toArray
    if u.hasMacroScopes then
      needs := needs ++ (book.pushedPast u).toArray
    -- a name lean numbered among what one command made, as its matchers and auxiliary proofs are,
    -- was numbered past the shared ones that command reused, so it needs what made those. what is
    -- made on demand afterwards, as equations are, is named after its declaration alone
    if let some k := book.owner u then
      if !book.exact.contains (shown u) && !book.realizedBy.contains u && !realized.contains u then
        needs := needs ++ ((book.sharedBy.get? k).getD []).toArray
  for n in (nameLits stx ++ found.expanded.foldl (fun acc o => nameLits o acc) #[]).toList do
    needs := needs ++ (book.owner n).toArray
  -- an attribute command is needed where what it gave an attribute is used the way the attribute
  -- has it used: for simp lemmas and instances, by simp or instance search, and otherwise at all
  let unnamed (t : Name) := tried.contains t || traced.contains t || !found.named.contains t
  for t in used.toList ++ tried.toList do
    for (k, quiet) in (book.targets.find? t).getD [] do
      if !quiet || unnamed t then needs := needs.push k
  -- an `eqns` attribute only takes effect where the equations were not made yet, so it needs the
  -- command that made them, if one did
  if (attributes bare {}).contains `eqns then
    for t in found.named.toList do
      for i in [1:20] do
        needs := needs ++ (book.realizedBy.find? (t ++ .mkSimple s!"eq_{i}")).toArray
      needs := needs ++ (book.realizedBy.find? (t ++ `eq_def)).toArray
  -- `@[simps]` reads the projections the first one to look at a structure found, and what a file's
  -- `Simps` projections said then
  if (attributes bare found.attrs).toList.any (·.toString.startsWith "simps") then
    needs := needs ++ book.simpsFirst ++ book.simpsRows
  -- `simp [-foo]` asks whether `foo` is a simp lemma, so it needs what made it one
  for id in erased stx do
    for (t, _) in ← (bareCtx.runMetaM {} (resolveGlobalName id.getId) : IO _) do
      for (k, _) in (book.targets.find? t).getD [] do needs := needs.push k
  -- a Verso docstring's roles parse and resolve syntax and categories without leaving info
  if fileSets `doc.verso && !(docTexts stx).isEmpty ||
      (fileSets `doc.verso && ((String.Pos.Raw.extract fileMap.source startPos stopPos).splitOn "/--").length > 1) then
    needs := needs ++ book.syntaxRows
  -- what the commands it uses that run code of their own read of the environment leaves no record
  for k in ((used.toList.filter (fun n => !found.named.contains n || written.contains n)).filterMap
      book.owner).eraseDups do
    if book.coded.contains k then needs := needs ++ (List.range count).toArray
  -- what lean says, where that is checked, prints names as short as the `open`s in effect and the
  -- other constants of the same last name let it, and through the notation switched on
  if textual then
    needs := needs ++ (book.opens.flatten.map (·.2)).toArray ++ (book.actives.flatten.map (·.2)).toArray
    -- and goals show every section variable in effect, which other names then print around
    needs := needs ++ (scope.varUIds.toList.filterMap book.vars.find?).toArray
    let mut named : NameSet := tried.toList.foldl (·.insert ·) used
    for u in used.toList ++ tried.toList do
      if let some ci := env.find? u then named := ci.type.getUsedConstants.foldl (·.insert ·) named
    for u in named.toList do
      if let .str _ last := shown u then
        needs := needs ++ ((book.byLast.find? (.mkSimple last)).getD []).toArray
  let mut levels := found.levels
  for d in defs.toList do
    if let some ci := env.find? d then
      levels := ci.levelParams.foldl (·.insert ·) levels
  -- what the command did to the scopes: opened or closed one, or put an `open` in the one it is in
  let depth := (← get).commandState.scopes.length
  let deeper := pre.commandState.scopes.length
  let scopeKind : Json :=
    if depth > deeper then
      if after.currNamespace != scope.currNamespace then "namespace" else "section"
    else if depth < deeper then "end"
    else Json.null
  let plainOpen := depth == deeper && (after.openDecls != scope.openDecls ||
    (bare.getKind == ``Parser.Command.open && !opens.scopedIn.isEmpty))
  -- the section variables it declares or declares anew, matched by unique id to their binders
  let fresh := after.varUIds.toList.filter (!scope.varUIds.contains ·)
  let was ← binders scope
  let now ← binders after
  let rebound := now.toList.filter fun (u, _, b) =>
    was.any fun (u', _, b') => u == u' && rebinds b b'
  let universesHere := after.levelNames.take (after.levelNames.length - scope.levelNames.length)
  let aliased := (getAliasState env).map₂.toList.any fun (a, targets) =>
    (getAliasState before).find? a != some targets
  let introduces := !fresh.isEmpty || !rebound.isEmpty || !universesHere.isEmpty || plainOpen ||
    aliased
  -- the section variables it took in, and those an `include` or `omit` names
  let decls := defs.toList.filterMap env.find?
  let own := ownBinders cmd
  let declared := if cmd[1][1].getKind == ``Parser.Command.declId then some cmd[1][1][0].getId else none
  let signed := decls.map fun ci => (ci, if declared.any (·.isSuffixOf (shown ci.name)) &&
    (shown ci.name).componentsRev.head? == declared.bind (·.componentsRev.head?) then own else [])
  let mut taken : List Name := opens.vars ++ (after.includedVars.filter
    (!scope.includedVars.contains ·)) ++ (after.omittedVars.filter (!scope.omittedVars.contains ·))
  -- a `variable ... in` declares anew, for this command alone, what an earlier one declared
  let inChain ← binders opens.wrapped
  taken := taken ++ (inChain.toList.filter fun (u, _, b) =>
    was.any fun (u', _, b') => u == u' && rebinds b b').map (·.1)
  -- only a theorem is elaborated with just the variables its statement takes in. any other
  -- declaration sees every one in effect, which can steer what it elaborates to without leaving a
  -- trace in it, and a pattern name a variable shadows is a variable rather than a constructor
  let isTheorem := cmd[1].getKind == ``Parser.Command.theorem ||
    found.kinds.contains ``Parser.Command.theorem
  if (kind == ``Parser.Command.declaration || found.kinds.contains ``Parser.Command.declaration) &&
      !isTheorem then
    taken := taken ++ opens.wrapped.varUIds.toList
  let shadowing := was.toList.filterMap fun (u, n, _) => if found.shadows.contains n then some u else none
  taken := taken ++ shadowing
  if !opens.wrapped.varUIds.isEmpty && (!decls.isEmpty || !fresh.isEmpty) then
    let (vs, alone) ← sectionVars signed fresh opens.wrapped
    taken := taken ++ vs
    -- one it took in only because an `include` said so needs that `include`
    for u in alone do
      if scope.includedVars.contains u then
        needs := needs ++ (book.includes.find? u).toArray
    -- and lean always takes in what an `include` names, even where a binder of the declaration's
    -- own has the same name, so matching by name cannot find it
    if kind == ``Parser.Command.declaration || found.kinds.contains ``Parser.Command.declaration then
      for u in opens.wrapped.includedVars do
        unless vs.contains u do
          taken := u :: taken
          needs := needs ++ (book.includes.find? u).toArray
  -- any command but a declaration may check identifiers against the section variables by name,
  -- as a notation's quotation is, so it needs the ones it names. a macro that expands to a
  -- declaration, as `lemma` does, is a declaration
  let declaration := kind == ``Parser.Command.declaration ||
    found.kinds.contains ``Parser.Command.declaration
  if !declaration && !decls.isEmpty then
    let names := was.foldl (fun m (u, n, _) => m.insert n u) ({} : NameMap Name)
    taken := taken ++ (idents bare).toList.filterMap names.find?
  needs := needs ++ (taken.filterMap book.vars.find?).toArray
  needs := needs ++ (rebound.filterMap (book.vars.find? ·.1)).toArray
  for l in levels.toList do
    needs := needs ++ (book.universes.findSome? fun level =>
      (level.find? (·.1 == l)).map (·.2)).toArray
  -- a route the command puts in place itself, by an `open ... in`, needs no command before it, and
  -- one several commands put in place needs any of them
  let mut choices : Array (List Nat) := #[]
  for (key, times) in found.routes ++ opens.routes do
    let ps := book.providers key
    if times > ps.length then continue
    match ps.eraseDups with
    | [] => pure ()
    | [k] =>
      needs := needs.push k
      for c in book.behind key k do
        match c with
        | [j] => needs := needs.push j
        | c => choices := choices.push c
    | ps => choices := choices.push ps
  -- an `open` that would resolve to fewer namespaces without another needs that one only where
  -- something is used through those
  let mut behind : List (Name × List Nat) := []
  for (ns, key, times) in opens.through do
    let ps := book.providers key
    unless times > ps.length || ps.isEmpty do behind := (ns, ps.eraseDups) :: behind
  for c in found.choices do
    let alts := c.toList.map fun (key, times) => (book.providers key, times)
    unless alts.any (fun (ps, times) => times > ps.length) do
      choices := choices.push (alts.flatMap (·.1)).eraseDups
  -- what is scoped to a namespace is in effect where it is switched on: inside the namespace, by
  -- the command itself, or by any of the commands in effect that opened it. a command that uses
  -- such a thing without naming it, by its syntax, by instance search or by simp, needs one
  let known ← introspected
  let switchedOn : List Name := if plainOpen then [] else
    (opens.introduced.toList.filterMap fun | .simple ns _ => some ns | _ => none) ++
      opens.scopedIn.toList
  let indirect := (used.toList ++ tried.toList).filter unnamed
  let active := book.actives.flatten
  let byWhom (ns : Name) := (active.filterMap fun (n, k) => if n == ns then some k else none).eraseDups
  let elsewhere (ns : Name) := !ns.isPrefixOf scope.currNamespace && !switchedOn.contains ns
  for ns in (active.map (·.1)).eraseDups do
    if elsewhere ns then
      let names ← scopedNames env ns
      if indirect.any names.contains then choices := choices.push (byWhom ns)
  -- something scoped where no record says who uses it is switched on wherever its namespace is
  -- open, so the command that adds it needs that
  for ns in ← scopedTo before env known do
    if elsewhere ns && !(byWhom ns).isEmpty then choices := choices.push (byWhom ns)
  -- what this command puts in place for those after it
  let fit {α} (levels : List (List α)) : List (List α) :=
    let levels := levels.drop (levels.length - min levels.length depth)
    List.replicate (depth - levels.length) [] ++ levels
  let mut book := { book with opens := fit book.opens, actives := fit book.actives,
                               universes := fit book.universes }
  for (u, _, _) in rebound do
    book := { book with vars := book.vars.insert u count }
  for u in fresh do
    book := { book with vars := book.vars.insert u count }
  for c in pre.commandState.usedQuotCtxts.toList.foldl (fun acc c => acc.erase c)
      s.commandState.usedQuotCtxts do
    book := { book with quotCtxs := book.quotCtxs.insert c count }
  book := { book with sharedBy := book.sharedBy.insert count (reused.filterMap book.owner).eraseDups }
  for (ns, ps) in behind do
    let others := (book.via.get? (count, ns)).getD []
    book := { book with via := book.via.insert (count, ns) (ps :: others) }
  for d in defs.toList do
    book := { book with owners := book.owners.insert d count, exact := book.exact.insert (shown d) count }
    if let .str _ last := shown d then
      let others := (book.byLast.find? (.mkSimple last)).getD []
      book := { book with byLast := book.byLast.insert (.mkSimple last) (count :: others) }
    if d.hasMacroScopes then
      let others := (book.printed.find? (printedAs (shown d))).getD []
      book := { book with printed := book.printed.insert (printedAs (shown d)) (count :: others) }
  if plainOpen then
    let introduced := (opens.introduced.map (·, count)).toList
    book := { book with opens := match book.opens with
      | level :: rest => (introduced ++ level) :: rest
      | [] => [introduced] }
  let activated : List Name := if plainOpen then
      (opens.introduced.toList.filterMap fun | .simple ns _ => some ns | _ => none) ++
        opens.scopedIn.toList
    else []
  book := { book with actives := match book.actives with
    | level :: rest => (activated.map (·, count) ++ level) :: rest
    | [] => [activated.map (·, count)] }
  for (a, targets) in (getAliasState env).map₂.toList do
    if (getAliasState before).find? a != some targets then
      book := { book with aliases := book.aliases.insert a count }
      if let .str _ last := a then
        let others := (book.byLast.find? (.mkSimple last)).getD []
        book := { book with byLast := book.byLast.insert (.mkSimple last) (count :: others) }
  book := { book with universes := match book.universes with
    | level :: rest => (universesHere.map (·, count) ++ level) :: rest
    | [] => [universesHere.map (·, count)] }
  -- a constant whose name is nowhere in the command was named by lean, as an instance written
  -- without a name, one a `deriving` clause makes and a notation's syntax kind are
  let writtenIds := idents bare
  for d in defs.toList do
    if !writtenIds.contains (shown d) &&
        !writtenIds.toList.any (·.isSuffixOf (shown d)) then
      book := { book with auto := book.auto.insert (shown d) count }
  let mut simpSets : NameSet := {}
  for (_, ext) in (← Meta.simpExtensionMapRef.get) do
    simpSets := simpSets.insert ext.ext.name
  -- a simp set no toolchain here has is read only by simp, whose trace names what it used. and a
  -- plain declaration written with no attribute only gets entries lean makes for its own
  -- constants, as for those a `deriving` clause makes, which nothing can use without using those
  let generated := kind == ``Parser.Command.declaration && (attributes bare {}).isEmpty
  let changes ← added before env (plainOpen || depth != deeper)
  -- the projections `@[simps]` finds for a structure are cached where it first finds them, and
  -- found the same way again by the next one to look. only those a command spells out are its own
  let cache (n : Name) := n == `Simps.structureExt &&
    !written.contains `Lean.Parser.Command.initialize_simps_projections
  -- and lean gives `grind` theorems of its own for what a declaration makes, such as how big a
  -- structure's values are, which are for constants nothing is written as
  let madeHere (d : Name) := defs.contains d &&
    !writtenIds.toList.any (·.isSuffixOf (shown d))
  let ownGrind := (grindDecls before env).all (·.any madeHere)
  let grinds (n : Name) := n == ``Meta.Grind.grindExt || n == ``Meta.Grind.liaExt
  let unaccounted := if generated then #[] else changes.filter fun n =>
    !accounted.contains n.toString && !observable.contains n.toString && !cache n &&
      !(grinds n && ownGrind) &&
      (unrecorded.contains n.toString || !simpSets.contains n)
  -- a syntax category comes with an attribute of its own for parsers, whose users name the category
  let unaccounted := if kind == ``Parser.Command.syntaxCat then
    unaccounted.filter (· != `Lean.attributeExtension) else unaccounted
  let unaccounted := if extendsForeign before env book defs written
    then unaccounted.push `foreignSyntaxRules else unaccounted
  -- an attribute command does nothing but give what it names an attribute
  -- an `include` is needed only by what takes a variable in because of it
  let including := kind == ``Parser.Command.include && depth == deeper
  if including then
    for u in after.includedVars.filter (!scope.includedVars.contains ·) do
      book := { book with includes := book.includes.insert u count }
  -- an attribute command whose attribute changes how its target is used beyond being named, as
  -- reducibility does, stays as long as its target does
  let attributing := kind == ``Parser.Command.attribute && defs.isEmpty && !introduces &&
    !(attributes bare {}).toList.any (·.toString.startsWith "-")
  let quiet := changes.all fun n => simpSets.contains n || n == ``Meta.instanceExtension ||
    n == `Lean.Meta.globalInstanceExtension || bookkeeping.contains n.toString
  -- one that changes how its target unfolds matters wherever the target is unfolded, which leaves
  -- no record, so it stays as long as its target does
  let unfolding := attributing && changes.any (·.toString == "reducibilityCore")
  for n in realized do
    unless book.realizedBy.contains n do book := { book with realizedBy := book.realizedBy.insert n count }
  if changes.any (·.toString == "Simps.structureExt") then
    book := { book with simpsFirst := book.simpsFirst.push count }
  if defs.toList.any (fun d => (shown d).components.contains `Simps) then
    book := { book with simpsRows := book.simpsRows.push count }
  if changes.any (· == ``Parser.parserExtension) then
    book := { book with syntaxRows := book.syntaxRows.push count }
  let rules := [``Parser.Command.macro, ``Parser.Command.macro_rules, ``Parser.Command.elab,
    ``Parser.Command.elab_rules].contains kind ||
    (kind == ``Parser.Command.declaration && [`macro, `term_elab, `tactic, `command_elab].any
      (attributes bare {}).contains)
  if rules && (runsCode bare || kind == ``Parser.Command.declaration ||
      !scope.opts.getBool `hygiene true || turnsOn stx `hygiene) then
    book := { book with coded := book.coded.insert count }
  -- a limit on recursion set for a command is left for every command after it
  let unaccounted := if s.commandState.maxRecDepth != pre.commandState.maxRecDepth then
    unaccounted.push `maxRecDepth else unaccounted
  if attributing then
    for t in found.named.toList do
      book := { book with targets := book.targets.insert t ((count, quiet) :: (book.targets.find? t).getD []) }
  let mut switches := false
  let mut shows : Array Name := #[]
  for ns in activated do
    for e in ← foreignScoped env ns known do
      if observable.contains e.toString then shows := shows.push e else switches := true
  -- setting an option that changes only what lean says matters only where what it says is checked
  -- turning a linter off is what lets a file compile where that linter would fail, so only turning
  -- one on, or changing what lean says in other ways, says nothing more
  let quietOption := bare.getKind == ``Parser.Command.set_option && saysOnly bare[1].getId &&
    !((`linter).isPrefixOf bare[1].getId && bare[3].getKind == `false)
  -- a command that changed nothing lean carries on to the next can only have said something
  -- what it put in place that the end of its scope takes away again, and whether it opens a section
  -- that does nothing else
  let undone := depth == deeper && (introduces || after.includedVars != scope.includedVars ||
    after.omittedVars != scope.omittedVars || ptrAddrUnsafe after.opts != ptrAddrUnsafe scope.opts ||
    (← addedLocally before env))
  let plainSection := kind == ``Parser.Command.section && cmd[0].getArgs.all (·.getNumArgs == 0)
  let inert := defs.isEmpty && !(← touched before env) && !introduces && depth == deeper &&
    after.includedVars == scope.includedVars && after.omittedVars == scope.omittedVars &&
    ptrAddrUnsafe after.opts == ptrAddrUnsafe scope.opts
  -- the namespaces it made known without defining anything under them, as `scoped[NS]` does
  let candidates := (identNodes stx ++ found.expanded.foldl (fun acc o => identNodes o acc) #[]).toList.flatMap
    fun i => (prefixesOf i.getId.eraseMacroScopes)
  let registersNow := (candidates.eraseDups.filter fun n => env.isNamespace n && !before.isNamespace n).toArray
  -- a command that runs code does what nothing records: `#eval` and its kin, `run_tac`, evaluating
  -- natively, or code of the file's own that can do IO, which can change state outside the
  -- environment that a later command reads. such a command is never deleted
  let runner := [`eval, `evalBang, `runCmd, `runElab, `runMeta, `runTac, `nativeDecide]
  let runs := (kindNodes stx).any (fun (k, _) => runner.contains (k.componentsRev.headD .anonymous)) ||
    written.toList.any (fun k => runner.contains (k.componentsRev.headD .anonymous)) ||
    [``Lean.reduceBool, ``Lean.reduceNat, ``Lean.ofReduceBool, ``Lean.ofReduceNat].any used.contains ||
    used.toList.any fun n => (book.owner n).isSome && effectful env n &&
      (!found.named.contains n || written.contains n)
  -- and what it runs may read anything outside the environment, written by any command before it
  if runs then needs := needs ++ (List.range count).toArray
  -- and code of the file's own that can do IO, registered where lean runs it without being asked by
  -- name, can write what a later command reads, so it makes every later command stay
  -- what reads a file reads what any command before it may have written, and what writes one does
  -- what nothing records
  let atoms := (atomsOf stx).toList
  let readsFiles := (kindNodes stx).any fun (k, _) =>
    [`includeStr, `bvCheck].contains (k.componentsRev.headD .anonymous)
  if readsFiles then needs := needs ++ (List.range count).toArray
  let writesFiles := atoms.contains "#clear_deprecations" || atoms.contains "bv_decide?" ||
    (atoms.contains "bv_decide" && atoms.any (·.endsWith "graphviz")) ||
    (atomsOf stx).any (· == "graphviz") ||
    (scope.opts.find? `aesop.stats.file).any (· != .ofString "") || turnsOn stx `aesop.stats.file
  -- code registered for syntax the file declares runs only where that syntax is written, which needs
  -- this command anyway; registered for imported syntax, or in a table lean runs by itself, it can
  -- run anywhere after
  let keys := newKeys macroAttribute.ext before env ++ newKeys Term.termElabAttribute.ext before env ++
    newKeys Tactic.tacticElabAttribute.ext before env ++ newKeys Command.commandElabAttribute.ext before env
  let ownKeys := keys.all fun k => (book.owner k).isSome || defs.contains k
  let elsewhere := changes.any fun n => unrecorded.contains n.toString ||
    n.toString == "Mathlib.Meta.NormNum.normNumExt"
  let worldWriter := !changes.isEmpty && defs.toList.any (effectful env ·) && (!ownKeys || elsewhere)
  -- the command's lines run from where it starts to where its last token ends, which can be the
  -- line the next command starts on
  let first := (fileMap.toPosition startPos).line
  let last := match stx.getTailPos? with
    | some p => (fileMap.toPosition p).line
    | none => first
  let rows (xs : Array Nat) : Json :=
    Json.arr ((xs.toList.filter (· != count)).eraseDups.mergeSort.toArray.map toJson)
  out.putStrLn (Json.compress <| Json.mkObj [
    ("start", toJson first), ("finish", toJson last), ("kind", toJson kind.toString),
    ("role", toJson (if switches || runs || global || writesFiles then "keep" else
      role (!scopeKind.isNull) (!defs.isEmpty || (attributing && !unfolding) || including) introduces
        (inert || quietOption)
        (!unaccounted.isEmpty))),
    ("scope", scopeKind), ("delta", toJson ((depth : Int) - deeper)), ("local", toJson undone),
    ("plain", toJson plainSection),
    ("unaccounted", Json.arr (unaccounted.map fun n => Json.str n.toString)),
    ("observable", Json.arr ((changes.filter (observable.contains ·.toString) ++ shows).map
      (fun n => Json.str n.toString) ++
      (if quietOption then #[Json.str s!"set_option {bare[1].getId}"] else #[]))),
    ("observes", toJson (observes || after.opts.getBool `warningAsError false)),
    ("traced", toJson (changes.any fun n => simpSets.contains n ||
      [``Meta.instanceExtension, `Mathlib.Meta.NormNum.normNumExt,
        ``Meta.unificationHintExtension].contains n ||
      ["Lean.Meta.NormCast.normCastExt.up", "Lean.Meta.NormCast.normCastExt.down",
        "Lean.Meta.NormCast.normCastExt.squash", "Lean.Meta.NormCast.pushCastExt",
        "Mathlib.Tactic.Push.pushExt", "Mathlib.Tactic.Push.pullExt",
        "Lean.Meta.Grind.normExt"].contains n.toString)),
    ("lossy", toJson (lossy.any written.contains || (textual && tracing))),
    ("defines", namesJson (shownAll defs)),
    ("needs", rows needs),
    ("choices", Json.arr (choices.toList.eraseDups.toArray.map fun c => rows c.toArray)),
    ("opens", Json.arr ((opens.own ++ found.quotedNs.toList.filter (!header.isNamespace ·)).eraseDups.toArray.map
      fun n => Json.str n.toString)),
    ("targets", rows (if unfolding then (found.named.toList.filterMap book.owner).toArray else #[])),
    ("divergent", toJson divergent),
    ("worldWriter", toJson worldWriter),
    ("fills", toJson fills), ("heartbeats", toJson spent), ("limit", toJson limit),
    ("namespace", toJson after.currNamespace.toString),
    ("registers", Json.arr (registersNow.map fun n => Json.str n.toString)),
    ("errors", toJson errors)])
  -- the trees of a finished command are no longer needed, and a large file would pile them up
  modify fun st => { st with commandState.infoState.trees := {}, commands := #[] }
  -- the options that make lean say what elaboration used hold for every command, whatever the file
  -- sets, and a unification hint is only of interest once the file has one of its own, since
  -- tracing every unification before then would only cost time
  let hints := book.hints || attrs.contains `unification_hint
  -- and an instance coercions unfold, only once the file has one of its own
  let coercions := book.coercions || (defs.toList ++ found.named.toList).any (unfoldedAway env ·)
  -- and what `norm_num` evaluated with, only once the file has an extension of its own: the trace
  -- costs a great deal on a large computation, and an imported extension is never deleted
  let normNum := book.normNum || changes.any (·.toString == "Mathlib.Meta.NormNum.normNumExt")
  -- what the file itself sets of those options, scope by scope, before they are set again: a
  -- value that is not the one this run put there was set by the file, and a scope opened since
  -- starts from the one around it
  let ours := evidenceOptions {} book.hints book.coercions book.normNum
  let scopes := (← get).commandState.scopes
  let known := List.replicate (scopes.length - min scopes.length book.fileOpts.length)
    (book.fileOpts.head?.getD []) ++ book.fileOpts.drop (book.fileOpts.length - scopes.length)
  let fileOpts := (scopes.zip known).map fun (sc, file) => evidenceKeys.foldl (fun acc k =>
    match sc.opts.find k with
    | some v => if ours.find k != some v then (k, v) :: acc.filter (·.1 != k) else acc
    | none => acc.filter (·.1 != k)) file
  book := { book with hints, coercions, normNum, fileOpts }
  modify fun st => { st with commandState.scopes := st.commandState.scopes.map fun sc =>
    { sc with opts := evidenceOptions sc.opts hints coercions normNum } }
  if done then return count + 1 else loop refs root header fileMap out book (count + 1)

partial def check (count : Nat := 0) : FrontendM Nat := do
  let done ← processCommand
  let mut count := count
  let st := (← get).commandState
  for msg in st.messages.toList ++ (snapshotMessages st).toList do
    if msg.severity == .error then
      count := count + 1
      if count ≤ 60 then IO.eprintln (← msg.toString)
  modify fun st => { st with commandState.messages := {}, commandState.snapshotTasks := #[],
                             commands := #[] }
  if done then return count else check count

/-- the statement of `root` and the axioms its proof rests on, so a pruned file can be checked to
prove the very same theorem without `sorry` -/
def statement (root : Name) (inputCtx : Parser.InputContext) (env : Environment) :
    IO (List (String × Json)) := do
  let root := if env.contains root then root else mkPrivateName env root
  match env.find? root with
  | none => return [("statement", Json.null)]
  | some ci =>
    let ctx : Core.Context := { fileName := inputCtx.fileName, fileMap := inputCtx.fileMap }
    let (axioms, _) ← (collectAxioms root : CoreM (Array Name)).toIO ctx { env }
    -- universe names, like binder names, are not part of what is stated, only how many and where
    let us := (List.range ci.levelParams.length).map fun i => Level.param (.mkSimple s!"u{i}")
    let type := (expandShared env (cached env) ci.type).instantiateLevelParams ci.levelParams us
    return [("statement", toJson s!"{us.length} {canonical 0 type}"),
      ("axioms", Json.arr (axioms.map fun n => Json.str n.toString))]

/-- elaborates the whole file with nothing but what a plain compile sets, then writes how many
errors it had and what `root` states -/
def checked (root : Name) (inputCtx : Parser.InputContext) (state : Frontend.State) :
    IO Json := do
  let (errors, s) ← (check).run { inputCtx } |>.run state
  let errors := errors + (s.commandState.messages.toList.filter (·.severity == .error)).length
  return Json.mkObj ([("errors", toJson errors)] ++ (← statement root inputCtx s.commandState.env))

unsafe def main (args : List String) : IO Unit := do
  let (path, target, mode) ← match args with
    | [path, target, "--root", root] => pure (path, target, (false, root.toName))
    | [path, target, "--check", root] => pure (path, target, (true, root.toName))
    | _ => throw <| IO.userError "usage: deps FILE OUT (--root | --check) ROOT"
  let (checking, root) := mode
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  -- proofs are compiled as the module `Upload`, which lean puts in the names it makes for instances
  -- and hygiene, so both runs here use that one too
  let (env, messages) ← processHeader header {} messages inputCtx (mainModule := `Upload)
  -- elaboration is synchronous here so each command's trees and messages are complete when it
  -- returns, which would put every proof on the main thread and its small fixed stack. a
  -- dedicated thread gets lean's own thread stack instead, the one a normal compile's workers
  -- use, and `--tstack` can raise it on every platform where `ulimit` does not exist
  if checking then
    let commandState := Command.mkState env messages
      (Options.empty.setBool `Elab.async false)
    let state : Frontend.State := { commandState, parserState, cmdPos := parserState.pos }
    let task ← IO.asTask (prio := .dedicated) (checked root inputCtx state)
    match ← IO.wait task with
    | .ok json => IO.FS.writeFile target (json.compress ++ "\n")
    | .error e => throw e
    return
  let opts := evidenceOptions (Options.empty.setBool `Elab.async false) false
  let commandState := { Command.mkState env messages opts with infoState.enabled := true }
  let state : Frontend.State := { commandState, parserState, cmdPos := parserState.pos }
  let out ← IO.FS.Handle.mk target .write
  let task ← IO.asTask (prio := .dedicated) do
    let refs ← globalRefs env
    (loop refs root env inputCtx.fileMap out {} 0).run { inputCtx } |>.run state
  match ← IO.wait task with
  | .ok (count, s) =>
    out.putStrLn (Json.compress <| Json.mkObj (("root", toJson root.toString) ::
      (← statement root inputCtx s.commandState.env)))
    out.flush
    IO.eprintln s!"{count} commands"
  | .error e => throw e
