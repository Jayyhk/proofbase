import Lean

open Lean

-- map a Lean constant's tag to the kind of string we store
def kindOf : ConstantInfo -> String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

-- a read only environment for the compiled declarations
abbrev EnvM := ReaderT Environment Id

-- required so we can run collectAxioms
instance : MonadEnv EnvM where
  getEnv := read
  modifyEnv _ := pure ()

-- Lean's built-in axiom collector. used to check our work
def axiomsOf (env : Environment) (n : Name) : Array Name :=
  (collectAxioms (m := EnvM) n).run env

-- memoizes each name's axiom set so we don't recompute it for dfs
abbrev AxCache := IO.Ref (Std.HashMap Name NameSet)

-- everything in a plus everything in b
def union (a b : NameSet) : NameSet := b.toList.foldl (fun s n => s.insert n) a

-- array of names to a set of names
def toSet (a : Array Name) : NameSet := a.foldl (fun s n => s.insert n) {}

-- compute transitive axiom set for one declaration via dfs
partial def footprint (env : Environment) (cache : AxCache) (open_ : NameSet) (c : Name) :
    IO (NameSet × Bool) := do
  if let some r := (<- cache.get)[c]? then
    return (r, false)
  if open_.contains c then
    return ({}, true)
  let some info := env.find? c | return ({}, false)
  let mut acc : NameSet := {}
  let mut cyclic := false
  let mut deps := info.getUsedConstantsAsSet.toList
  match info with
  | .axiomInfo v => acc := acc.insert c; deps := v.type.getUsedConstantsAsSet.toList
  | .quotInfo _ => deps := []
  | .inductInfo v => deps := deps ++ v.ctors
  | _ => pure ()
  for d in deps do
    let (s, hit) <- footprint env cache (open_.insert c) d
    acc := union acc s
    cyclic := cyclic || hit
  -- use Lean's axiom collector instead for cycles
  let r := if cyclic then toSet (axiomsOf env c) else acc
  cache.modify (·.insert c r)
  return (r, false)

-- which module a declaration lives in
def moduleOf (env : Environment) (mods : Array Name) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => mods[i.toNat]!

-- true if a declaration belongs to the proof we are auditing
def isOwn (roots : Array Name) : Option Name -> Bool
  | some m => roots.any fun r => r == m || r.isPrefixOf m
  | none => false

-- a declaration's source line range if it exists
def rangeOf (env : Environment) (n : Name) : Option DeclarationRange :=
  (declRangeExt.find? (level := .exported) env n
    <|> declRangeExt.find? (level := .server) env n).map (·.range)

-- Lean generates these from something the user wrote. only the user's own go in the graph
def isDerived (env : Environment) (n : Name) : Bool := Id.run do
  if env.isConstructor n || env.isProjectionFn n then
    return true
  -- an anonymous instance is named inst<TypeName>, the user would have named it themselves
  if let .str _ s := n then
    if s.startsWith "inst" then
      match s.toList.drop 4 with
      | c :: _ => if c.isUpper then return true
      | [] => pure ()
  -- an attribute's lemma sits at the same source range as the declaration it came from
  let .str parent _ := n | return false
  let some pr := rangeOf env parent | return false
  let some r := rangeOf env n | return false
  return pr.pos.line <= r.pos.line && r.endPos.line <= pr.endPos.line

-- converts an optional string into json (null if absent)
def optStr : Option String -> Json
  | some s => toJson s
  | none => Json.null

-- builds one declaration's json metadata
def nodeJson (env : Environment) (ax : AxCache)
    (name : Name) (info : ConstantInfo) : IO Json := do
  let (axs, _) <- footprint env ax {} name
  let r := rangeOf env name
  return Json.mkObj [
    ("name", toJson name.toString),
    ("kind", toJson (kindOf info)),
    ("generated", toJson (name.isInternalDetail || isDerived env name)),
    ("lineStart", match r with | some r => toJson r.pos.line | none => Json.null),
    ("lineEnd", match r with | some r => toJson r.endPos.line | none => Json.null),
    ("axioms", toJson ((axs.toList.filter (· != name)).map Name.toString).toArray)
  ]

-- read a file, none if it's missing
def readFile? (p : String) : IO (Option String) := do
  if !(<- System.FilePath.pathExists p) then return none
  return some (<- IO.FS.readFile p)

-- read a one-line file, stripping newlines
def readLine? (p : String) : IO (Option String) := do
  return (<- readFile? p).map fun s => s.replace "\n" "" |>.replace "\r" ""

-- parse args: --verify, -o, anything else is a module name
def parseArgs : List String -> Bool × Option String × List String
  | [] => (false, none, [])
  | "--verify" :: rest => let (_, o, m) := parseArgs rest; (true, o, m)
  | "-o" :: p :: rest => let (v, _, m) := parseArgs rest; (v, some p, m)
  | a :: rest => let (v, o, m) := parseArgs rest; (v, o, a :: m)

-- load the compiled proof, walk its declarations, and write the graph json (nodes, edges, axioms)
def main (args : List String) : IO Unit := do
  initSearchPath (<- findSysroot)
  let (verify, outArg, mods) := parseArgs args
  let out := outArg.getD "graph.json"
  let toolchain <- readLine? "./lean-toolchain"
  -- roots = the modules to audit, passed on the command line
  let roots := (mods.map String.toName).toArray
  if roots.isEmpty then
    throw <| IO.userError "no module given -- pass a module name to audit"
  let proof := Json.mkObj [
    ("leanVersion", optStr toolchain)
  ]
  let env <- importModules (roots.map fun r => { module := r }) {}
  let mods := env.allImportedModuleNames
  let mut nodes := #[]
  let mut edges := #[]
  let mut refs : NameSet := {}
  let ax <- IO.mkRef {}
  let mut bad := 0
  -- walk every constant. only process the proof's own declarations
  for (name, info) in env.constants do
    if !isOwn roots (moduleOf env mods name) then
      continue
    nodes := nodes.push (<- nodeJson env ax name info)
    let (fp, _) <- footprint env ax {} name
    -- if --verify then cross-check our footprint against Lean's collector
    if verify && (fp.toList.map Name.toString).toArray.qsort (· < ·)
        != ((axiomsOf env name).map Name.toString).qsort (· < ·) then
      IO.eprintln s!"MISMATCH {name}"
      bad := bad + 1
    for a in fp do
      refs := refs.insert a
    -- direct uses become graph edges
    for dep in info.getUsedConstantsAsSet.toList do
      refs := refs.insert dep
      if dep != name && isOwn roots (moduleOf env mods dep) then
        edges := edges.push <| Json.mkObj [
          ("from", toJson name.toString),
          ("to", toJson dep.toString)
        ]
  -- add external axioms (e.g. Classical.choice) as nodes and skip other library constants
  let mut externals := 0
  for r in refs do
    if isOwn roots (moduleOf env mods r) then
      continue
    let some info := env.find? r | continue
    if !(info matches .axiomInfo _) then
      continue
    nodes := nodes.push (<- nodeJson env ax r info)
    externals := externals + 1
  IO.eprintln s!"environment: {env.constants.fold (fun n _ _ => n + 1) 0}"
  IO.eprintln s!"modules: {roots.size} nodes: {nodes.size} (external axioms: {externals}) \
edges: {edges.size}"
  if verify then IO.eprintln s!"verified against collectAxioms, mismatches: {bad}"
  -- write the final {proof, nodes, edges} json
  let json := (Json.mkObj [("proof", proof),
    ("nodes", Json.arr nodes), ("edges", Json.arr edges)]).compress
  IO.FS.writeFile out json
  IO.eprintln s!"wrote {out}"
