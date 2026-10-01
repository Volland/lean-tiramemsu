/-
The proof-policy rules. Environment facts (axioms, unsafe/opaque constants, overrides, imports)
are read from the built environments; only source-level facts (`native_decide`, `bv_decide`)
and repository files use text scans. Tooling only: never linked into the runtime.
-/
import Lean
import Policy.Index

namespace Policy

open Lean

--# @lat: [[verification#Proof Policy#Policy Checker]]

/-- A rule violation: the rule identifier, what violates it and why. -/
structure Violation where
  rule : String
  subject : String
  detail : String := ""
  deriving Repr, Inhabited

instance : ToString Violation where
  toString v := s!"[{v.rule}] {v.subject}" ++ (if v.detail.isEmpty then "" else s!": {v.detail}")

/-- What the rules check, and against which lists. -/
structure Config where
  /-- Module roots of the checked libraries (and executable roots). -/
  libRoots : Array Name
  /-- Root of the proof library (indexed theorems must live there). -/
  proofRoots : Array Name
  /-- Prefixes of verified modules. -/
  verified : Array Name
  /-- Roots of the runtime import closure. -/
  runtimeRoots : Array Name
  /-- Module roots the runtime closure may contain. -/
  runtimeAllowed : Array Name
  /-- Toolchain modules the runtime may import (`policy/toolchain-imports.txt`). -/
  toolchainImports : Array Name
  /-- Theorems allowed `Lean.ofReduceBool` (`policy/bv-decide-allowlist.txt`). -/
  bvAllowlist : Array Name
  /-- Prefix of the codec proof modules, the only home of `bv_decide`. -/
  codecPrefix : Name
  deriving Repr, Inhabited

/-- The axioms every theorem may use. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv := modify

/-- The axioms a constant depends on. -/
def axiomsOf (env : Environment) (c : Name) : Array Name :=
  (collectAxioms c : StateM Environment (Array Name)).run' env |>.run

def moduleOf? (env : Environment) (c : Name) : Option Name := do
  let i ← env.getModuleIdxFor? c
  env.header.moduleNames[i.toNat]?

def Config.isLib (cfg : Config) (m : Name) : Bool := cfg.libRoots.contains m.getRoot
def Config.isVerified (cfg : Config) (m : Name) : Bool := cfg.verified.any (·.isPrefixOf m)

/-- Modules of the checked libraries with their index in the environment. -/
def libModules (env : Environment) (cfg : Config) : Array (Nat × Name) := Id.run do
  let mut out := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if cfg.isLib m then out := out.push (i, m)
  return out

/-- Axioms outside the standard set that a theorem may not use. Missing proofs and user
axioms are left to their own rules. -/
def badAxioms (env : Environment) (cfg : Config) (c : Name) : Array Name :=
  let allowed := if cfg.bvAllowlist.contains c then
      standardAxioms ++ axiomsOf env ``Lean.ofReduceBool
    else standardAxioms
  (axiomsOf env c).filter fun a =>
    !allowed.contains a && a != ``sorryAx && !((moduleOf? env a).map cfg.isLib |>.getD false)

/-- `@[csimp]` replacements declared in the checked libraries (read from the imported module
data, since extension states are not loaded): replaced constant ↦ replacement. -/
def csimpMap (env : Environment) (cfg : Config) : Std.HashMap Name Name := Id.run do
  let mut out := {}
  for (i, _) in libModules env cfg do
    for e in Compiler.CSimp.ext.ext.getModuleEntries env i (level := .private) do
      let entry := match e with
        | .global x => x
        | .scoped _ x => x
      out := out.insert entry.fromDeclName entry.toDeclName
  return out

/-- Rules over the elaborated declarations: `no-sorry`, `no-user-axiom`, `axiom-set`,
`verified-total`, `override-csimp`, `verified-imports`. -/
def envRules (env : Environment) (cfg : Config) : Array Violation := Id.run do
  let mut out := #[]
  let csimp := csimpMap env cfg
  for (i, m) in libModules env cfg do
    let some md := env.header.moduleData[i]? | continue
    for c in md.constNames do
      let some ci := env.find? c | continue
      if ci matches .axiomInfo _ then
        out := out.push { rule := "no-user-axiom", subject := c.toString, detail := s!"axiom in {m}" }
      let axs := axiomsOf env c
      if axs.contains ``sorryAx then
        out := out.push { rule := "no-sorry", subject := c.toString, detail := "depends on sorry" }
      if ci matches .thmInfo _ then
        let bad := badAxioms env cfg c
        unless bad.isEmpty do
          out := out.push { rule := "axiom-set", subject := c.toString,
                            detail := s!"axioms {axs.toList}" }
      if cfg.isVerified m then
        let isOpaque := ci matches .opaqueInfo _
        if ci.isUnsafe || isOpaque then
          let detail := if ci.isUnsafe then s!"unsafe in verified module {m}"
            else s!"opaque or partial in verified module {m}"
          out := out.push { rule := "verified-total", subject := c.toString, detail }
        else
          let impl := Compiler.getImplementedBy? env c
          if impl.isSome || isExtern env c then
            let ok := match csimp[c]? with
              | some target => impl.all (· == target)
              | none => false
            unless ok do
              let detail := "implemented_by/extern without a @[csimp] theorem equating it"
              out := out.push { rule := "override-csimp", subject := c.toString, detail }
    if cfg.isVerified m then
      for imp in md.imports do
        let r := imp.module.getRoot
        unless r == `Init || r == `Std || cfg.isVerified imp.module do
          out := out.push { rule := "verified-imports", subject := m.toString,
                            detail := s!"imports {imp.module}" }
  return out

/-- The runtime import closure: every module reachable from the runtime roots has an allowed
root or is an allowlisted toolchain module (whose own imports are then not inspected). -/
def runtimeImports (env : Environment) (cfg : Config) : Array Violation := Id.run do
  let names := env.header.moduleNames
  let mut idx : Std.HashMap Name Nat := {}
  for h : i in [0:names.size] do idx := idx.insert names[i] i
  let mut parent : Std.HashMap Name Name := {}
  let mut seen : Std.HashSet Name := {}
  let mut queue := cfg.runtimeRoots
  let mut out := #[]
  for r in cfg.runtimeRoots do seen := seen.insert r
  let mut qi := 0
  while h : qi < queue.size do
    let m := queue[qi]
    qi := qi + 1
    let allowed := cfg.runtimeAllowed.contains m.getRoot
    let listed := cfg.toolchainImports.contains m
    if !allowed && !listed then
      let mut chain := [m]
      let mut cur := m
      for _ in [0:names.size] do
        match parent[cur]? with
        | some p => chain := p :: chain; cur := p
        | none => break
      out := out.push { rule := "runtime-imports", subject := m.toString,
                        detail := "import chain " ++ " -> ".intercalate (chain.map toString) }
      continue
    if listed then continue
    let some i := idx[m]? | continue
    let some md := env.header.moduleData[i]? | continue
    for imp in md.imports do
      unless seen.contains imp.module do
        seen := seen.insert imp.module
        parent := parent.insert imp.module m
        queue := queue.push imp.module
  return out

/-- Allowlist entries must be theorems declared in codec proof modules. -/
def allowlistRule (env : Environment) (cfg : Config) : Array Violation :=
  cfg.bvAllowlist.filterMap fun n =>
    match moduleOf? env n with
    | some m => if cfg.codecPrefix.isPrefixOf m then none
      else some { rule := "bv-allowlist-scope", subject := n.toString,
                  detail := s!"declared in {m}, not in {cfg.codecPrefix}" }
    | none => some { rule := "bv-allowlist-scope", subject := n.toString,
                     detail := "no such theorem" }

/-- Source rules: `no-native-decide` everywhere, `bv_decide` only under the codec prefix. -/
def sourceRules (files : Array (Name × System.FilePath)) (cfg : Config) : IO (Array Violation) := do
  let mut out := #[]
  for (m, f) in files do
    let lines := ((← IO.FS.readFile f).splitOn "\n").toArray
    for h : i in [0:lines.size] do
      let l := lines[i]
      let has (needle : String) := (l.splitOn needle).length > 1
      if has "native_decide" || has "decide +native" || has "native := true" then
        out := out.push { rule := "no-native-decide", subject := s!"{m}:{i + 1}",
                          detail := l.trimAscii.toString }
      if has "bv_decide" && !cfg.codecPrefix.isPrefixOf m then
        out := out.push { rule := "bv-decide-scope", subject := s!"{m}:{i + 1}",
                          detail := "bv_decide outside the codec proofs" }
  return out

/-- No C, C++ or header file outside `abi/` and build output (symbolic links not followed). -/
partial def strayC (root : System.FilePath) : IO (Array Violation) := do
  let skipTop := #[".lake", ".oracle", ".git", "abi"]
  let exts := #["c", "h", "cc", "cpp", "cxx", "hh", "hpp", "hxx"]
  let rec go (dir : System.FilePath) (rel : String) : IO (Array Violation) := do
    let mut out := #[]
    for e in ← dir.readDir do
      let relPath := if rel.isEmpty then e.fileName else rel ++ "/" ++ e.fileName
      let md ← e.path.symlinkMetadata
      if md.type == .symlink then continue
      if md.type == .dir then
        if rel.isEmpty && skipTop.contains e.fileName then continue
        out := out ++ (← go e.path relPath)
      else if exts.any (e.path.extension == some ·) then
        out := out.push { rule := "no-stray-c", subject := relPath,
                          detail := "C/C++ source outside abi/" }
    return out
  go root ""

/-- The theorem-index rule. Requirements from sources in `strict` fail when unindexed or when
an indexed theorem is missing; other sources only report them as pending. -/
def indexRule (env : Environment) (cfg : Config) (reqs : Array Requirement)
    (index : Array IndexEntry) (strict : String → Bool) : Array Violation × Array String := Id.run do
  let mut out := #[]
  let mut pending := #[]
  for r in reqs do
    unless r.proven do continue
    let entries := index.filter fun e => e.spec == r.capability && e.requirement == r.name
    if entries.all (·.theorems.isEmpty) then
      let what := s!"{r.capability}: {r.name}"
      if strict r.source then
        out := out.push { rule := "theorem-index", subject := what,
                          detail := "proven requirement has no theorem in the index" }
      else pending := pending.push s!"{what} ({r.source}): no index entry"
  for e in index do
    let what := s!"{e.spec}: {e.requirement}"
    match reqs.find? fun r => r.capability == e.spec && r.name == e.requirement with
    | none => out := out.push { rule := "theorem-index", subject := what,
                                detail := "names a requirement that does not exist" }
    | some r =>
      if !r.proven then
        out := out.push { rule := "theorem-index", subject := what,
                          detail := "names a requirement that is not proven" }
      for t in e.theorems do
        let n := t.toName
        match env.find? n with
        | none =>
          if strict r.source then
            out := out.push { rule := "theorem-index", subject := what,
                              detail := s!"missing theorem {t}" }
          else pending := pending.push s!"{what} ({r.source}): theorem {t} not written yet"
        | some ci =>
          let inProofs := (moduleOf? env n).map (cfg.proofRoots.contains ·.getRoot) |>.getD false
          if !(ci matches .thmInfo _) || !inProofs then
            out := out.push { rule := "theorem-index", subject := what,
                              detail := s!"{t} is not a theorem of the proof library" }
          else
            let bad := badAxioms env cfg n
            if !bad.isEmpty || (axiomsOf env n).contains ``sorryAx then
              out := out.push { rule := "theorem-index", subject := what,
                                detail := s!"{t} fails the axiom rule: {(axiomsOf env n).toList}" }
  return (out, pending)

end Policy
