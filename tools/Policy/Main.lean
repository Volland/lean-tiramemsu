/-
`policy-check`: runs every proof-policy rule on the built libraries, or (`--self-test`) on the
seeded fixtures. Exit status 1 on any violation.

  policy-check                         all rules; theorem index strict for project specs,
                                       report-only for active changes
  policy-check --change <name> --strict  also strict on that change's specs (pre-archive run)
  policy-check --self-test             each seeded fixture is rejected by exactly its rule
-/
import Policy.Rules

open Lean Policy

/-- Non-empty, non-comment lines of a list file, as names. -/
def readList (p : System.FilePath) : IO (Array Name) := do
  if !(← p.pathExists) then return #[]
  let lines := (← IO.FS.readFile p).splitOn "\n" |>.map (·.trimAscii.toString)
  return (lines.filter fun l => !l.isEmpty && !l.startsWith "#").toArray.map (·.toName)

/-- The Lean source files of a directory tree, with their module names. -/
partial def leanFiles (dir : System.FilePath) (pre : Name) : IO (Array (Name × System.FilePath)) := do
  if !(← dir.isDir) then return #[]
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then
      out := out ++ (← leanFiles e.path (pre.str e.fileName))
    else if e.path.extension == some "lean" then
      out := out.push (pre.str (e.fileName.dropEnd 5).toString, e.path)
  return out

def importEnv (mods : Array Name) : IO Environment := do
  importModules (mods.map fun m => { module := m }) {} (loadExts := false)

def report (vs : Array Violation) : IO Unit :=
  for v in vs do IO.println (toString v)

def repoConfig : IO Config := do
  return {
    libRoots := #[`Tiramemsu, `TiramemsuProofs, `Main]
    proofRoots := #[`TiramemsuProofs]
    verified := ← readList "policy/verified-modules.txt"
    runtimeRoots := #[`Tiramemsu, `Main]
    runtimeAllowed := #[`Init, `Std, `SQLite, `Tiramemsu, `Main]
    toolchainImports := ← readList "policy/toolchain-imports.txt"
    bvAllowlist := ← readList "policy/bv-decide-allowlist.txt"
    codecPrefix := `TiramemsuProofs.Codec }

def checkRepo (change : Option String) (strictChange : Bool) : IO UInt32 := do
  let cfg ← repoConfig
  let env ← importEnv #[`Tiramemsu, `TiramemsuProofs, `Main]
  let files := (← leanFiles "src" .anonymous) ++ (← leanFiles "TiramemsuProofs" `TiramemsuProofs)
    ++ #[(`TiramemsuProofs, ("TiramemsuProofs.lean" : System.FilePath)),
         (`Main, ("Main.lean" : System.FilePath))]
  let mut vs := envRules env cfg ++ runtimeImports env cfg ++ allowlistRule env cfg
  vs := vs ++ (← sourceRules files cfg) ++ (← strayC ".")
  let reqs ← loadRequirements "."
  let index ← loadIndex "policy/theorem-index.toml"
  let strict (src : String) := src == "project" || (strictChange && change == some src)
  let (iv, pending) := indexRule env cfg reqs index strict
  vs := vs ++ iv
  report vs
  for p in pending do IO.println s!"pending: {p}"
  let proven := reqs.filter (·.proven)
  IO.println s!"policy-check: {vs.size} violation(s); {proven.size} proven requirement(s), {index.size} index entr(y/ies), {pending.size} pending"
  return if vs.isEmpty then 0 else 1

/-- Theorems of the proof library that depend on a `bv_decide` certificate axiom, one per line
(the content `policy/bv-decide-allowlist.txt` must cover). -/
def listBv : IO UInt32 := do
  let cfg ← repoConfig
  let env ← importEnv #[`Tiramemsu, `TiramemsuProofs, `Main]
  let mut out := #[]
  for (i, m) in libModules env cfg do
    unless cfg.proofRoots.contains m.getRoot do continue
    let some md := env.header.moduleData[i]? | continue
    for c in md.constNames do
      let some ci := env.find? c | continue
      unless ci matches .thmInfo _ do continue
      if (axiomsOf env c).any (isBvDecideAxiom env) then out := out.push c.toString
  for n in out.qsort (· < ·) do IO.println n
  return 0

/-! ## Self-test -/

structure Case where
  name : String
  modules : Array Name := #[]
  cfg : Config → Config := id
  /-- Extra violations of the case (source, repository and index rules). -/
  extra : Environment → Config → IO (Array Violation) := fun _ _ => pure #[]
  expect : Array String

def fixtureConfig : Config := {
  libRoots := #[`Fixture], proofRoots := #[`Fixture], verified := #[], runtimeRoots := #[],
  runtimeAllowed := #[`Init, `Std, `SQLite, `Fixture], toolchainImports := #[],
  bvAllowlist := #[], codecPrefix := `Fixture.Codec }

def fixtureFile (m : Name) : System.FilePath :=
  ("tools/Policy/Fixtures" : System.FilePath) / (System.mkFilePath (m.components.map toString)).toString
    |>.addExtension "lean"

def sourcesOf (m : Name) (_ : Environment) (cfg : Config) : IO (Array Violation) :=
  sourceRules #[(m, fixtureFile m)] cfg

def indexCase (indexFile : String) (strictChange : Bool := false) :
    Environment → Config → IO (Array Violation) := fun env cfg => do
  let root : System.FilePath := "tools/Policy/Fixtures/index"
  let reqs ← loadRequirements root
  let index ← loadIndex (root / indexFile)
  let (vs, pending) := indexRule env cfg reqs index
    (fun s => s == "project" || (strictChange && s == "pending-change"))
  for p in pending do IO.println s!"    pending: {p}"
  return vs

def strayCase (_ : Environment) (_ : Config) : IO (Array Violation) := do
  let dir : System.FilePath := ".lake" / "policy-selftest"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll (dir / "src"); IO.FS.createDirAll (dir / "abi"); IO.FS.createDirAll (dir / ".lake")
  IO.FS.writeFile (dir / "src" / "stray.c") "int x;\n"
  IO.FS.writeFile (dir / "abi" / "shim.c") "int y;\n"
  IO.FS.writeFile (dir / ".lake" / "gen.c") "int z;\n"
  let vs ← strayC dir
  IO.FS.removeDirAll dir
  return vs

def verifiedOnly (m : Name) (c : Config) : Config := { c with verified := #[m] }

def cases : Array Case := #[
  { name := "sorry in a proof", modules := #[`Fixture.Sorry], expect := #["no-sorry"] },
  { name := "user axiom", modules := #[`Fixture.UserAxiom], expect := #["no-user-axiom"] },
  { name := "Lean.ofReduceBool outside the allowlist", modules := #[`Fixture.ReduceBool],
    expect := #["axiom-set"] },
  { name := "standard axioms accepted", modules := #[`Fixture.Clean],
    cfg := verifiedOnly `Fixture.Clean, expect := #[] },
  { name := "partial def in a verified module", modules := #[`Fixture.Partial],
    cfg := verifiedOnly `Fixture.Partial, expect := #["verified-total"] },
  { name := "shell code may be partial", modules := #[`Fixture.Partial], expect := #[] },
  { name := "implemented_by without csimp", modules := #[`Fixture.Override],
    cfg := verifiedOnly `Fixture.Override, expect := #["override-csimp"] },
  { name := "implemented_by with csimp accepted", modules := #[`Fixture.CsimpOk],
    cfg := verifiedOnly `Fixture.CsimpOk, expect := #[] },
  { name := "verified module imports the SQLite binding", modules := #[`Fixture.VerifiedImport],
    cfg := verifiedOnly `Fixture.VerifiedImport, expect := #["verified-imports"] },
  { name := "native_decide", modules := #[`Fixture.NativeDecide],
    extra := sourcesOf `Fixture.NativeDecide, expect := #["no-native-decide"] },
  { name := "bv_decide outside the codec", modules := #[`Fixture.BvDecide],
    extra := sourcesOf `Fixture.BvDecide, expect := #["bv-decide-scope"] },
  { name := "bv_decide in an allowlisted codec theorem accepted", modules := #[`Fixture.Codec.BvOk],
    cfg := fun c => { c with bvAllowlist := #[`Fixture.Codec.BvOk.and_or_add] },
    extra := sourcesOf `Fixture.Codec.BvOk, expect := #[] },
  { name := "bv_decide in a codec theorem missing from the allowlist", modules := #[`Fixture.Codec.BvOk],
    extra := sourcesOf `Fixture.Codec.BvOk, expect := #["axiom-set"] },
  { name := "allowlist entry outside the codec", modules := #[`Fixture.Clean],
    cfg := fun c => { c with bvAllowlist := #[`Fixture.Clean.std_axioms] },
    expect := #["bv-allowlist-scope"] },
  { name := "Mathlib import in runtime code", modules := #[`Fixture.MathlibImport],
    cfg := fun c => { c with runtimeRoots := #[`Fixture.MathlibImport] },
    expect := #["runtime-imports"] },
  { name := "unlisted toolchain module", modules := #[`Fixture.LeanImport],
    cfg := fun c => { c with runtimeRoots := #[`Fixture.LeanImport] },
    expect := #["runtime-imports"] },
  { name := "listed toolchain module accepted", modules := #[`Fixture.LeanImport],
    cfg := fun c => { c with runtimeRoots := #[`Fixture.LeanImport],
                             toolchainImports := #[`Lean.Data.Json.Basic] },
    expect := #[] },
  { name := "stray C file", modules := #[`Fixture.Clean], extra := strayCase,
    expect := #["no-stray-c"] },
  { name := "index names a missing theorem", modules := #[`Fixture.Clean],
    extra := indexCase "index-missing-theorem.toml", expect := #["theorem-index"] },
  { name := "unindexed proven requirement", modules := #[`Fixture.Clean],
    extra := indexCase "index-unindexed.toml", expect := #["theorem-index"] },
  { name := "index names a requirement that is not proven", modules := #[`Fixture.Clean],
    extra := indexCase "index-not-proven.toml", expect := #["theorem-index"] },
  { name := "complete index accepted, pending change reported", modules := #[`Fixture.Clean],
    extra := indexCase "index-ok.toml", expect := #[] },
  { name := "pending change fails its pre-archive run", modules := #[`Fixture.Clean],
    extra := indexCase "index-ok.toml" (strictChange := true), expect := #["theorem-index"] }
]

def selfTest : IO UInt32 := do
  let mut failures := 0
  for c in cases do
    let cfg := c.cfg fixtureConfig
    let env ← importEnv c.modules
    let vs := envRules env cfg ++ runtimeImports env cfg ++ allowlistRule env cfg
      ++ (← c.extra env cfg)
    let got := (vs.map (·.rule)).toList.eraseDups.toArray.qsort (· < ·)
    let want := c.expect.qsort (· < ·)
    if got == want then
      IO.println s!"ok   {c.name}: {if want.isEmpty then "accepted" else s!"rejected by {want.toList}"}"
      for v in vs do IO.println s!"       {v}"
    else
      failures := failures + 1
      IO.println s!"FAIL {c.name}: expected {want.toList}, got {got.toList}"
      report vs
  IO.println s!"policy self-test: {cases.size - failures}/{cases.size} cases as expected"
  return if failures == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | ["--self-test"] => selfTest
  | ["--list-bv"] => listBv
  | [] => checkRepo none false
  | ["--change", c] => checkRepo (some c) false
  | ["--change", c, "--strict"] | ["--strict", "--change", c] => checkRepo (some c) true
  | _ =>
    IO.eprintln "usage: policy-check [--change <name> [--strict]] | --self-test"
    return 2
