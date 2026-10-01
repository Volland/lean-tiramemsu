/-
Deterministic database fixtures written by the pinned Rust build through its driver, from a
seed (core `StdGen`): asserts over a small vocabulary with optional valid times, retractions,
supersedes and meta statements. Used by the refinement tests and the scenarios. Tooling only.
-/
import Oracle.Driver

namespace Oracle

open Tiramemsu.Json

def iri (s : String) : Json := .obj #[("iri", .str s!"http://ex/{s}")]

/-- One random object term: an IRI, a short or long string, an integer or a double. -/
def randObject (g : StdGen) : Json × StdGen :=
  let (k, g) := randNat g 0 5
  let (v, g) := randNat g 0 9
  let o := match k with
    | 0 | 1 => iri s!"o{v}"
    | 2 => .str s!"v{v}"
    | 3 => .str s!"a longer literal number {v}"
    | 4 => .int (v * 1000003)
    | _ => .num s!"{v}.5"
  (o, g)

/-- Writes `txs` random transactions into `path` with the Rust driver. Returns the number of
transactions that committed. -/
def writeFixture (rust : Driver) (path : System.FilePath) (seed txs : Nat) : IO Nat := do
  for suf in ["", "-wal", "-shm"] do
    let f : System.FilePath := path.toString ++ suf
    if ← f.pathExists then IO.FS.removeFile f
  let _ ← rust.call! "open" (.obj #[("path", .str path.toString)])
  let mut g := mkStdGen seed
  let mut live : Array Int := #[]
  let mut committed := 0
  for _ in [0:txs] do
    let (nOps, g1) := randNat g 1 6
    g := g1
    let mut ops : Array Json := #[]
    let mut used : Array Int := #[]
    for _ in [0:nOps] do
      let (kind, g1) := randNat g 0 9
      g := g1
      if kind ≤ 5 || live.isEmpty then
        let (s, g1) := randNat g 0 9
        let (p, g2) := randNat g1 0 4
        let (o, g3) := randObject g2
        let (vt, g4) := randNat g3 0 3
        g := g4
        let valid := if vt == 0 then #[("validFrom", Json.int 1000), ("validTo", Json.int 2000)] else #[]
        ops := ops.push (.obj (#[("op", .str "assert"), ("s", iri s!"s{s}"), ("p", iri s!"p{p}"),
                                 ("o", o)] ++ valid))
      else
        let (j, g1) := randNat g 0 (live.size - 1)
        g := g1
        let e := live[j]!
        if used.contains e then continue
        used := used.push e
        if kind ≤ 7 then
          ops := ops.push (.obj #[("op", .str "retract"), ("eid", .int e)])
        else if kind == 8 then
          let (o, g1) := randObject g
          g := g1
          ops := ops.push (.obj #[("op", .str "supersede"), ("eid", .int e),
                                  ("patch", .obj #[("o", o)])])
        else
          let (o, g1) := randObject g
          g := g1
          ops := ops.push (.obj #[("op", .str "meta"), ("p", iri "source"), ("o", o)])
    match ← rust.call "transact" (.obj #[("ops", .arr ops)]) with
    | .ok rep =>
      committed := committed + 1
      let asserted := ((rep.getArr? "asserted").getD #[]).filterMap fun | .int i => some i | _ => none
      let retracted := ((rep.getArr? "retracted").getD #[]).filterMap fun r => r.getInt? "eid"
      live := (live.filter (!retracted.contains ·)) ++ asserted
    | .err _ _ => pure ()   -- e.g. an assert that conflicts; the transaction is discarded
  let _ ← rust.call! "close"
  return committed

end Oracle
