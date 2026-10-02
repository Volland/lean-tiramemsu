/-
The `tiramemsu` command-line tool: `tiramemsu <db> <command> …` over the Lean API.

Commands: `info`, `assert s p o [--valid-from t] [--valid-to t]`, `retract eid`,
`triples [--s t] [--p t] [--o t]`, `values s key`, `dependents eid`,
`path start expr [--mode m] [--max-hops n] [--graph g]… [--time-respecting[=t]]`, `bundle eid`,
`import-bundle file|-`. Read commands take `--as-of <t or RFC 3339>`, `--history` and
`--valid-at <date or date-time>`. Terms: `<iri>`, a CURIE over the database prefixes, a quoted
literal with `@lang` or `^^datatype`, a bare number or boolean, a skolem IRI or `K:n` for `K` in
`node`, `bnode`, `stmt`, `tx`. One JSON value per line on standard output; an error prints
`{"kind", "message"}` on standard error and exits with 1; a usage error exits with 2. Each write
command is one transaction.
Shell module (unverified; golden-tested).
-/
import Tiramemsu.Api.Api

namespace Tiramemsu.Cli

open Tiramemsu.Store Tiramemsu.Codec Tiramemsu.Engine Tiramemsu.IR Tiramemsu.Api Tiramemsu.Json
open Tiramemsu.Shell (bundleTermJ sortedText)

--# @lat: [[query#Command-Line Tool]]

def usage : String :=
  "usage: tiramemsu <db> <command> [args]\n" ++
  "  info | assert s p o [--valid-from t] [--valid-to t] | retract eid\n" ++
  "  triples [--s t] [--p t] [--o t] | values s key | dependents eid\n" ++
  "  path start expr [--mode m] [--max-hops n] [--graph g]... [--time-respecting[=t]]\n" ++
  "  bundle eid | import-bundle file|-\n" ++
  "  read options: --as-of <t or RFC 3339> | --history | --valid-at <date or date-time>\n" ++
  "       tiramemsu version [--verbose] | tiramemsu driver"

/-- A failure: a usage error (exit 2) or an API error (exit 1). -/
inductive CliError where
  | usage (msg : String)
  | api (e : ApiError)

abbrev CliM := ExceptT CliError IO

def usageErr {α : Type} (msg : String) : CliM α := throw (.usage msg)
def apiOk {α : Type} (x : Except ApiError α) : CliM α := match x with
  | .ok a => pure a
  | .error e => throw (.api e)

/-! ## Arguments -/

/-- Splits options (`--k v`, `--k=v`, `--flag`) from positional arguments. -/
def splitArgs (flags : List String) : List String → List String × List (String × Option String)
  | [] => ([], [])
  | a :: rest =>
    if a.startsWith "--" then
      let body := (a.drop 2).toString
      match body.splitOn "=" with
      | k :: v :: more => let (ps, os) := splitArgs flags rest; (ps, (k, some ("=".intercalate (v :: more))) :: os)
      | _ =>
        if flags.contains body then let (ps, os) := splitArgs flags rest; (ps, (body, none) :: os)
        else match rest with
          | v :: rest' => let (ps, os) := splitArgs flags rest'; (ps, (body, some v) :: os)
          | [] => let (ps, os) := splitArgs flags []; (ps, (body, none) :: os)
    else let (ps, os) := splitArgs flags rest; (a :: ps, os)

def opt (os : List (String × Option String)) (k : String) : Option String := (os.find? (·.1 == k)).bind (·.2)
def has (os : List (String × Option String)) (k : String) : Bool := os.any (·.1 == k)

/-- A time: an integer of epoch ms, an RFC 3339 date-time, or a date. -/
def parseInstant (s : String) : Option Int :=
  match s.toInt? with
  | some i => some i
  | none => match parseDateTime s with
    | some (ms, _) => some ms
    | none => (parseDate s).map (· * msPerDay)

/-- A term of the command line. -/
def parseTerm (vc : Path.Vocab) (t : String) : Except String Value :=
  if t.startsWith "<" && t.endsWith ">" then .ok (Value.iri ((t.drop 1).dropEnd 1).toString).canonical
  else if t.startsWith "\"" then
    let body := (t.drop 1).toString
    match body.splitOn "\"" with
    | [] => .error s!"bad literal {t}"
    | parts =>
      let lex := "\"".intercalate parts.dropLast
      let tail := parts.getLast?.getD ""
      if tail.isEmpty then .ok (literal lex none none)
      else if tail.startsWith "@" then .ok (literal lex none (some (tail.drop 1).toString))
      else if tail.startsWith "^^" then
        let dt := (tail.drop 2).toString
        let dtIri := if dt.startsWith "<" then ((dt.drop 1).dropEnd 1).toString
          else match dt.splitOn ":" with
            | [pre, l] => (vc.prefixIri pre).map (· ++ l) |>.getD dt
            | _ => dt
        .ok (literal lex (some dtIri) none)
      else .error s!"bad literal {t}"
  else if t == "true" then .ok (.bool true)
  else if t == "false" then .ok (.bool false)
  else match t.toInt? with
    | some i => .ok (Value.int i).canonical
    | none =>
      if (t.toList.all fun c => c.isDigit || c == '.' || c == '-' || c == '+') && t.contains '.' then
        .ok (literal t (some xsdDecimal) none)
      else match parseDouble t with
        | some x => if t.any (fun c => c == 'e' || c == 'E') then .ok (.double x) else .error s!"bad term {t}"
        | none =>
          match t.splitOn ":" with
          | [k, n] =>
            match k, n.toNat? with
            | "node", some i => .ok (.node i)
            | "bnode", some i => .ok (.bnode i)
            | "stmt", some i => .ok (.stmt i)
            | "tx", some i => .ok (.tx i)
            | pre, _ => match vc.prefixIri pre with
              | some base => .ok (Value.iri (base ++ n)).canonical
              | none => .error s!"unknown prefix `{pre}` in {t}"
          | [w] => .ok (Value.iri (vc.vocab ++ Path.pctEncode w)).canonical
          | _ => .error s!"bad term {t}"

/-! ## Output -/

def termJson (v : Value) : Json := bundleTermJ (.value v)

def eidText (x : ObjectId) : String := (Value.stmt x.counter.toNat).lexical

def emit (j : Json) : CliM Unit := do IO.println (sortedText j)

def tripleJ (decode : ObjectId → CliM Value) (r : TripleRow) : CliM Json := do
  let base := #[("eid", Json.str (eidText ⟨r.eid⟩)), ("s", termJson (← decode ⟨r.s⟩)), ("p", termJson (← decode ⟨r.p⟩)),
    ("o", termJson (← decode ⟨r.o⟩)), ("tAdd", .int r.tAdd.toInt)]
  let extra := (match r.vFrom with | some f => #[("validFrom", Json.int f.toInt)] | none => #[]) ++
    (match r.vTo with | some t => #[("validTo", Json.int t.toInt)] | none => #[]) ++
    (match r.tRet with | some t => #[("tRet", Json.int t.toInt)] | none => #[])
  return .obj (base ++ extra)

/-! ## Commands -/

def readView (db : Api.Db) (os : List (String × Option String)) : CliM Api.View := do
  let v ← if has os "history" then pure db.history
    else match opt os "as-of" with
      | some t => match t.toNat? with
        | some n => pure (db.asOf (.tx n.toInt64))
        | none => match parseInstant t with
          | some ms => pure (db.asOf (.instant (Int64.ofInt ms)))
          | none => usageErr s!"bad --as-of {t}"
      | none => pure db.now
  match opt os "valid-at" with
  | some t => match parseInstant t with
    | some ms => pure (v.validAt (Int64.ofInt ms))
    | none => usageErr s!"bad --valid-at {t}"
  | none => pure v

def loadVocabOf (v : Api.View) : CliM Path.Vocab := do
  match ← v.read (Path.loadVocab).run with
  | .ok (.ok vc) => pure vc
  | .ok (.error e) => throw (.api (.query e))
  | .error e => throw (.api e)

def termArg (vc : Path.Vocab) (t : String) : CliM Value :=
  match parseTerm vc t with
  | .ok v => pure v
  | .error m => usageErr m

def run (args : List String) : CliM Unit := do
  let (pos, os) := splitArgs ["history", "time-respecting"] args
  match pos with
  | dbPath :: cmd :: rest =>
    let db ← apiOk (← Api.Db.open dbPath)
    try
      let v ← readView db os
      let vc ← loadVocabOf db.now
      let decode (x : ObjectId) : CliM Value := do apiOk (← v.decode x)
      let encode (x : Value) : CliM (Option ObjectId) := do apiOk (← v.encode x)
      match cmd, rest with
      | "info", [] =>
        let rows ← apiOk (← db.history.triples none none none)
        let live := rows.filter (·.tRet.isNone)
        let basis ← apiOk (← db.now.query (ReadProg.query .basis))
        emit (.obj #[("path", .str dbPath), ("format", .int 1), ("lastT", .int basis.toInt),
          ("statements", .int rows.length), ("live", .int live.length)])
      | "assert", [s, p, o] =>
        let (sv, pv, ov) := (← termArg vc s, ← termArg vc p, ← termArg vc o)
        let tv (k : String) : CliM (Option Int64) := match opt os k with
          | some t => match parseInstant t with
            | some ms => pure (some (Int64.ofInt ms))
            | none => usageErr s!"bad --{k} {t}"
          | none => pure none
        let valid : Valid := { vFrom := ← tv "valid-from", vTo := ← tv "valid-to" }
        let (a, rep) ← apiOk (← db.transact (do
          TxProg.verb (.assert (← TxProg.verb (.encode sv)) (← TxProg.verb (.encode pv)) (← TxProg.verb (.encode ov)) { valid })))
        emit (.obj #[("eid", .str (eidText a.eid)), ("new", .bool a.isNew), ("t", .int rep.t.toInt)])
      | "retract", [e] =>
        let some x ← encode (← termArg vc e) | usageErr s!"not a statement {e}"
        let (done, rep) ← apiOk (← db.transact (TxProg.verb (.retract x)))
        emit (.obj #[("retracted", .bool done), ("t", .int rep.t.toInt),
          ("cascade", .arr (rep.retracted.map fun (x, _) => Json.str (eidText x)))])
      | "triples", [] =>
        let pos (k : String) : CliM (Option Value) := match opt os k with
          | some t => do pure (some (← termArg vc t))
          | none => pure none
        let rows ← apiOk (← v.triples (← pos "s") (← pos "p") (← pos "o"))
        for r in rows do emit (← tripleJ decode r)
      | "values", [s, k] =>
        let (some sx, some kx) := (← encode (← termArg vc s), ← encode (← termArg vc k)) | pure ()
        for x in ← apiOk (← v.values sx kx) do emit (termJson (← decode x))
      | "dependents", [e] =>
        let some x ← encode (← termArg vc e) | pure ()
        for d in ← apiOk (← v.dependents x) do emit (.str (eidText d))
      | "path", [start, expr] =>
        let some sx ← encode (← termArg vc start) | pure ()
        let mode ← match opt os "mode" with
          | some m => match PathMode.parse? m with
            | some md => pure md
            | none => throw (.api (.query (.unsupported s!"path mode `{m}`")))
          | none => pure .reach
        let maxHops ← match opt os "max-hops" with
          | some n => match n.toNat? with
            | some k => pure (some k)
            | none => usageErr s!"bad --max-hops {n}"
          | none => pure none
        let graphTexts := os.filterMap fun (k, x) => if k == "graph" then x else none
        let graphs ← if graphTexts.isEmpty then pure none else do
          let ids ← graphTexts.filterMapM fun g => do encode (← termArg vc g)
          pure (some ids)
        let timed ← if has os "time-respecting" then
            match opt os "time-respecting" with
            | some t => match parseInstant t with
              | some ms => pure (some (some (Int64.ofInt ms)))
              | none => usageErr s!"bad --time-respecting {t}"
            | none => pure (some none)
          else pure none
        let rows ← apiOk (← v.pathWith sx expr { mode, maxHops, graphs, timeRespecting := timed })
        for r in rows do
          let base := #[("start", termJson (← decode ⟨r.start⟩)), ("end", termJson (← decode ⟨r.end⟩)), ("hops", Json.int r.hops)]
          let p ← match r.path with
            | some pv => do
              let nodes ← pv.nodes.mapM fun n => do pure (termJson (← decode ⟨n⟩))
              let hops := pv.hops.map fun h => Json.obj #[("eid", .str (eidText ⟨h.eid⟩)),
                ("p", .str ((Path.virtualPredIri? h.pred).getD s!"#{h.pred}")), ("dir", .str (if h.dir == .out then "out" else "in"))]
              let hops ← pv.hops.zip hops |>.mapM fun (h, j) => do
                if (Path.virtualPredIri? h.pred).isSome then pure j
                else pure (Json.obj #[("eid", .str (eidText ⟨h.eid⟩)), ("p", termJson (← decode ⟨h.pred⟩)),
                  ("dir", .str (if h.dir == .out then "out" else "in"))])
              pure #[("path", Json.obj #[("nodes", .arr nodes.toArray), ("hops", .arr hops.toArray)])]
            | none => pure #[]
          let a := match r.arrival with | some t => #[("arrival", Json.int t)] | none => #[]
          emit (.obj (base ++ p ++ a))
      | "bundle", [e] =>
        let some x ← encode (← termArg vc e) | throw (.api (.engine (.notLive ⟨0⟩)))
        let b ← apiOk (← v.bundle x)
        IO.println b.toJson
      | "import-bundle", [file] =>
        let text ← if file == "-" then (do let stdin ← IO.getStdin; stdin.readToEnd) else IO.FS.readFile file
        let b ← match Bundle.Bundle.fromJson text.trimAscii.toString with
          | .ok b => pure b
          | .error e => throw (.api (.engine e))
        let (rep, _) ← apiOk (← db.transact (Tx.importBundle b))
        emit (.obj #[("root", .str (eidText rep.root)),
          ("statements", .arr (rep.statements.map fun s => Json.obj #[("id", .int s.local_), ("eid", .str (eidText s.eid)),
            ("new", .bool s.new)]).toArray)])
      | c, _ => usageErr s!"unknown command or arguments: {c}"
    finally
      db.close
  | _ => usageErr "expected a database path and a command"

/-- The CLI entry point: the exit status. -/
def main (args : List String) : IO UInt32 := do
  match ← (run args).run with
  | .ok () => pure 0
  | .error (.usage msg) =>
    IO.eprintln s!"tiramemsu: {msg}"
    IO.eprintln usage
    pure 2
  | .error (.api e) =>
    IO.eprintln (sortedText (.obj #[("kind", .str e.code), ("message", .str e.message)]))
    pure 1

end Tiramemsu.Cli
