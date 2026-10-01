/-
Skolem IRIs of allocated ids: `urn:tiramemsu:node:<n>`, `bnode:`, `stmt:`, `tx:`. A canonical
decimal `1 ≤ n < 2^48` is the origin-0 id of counter `n`; `2^48 ≤ n < 2^60` names a foreign
origin and is rejected; anything else stays an ordinary IRI.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.Origin
import Tiramemsu.Codec.Text

namespace Tiramemsu.Codec

--# @lat: [[codec#Skolem IRIs]]

/-- The skolem IRI prefix of an allocated tag. -/
def skolemPrefix : AllocTag → String
  | .node => "urn:tiramemsu:node:"
  | .bnode => "urn:tiramemsu:bnode:"
  | .stmt => "urn:tiramemsu:stmt:"
  | .tx => "urn:tiramemsu:tx:"

/-- A canonical decimal `n` with `1 ≤ n < 2^60` (no sign, no leading zero). -/
def parseCanonN (l : List Char) : Option Nat :=
  match l with
  | [] => none
  | '0' :: _ => none
  | _ =>
    if l.all isDigitChar then
      let n := Nat.ofDigitChars 10 l 0
      if n < 2 ^ 60 then some n else none
    else none

/-- The text after the skolem prefix of `k`, if `l` starts with it. -/
def skolemTry (l : List Char) (k : AllocTag) : Option (AllocTag × List Char) :=
  let p := (skolemPrefix k).toList
  if p.isPrefixOf l then some (k, l.drop p.length) else none

/-- The text after a skolem prefix, with the prefix's tag. -/
def skolemSplit (s : String) : Option (AllocTag × List Char) :=
  let l := s.toList
  (skolemTry l .node).or ((skolemTry l .bnode).or ((skolemTry l .stmt).or (skolemTry l .tx)))

/-- The allocated tag and counter (`1 ≤ n < 2^60`) of a skolem IRI, if it is one. -/
def skolemValue? (s : String) : Option (AllocTag × Nat) := do
  let (k, rest) ← skolemSplit s
  let n ← parseCanonN rest
  pure (k, n)

/-- The skolem IRI of an allocated tag and counter. -/
def renderSkolem (k : AllocTag) (n : Nat) : String := skolemPrefix k ++ natText n

/-- Parses a skolem IRI: the tag and counter for `1 ≤ n < 2^48`, `Unsupported "origin <o>"`
for `2^48 ≤ n < 2^60`, and `none` (an ordinary IRI) for anything else. -/
def parseSkolem (s : String) : Except CodecError (Option (AllocTag × Nat)) :=
  match skolemValue? s with
  | none => .ok none
  | some (k, n) => if n < 2 ^ 48 then .ok (some (k, n)) else .error (.unsupported (originFeature (n / 2 ^ 48)))

end Tiramemsu.Codec
