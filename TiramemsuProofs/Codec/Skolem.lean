/-
Proofs of skolem IRIs: parsing the rendering of an origin-0 allocated value with counter
`1 … 2^48 − 1` gives it back, rendering a parsed skolem gives back the IRI, and counters with
a non-zero origin are rejected.
-/
import Tiramemsu.Codec.Skolem
import TiramemsuProofs.Codec.Text

namespace Tiramemsu.Codec

--# @lat: [[codec#Skolem IRIs]]

theorem skolemPrefix_toList (k : AllocTag) : (skolemPrefix k).toList =
    match k with
    | .node => ['u','r','n',':','t','i','r','a','m','e','m','s','u',':','n','o','d','e',':']
    | .bnode => ['u','r','n',':','t','i','r','a','m','e','m','s','u',':','b','n','o','d','e',':']
    | .stmt => ['u','r','n',':','t','i','r','a','m','e','m','s','u',':','s','t','m','t',':']
    | .tx => ['u','r','n',':','t','i','r','a','m','e','m','s','u',':','t','x',':'] := by
  cases k <;> decide

theorem skolemSplit_prefix (k : AllocTag) (r : List Char) :
    skolemSplit (String.ofList ((skolemPrefix k).toList ++ r)) = some (k, r) := by
  unfold skolemSplit skolemTry
  simp only [String.toList_ofList, skolemPrefix_toList]
  cases k <;> simp [List.isPrefixOf]

theorem skolemTry_some {l : List Char} {k k' : AllocTag} {r : List Char}
    (h : skolemTry l k = some (k', r)) : k' = k ∧ l = (skolemPrefix k).toList ++ r := by
  unfold skolemTry at h
  dsimp only at h
  split at h
  · rename_i hp
    cases h
    refine ⟨rfl, ?_⟩
    obtain ⟨t, ht⟩ := List.isPrefixOf_iff_prefix.mp hp
    rw [← ht]; simp
  · cases h

theorem skolemSplit_some {s : String} {k : AllocTag} {r : List Char}
    (h : skolemSplit s = some (k, r)) : s.toList = (skolemPrefix k).toList ++ r := by
  unfold skolemSplit at h
  simp only at h
  rcases h1 : skolemTry s.toList .node with _ | ⟨k1, r1⟩ <;> rw [h1] at h <;> simp only [Option.none_or, Option.some_or] at h
  · rcases h2 : skolemTry s.toList .bnode with _ | ⟨k2, r2⟩ <;> rw [h2] at h <;>
      simp only [Option.none_or, Option.some_or] at h
    · rcases h3 : skolemTry s.toList .stmt with _ | ⟨k3, r3⟩ <;> rw [h3] at h <;>
        simp only [Option.none_or, Option.some_or] at h
      · obtain ⟨rfl, e⟩ := skolemTry_some h; exact e
      · cases h; obtain ⟨rfl, e⟩ := skolemTry_some h3; exact e
    · cases h; obtain ⟨rfl, e⟩ := skolemTry_some h2; exact e
  · cases h; obtain ⟨rfl, e⟩ := skolemTry_some h1; exact e

theorem renderSkolem_toList (k : AllocTag) (n : Nat) :
    (renderSkolem k n).toList = (skolemPrefix k).toList ++ natChars n := by
  simp [renderSkolem, String.toList_append, natText_toList]

theorem parseCanonN_natChars (n : Nat) (h1 : 1 ≤ n) (h2 : n < 2 ^ 60) :
    parseCanonN (natChars n) = some n := by
  obtain ⟨c, rest, hc, hz⟩ := natChars_head_ne_zero n (by omega)
  have hall := natChars_all_digit n
  have hval := natChars_val n
  unfold parseCanonN
  rw [hc]
  split
  · rename_i h; cases h
  · rename_i h; cases h; exact absurd rfl hz
  · rw [← hc, hall, if_pos rfl, hval, if_pos h2]

theorem parseCanonN_some {l : List Char} {n : Nat} (h : parseCanonN l = some n) :
    l = natChars n ∧ 1 ≤ n ∧ n < 2 ^ 60 := by
  unfold parseCanonN at h
  split at h
  · cases h
  · cases h
  · rename_i hnil hz
    split at h
    · rename_i hall
      dsimp only at h
      split at h
      · rename_i hlt
        cases h
        have hne : l ≠ [] := fun e => hnil e
        have hz' : ∀ t, l ≠ '0' :: t := fun t e => hz t e
        refine ⟨(natChars_ofDigitChars l hne hall hz').symm, ?_, hlt⟩
        cases l with
        | nil => exact absurd rfl hne
        | cons c t =>
          have hcd : c.isDigit = true := by simp at hall; exact hall.1
          exact ofDigitChars_pos c t hcd (fun e => hz' t (by rw [e]))
      · cases h
    · cases h

theorem skolemValue_render (k : AllocTag) (n : Nat) (h1 : 1 ≤ n) (h2 : n < 2 ^ 60) :
    skolemValue? (renderSkolem k n) = some (k, n) := by
  unfold skolemValue?
  have : renderSkolem k n = String.ofList ((skolemPrefix k).toList ++ natChars n) := by
    rw [← renderSkolem_toList, String.ofList_toList]
  rw [this, skolemSplit_prefix]
  simp [parseCanonN_natChars n h1 h2]

/-- Parsing the skolem IRI of an origin-0 allocated value with counter `1 … 2^48 − 1` gives it
back. -/
theorem parseSkolem_renderSkolem (k : AllocTag) (n : Nat) (h1 : 1 ≤ n) (h2 : n < 2 ^ 48) :
    parseSkolem (renderSkolem k n) = .ok (some (k, n)) := by
  unfold parseSkolem
  rw [skolemValue_render k n h1 (by omega)]
  simp <;> omega

/-- A counter with a non-zero origin is rejected with `Unsupported "origin <o>"`. -/
theorem parseSkolem_origin (k : AllocTag) (n : Nat) (h1 : 2 ^ 48 ≤ n) (h2 : n < 2 ^ 60) :
    parseSkolem (renderSkolem k n) = .error (.unsupported (originFeature (n / 2 ^ 48))) := by
  unfold parseSkolem
  rw [skolemValue_render k n (by omega) h2]
  simp <;> omega

/-- Rendering a parsed skolem gives back the IRI. -/
theorem renderSkolem_parseSkolem (s : String) (k : AllocTag) (n : Nat)
    (h : parseSkolem s = .ok (some (k, n))) : renderSkolem k n = s ∧ 1 ≤ n ∧ n < 2 ^ 48 := by
  unfold parseSkolem at h
  split at h
  · cases h
  · rename_i k' n' hv
    split at h
    · rename_i hlt
      cases h
      unfold skolemValue? at hv
      rcases hs : skolemSplit s with _ | ⟨k1, r⟩
      · simp [hs] at hv
      · rcases hc : parseCanonN r with _ | m
        · simp [hs, hc] at hv
        · simp [hs, hc] at hv
          obtain ⟨rfl, rfl⟩ := hv
          obtain ⟨hr, hm1, _⟩ := parseCanonN_some hc
          refine ⟨?_, hm1, hlt⟩
          have e := skolemSplit_some hs
          rw [← String.ofList_toList (s := s), e, hr, ← renderSkolem_toList, String.ofList_toList]
    · cases h

end Tiramemsu.Codec
