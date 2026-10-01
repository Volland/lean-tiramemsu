/-
The printed form parses back: `parseDouble (printDouble x) = some x.canon` for every bit
pattern (finite values give back their bits, NaNs the canonical NaN), and the printed
significant digits are the fewest of any decimal that rounds to `x`.
-/
import TiramemsuProofs.Codec.Double.Print

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Doubles]]

theorem takeWhile_append_stop {p : Char → Bool} (l r : List Char) (c : Char)
    (hl : l.all p = true) (hc : p c = false) : (l ++ c :: r).takeWhile p = l := by
  induction l with
  | nil => simp [List.takeWhile_cons, hc]
  | cons a l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hl
    simp [List.takeWhile_cons, hl.1, ih hl.2]

theorem digit_not_e (c : Char) (h : c.isDigit = true) : (c != 'e' && c != 'E') = true := by
  have h1 : c ≠ 'e' := by rintro rfl; exact absurd h (by decide)
  have h2 : c ≠ 'E' := by rintro rfl; exact absurd h (by decide)
  simp [h1, h2]

theorem digit_not_dot (c : Char) (h : c.isDigit = true) : (c != '.') = true := by
  have h1 : c ≠ '.' := by rintro rfl; exact absurd h (by decide)
  simp [h1]

theorem splitSign_intText (X : Int) :
    splitSign (intText X).toList = (decide (X < 0), natChars (if X < 0 then X.natAbs else X.toNat)) := by
  rw [intText_toList]
  by_cases h : X < 0
  · simp [h, splitSign]
  · simp [h, splitSign_natChars]

/-- The syntax of a printed finite nonzero value. -/
theorem scan_sciChars (neg : Bool) (c : ℕ) (P : Int) (hc : 0 < c) :
    ∃ i f en ed, scanDouble (String.ofList (sciChars neg c P)) = some (.numeric neg i f en ed) ∧
      DoubleSyntax.decValue i f en ed = (c : ℚ) * (10 : ℚ) ^ P := by
  have hall := natChars_all_digit c
  have hval := natChars_val c
  obtain ⟨d0, rest, hds⟩ : ∃ d0 rest, natChars c = d0 :: rest := by
    cases h : natChars c with
    | nil => exact absurd h (natChars_ne_nil c)
    | cons d r => exact ⟨d, r, rfl⟩
  rw [hds] at hall hval
  simp only [List.all_cons, Bool.and_eq_true] at hall
  obtain ⟨hd0, hrest⟩ := hall
  generalize hX : P + ((d0 :: rest).length : Int) - 1 = X
  generalize hF : (if rest.isEmpty then ['0'] else rest) = F
  have hFall : F.all isDigitChar = true := by
    rw [← hF]; split
    · decide
    · exact hrest
  have hchars : sciChars neg c P = (if neg then ['-'] else []) ++ d0 :: '.' :: F ++ 'E' :: (intText X).toList := by
    unfold sciChars
    simp only [hds]
    rw [← hX, ← hF]
  refine ⟨[d0], F, decide (X < 0), natChars (if X < 0 then X.natAbs else X.toNat), ?_, ?_⟩
  · rw [hchars]
    unfold scanDouble
    -- not a special form
    have hne : ∀ t : String, t.toList ≠ ((if neg then ['-'] else []) ++ d0 :: '.' :: F ++ 'E' :: (intText X).toList) →
        (String.ofList ((if neg then ['-'] else []) ++ d0 :: '.' :: F ++ 'E' :: (intText X).toList) == t) = false := by
      intro t ht
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; apply ht; rw [← e, String.toList_ofList]
    have hdI : d0 ≠ 'I' := by rintro rfl; exact absurd hd0 (by decide)
    have hdN : d0 ≠ 'N' := by rintro rfl; exact absurd hd0 (by decide)
    have hdP : d0 ≠ '+' := by rintro rfl; exact absurd hd0 (by decide)
    have hdM : d0 ≠ '-' := by rintro rfl; exact absurd hd0 (by decide)
    rw [hne "INF" (by cases neg <;> simp [hdI]), hne "+INF" (by cases neg <;> simp [hdP]),
      hne "-INF" (by cases neg <;> simp [hdM, hdI]), hne "NaN" (by cases neg <;> simp [hdN])]
    simp only [Bool.or_false, Bool.false_eq_true, ite_false, String.toList_ofList]
    unfold scanNumeric
    have hsplit : splitSign ((if neg then ['-'] else []) ++ d0 :: '.' :: F ++ 'E' :: (intText X).toList) =
        (neg, d0 :: '.' :: F ++ 'E' :: (intText X).toList) := by
      cases neg
      · simp only [Bool.false_eq_true, ite_false, List.nil_append, List.cons_append]
        exact splitSign_digit_head _ _ hd0
      · simp [splitSign]
    rw [hsplit]
    simp only
    have hmant : (d0 :: '.' :: F ++ 'E' :: (intText X).toList).takeWhile (fun c => c != 'e' && c != 'E') =
        d0 :: '.' :: F := by
      rw [show d0 :: '.' :: F ++ 'E' :: (intText X).toList = (d0 :: '.' :: F) ++ 'E' :: (intText X).toList by simp]
      apply takeWhile_append_stop
      · simp only [List.all_cons, Bool.and_eq_true]
        refine ⟨by simpa using digit_not_e d0 hd0, by decide, ?_⟩
        rw [List.all_eq_true]
        intro y hy
        exact digit_not_e y (by have := List.all_eq_true.mp hFall y hy; simpa using this)
      · decide
    rw [hmant]
    have hdrop : (d0 :: '.' :: F ++ 'E' :: (intText X).toList).drop (d0 :: '.' :: F).length =
        'E' :: (intText X).toList := by
      rw [show d0 :: '.' :: F ++ 'E' :: (intText X).toList = (d0 :: '.' :: F) ++ 'E' :: (intText X).toList by simp]
      exact List.drop_left
    rw [hdrop]
    have hint : (d0 :: '.' :: F).takeWhile (· != '.') = [d0] := by
      simp [List.takeWhile_cons, digit_not_dot d0 hd0]
    rw [hint]
    simp only [List.length_singleton, List.drop_succ_cons, List.drop_zero, List.isEmpty_cons,
      Bool.false_and, Bool.false_eq_true, ite_false, List.all_cons, List.all_nil, Bool.and_true]
    simp only [hd0, hFall, Bool.true_and, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [splitSign_intText]
    simp only [natChars_all_digit, Bool.not_true, Bool.or_false]
    have hne' : (natChars (if X < 0 then X.natAbs else X.toNat)).isEmpty = false := by
      cases h : natChars (if X < 0 then X.natAbs else X.toNat) with
      | nil => exact absurd h (natChars_ne_nil _)
      | cons _ _ => rfl
    simp [hne']
  · unfold DoubleSyntax.decValue DoubleSyntax.decExp
    rw [natChars_val]
    have hXe : (if decide (X < 0) = true then -(((if X < 0 then X.natAbs else X.toNat) : ℕ) : Int)
        else (((if X < 0 then X.natAbs else X.toNat) : ℕ) : Int)) = X := by
      by_cases h : X < 0
      · simp only [h, decide_true, ite_true]; omega
      · simp only [h, decide_false, ite_false, Bool.false_eq_true]; omega
    dsimp only
    rw [hXe]
    by_cases hr : rest = []
    · subst hr
      simp only [List.isEmpty_nil, ite_true] at hF
      subst hF
      simp only [List.length_singleton, Nat.cast_one] at hX
      have hc' : c = d0.toNat - 48 := by
        rw [← hval]; simp [Nat.ofDigitChars_cons]
      rw [show [d0] ++ ['0'] = [d0, '0'] by rfl]
      simp only [Nat.ofDigitChars_cons, Nat.ofDigitChars_nil, List.length_singleton, Nat.cast_one]
      rw [← hX]
      have : ('0'.toNat - '0'.toNat) = 0 := by decide
      simp only [Nat.mul_zero, Nat.zero_add, this, Nat.add_zero]
      rw [hc']
      push_cast
      rw [show P + 1 - 1 - 1 = P - 1 by ring, zpow_sub₀ (by norm_num)]
      have h0 : (48 : ℕ) = '0'.toNat := rfl
      rw [h0]
      field_simp
    · have hFr : F = rest := by
        rw [← hF]; simp [hr]
      subst hFr
      rw [show [d0] ++ F = d0 :: F by rfl, hval]
      rw [← hX]
      congr 1
      simp only [List.length_cons]
      push_cast
      ring

theorem Double64.isZero_eq (x : Double64) (h : x.isZero = true) : x = Double64.zero x.neg := by
  simp only [Double64.isZero, Bool.and_eq_true, beq_iff_eq] at h
  rw [Double64.zero_eq_ofFields]
  conv => lhs; rw [Double64.eq_ofFields x]
  rw [h.1, h.2]

theorem Double64.isInf_eq (x : Double64) (h : x.isInf = true) : x = Double64.inf x.neg := by
  simp only [Double64.isInf, Bool.and_eq_true, beq_iff_eq] at h
  have e : Double64.inf x.neg = Double64.ofFields x.neg 2047 0 := by cases x.neg <;> decide
  rw [e]
  conv => lhs; rw [Double64.eq_ofFields x]
  rw [h.1, h.2]

theorem parse_zero_text : parseDouble "0.0E0" = some (Double64.zero false) := by decide
theorem parse_negzero_text : parseDouble "-0.0E0" = some (Double64.zero true) := by decide
theorem parse_inf_text : parseDouble "INF" = some (Double64.inf false) := by decide
theorem parse_neginf_text : parseDouble "-INF" = some (Double64.inf true) := by decide
theorem parse_nan_text : parseDouble "NaN" = some Double64.canonNaN := by decide

/-- Round trip: parsing the printed form gives back the value (every NaN gives the canonical
NaN). -/
theorem parseDouble_printDouble (x : Double64) : parseDouble (printDouble x) = some x.canon := by
  unfold printDouble
  by_cases hn : x.isNaN = true
  · rw [if_pos hn, parse_nan_text]; simp [Double64.canon, hn]
  rw [if_neg hn]
  have hc : x.canon = x := by simp [Double64.canon, hn]
  rw [hc]
  by_cases hi : x.isInf = true
  · rw [if_pos hi]
    conv => rhs; rw [Double64.isInf_eq x hi]
    cases x.neg <;> simp [parse_inf_text, parse_neginf_text]
  rw [if_neg hi]
  have hf : x.isFinite = true := by
    simp only [Double64.isNaN, Double64.isInf, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      not_and, not_not] at hn hi
    simp only [Double64.isFinite, bne_iff_ne, ne_eq]
    intro h; exact hi h (hn h)
  by_cases hz : x.isZero = true
  · rw [if_pos hz]
    conv => rhs; rw [Double64.isZero_eq x hz]
    cases x.neg <;> simp [parse_zero_text, parse_negzero_text]
  rw [if_neg hz]
  have hz' : x.isZero = false := by simpa using hz
  obtain ⟨hpos, hin⟩ := shortestDec_spec x hf hz'
  generalize shortestDec x = cp at hpos hin
  obtain ⟨c, P⟩ := cp
  simp only at hpos hin ⊢
  obtain ⟨i, f, en, ed, hs, hv⟩ := scan_sciChars x.neg c P hpos
  rw [parseDouble_correct _ _ _ _ _ _ hs, hv]
  congr 1
  exact (round_eq_iff x hf hz' _ (by positivity)).mpr hin

/-- Shortness in terms of the printer: no decimal `m · 10^e` with fewer significant digits than
the printed form rounds to a finite nonzero `x`. -/
theorem printDouble_shortest (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false)
    (m : ℕ) (e : Int) (s : ℕ) (hm : 0 < m) (hs : IsSig m s)
    (h : roundBinary64 x.neg ((m : ℚ) * (10 : ℚ) ^ e) = x) : IsSig (shortestDec x).1 s :=
  shortestDec_shortest x hf hz m e s hm hs h

/-- The printed text of a finite nonzero value is `sciChars` of the shortest decimal. -/
theorem printDouble_finite (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false) :
    printDouble x = String.ofList (sciChars x.neg (shortestDec x).1 (shortestDec x).2) := by
  have hn : x.isNaN = false := by
    simp only [Double64.isFinite, bne_iff_ne, ne_eq] at hf
    simp [Double64.isNaN, hf]
  have hi : x.isInf = false := by
    simp only [Double64.isFinite, bne_iff_ne, ne_eq] at hf
    simp [Double64.isInf, hf]
  unfold printDouble
  simp [hn, hi, hz]

end Tiramemsu.Codec
