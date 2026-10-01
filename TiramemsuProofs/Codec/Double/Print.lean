/-
The shortest printer: the printed decimal lies in the value's rounding interval (so it parses
back to the same bits), seventeen digits always suffice, and no decimal with fewer significant
digits rounds to the value.
-/
import TiramemsuProofs.Codec.Double.Interval
import TiramemsuProofs.Codec.Text

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Doubles]]

/-! ## Exact comparisons -/

theorem max_pos_neg (p : Int) : p + max (-p) 0 = max p 0 := by omega

theorem cmpDecBin_key (a : ℕ) (pa : Int) (b : ℕ) (eb : Int) :
    let D : ℚ := (10 : ℚ) ^ (max (-pa) 0).toNat * (2 : ℚ) ^ (max (-eb) 0).toNat
    ((a : ℚ) * (10 : ℚ) ^ pa) * D = ((a * 10 ^ (max pa 0).toNat * 2 ^ (max (-eb) 0).toNat : ℕ) : ℚ) ∧
      ((b : ℚ) * (2 : ℚ) ^ eb) * D = ((b * 2 ^ (max eb 0).toNat * 10 ^ (max (-pa) 0).toNat : ℕ) : ℚ) := by
  intro D
  have h10 : (10 : ℚ) ^ pa * (10 : ℚ) ^ (max (-pa) 0).toNat = (10 : ℚ) ^ (max pa 0).toNat := by
    rw [← zpow_natCast, ← zpow_natCast (n := (max pa 0).toNat), ← zpow_add₀ (by norm_num)]
    congr 1; omega
  have h2 : (2 : ℚ) ^ eb * (2 : ℚ) ^ (max (-eb) 0).toNat = (2 : ℚ) ^ (max eb 0).toNat := by
    rw [← zpow_natCast, ← zpow_natCast (n := (max eb 0).toNat), ← zpow_add₀ (by norm_num)]
    congr 1; omega
  constructor
  · push_cast
    calc (a : ℚ) * (10 : ℚ) ^ pa * ((10 : ℚ) ^ (max (-pa) 0).toNat * (2 : ℚ) ^ (max (-eb) 0).toNat)
        = a * ((10 : ℚ) ^ pa * (10 : ℚ) ^ (max (-pa) 0).toNat) * (2 : ℚ) ^ (max (-eb) 0).toNat := by ring
      _ = _ := by rw [h10]
  · push_cast
    calc (b : ℚ) * (2 : ℚ) ^ eb * ((10 : ℚ) ^ (max (-pa) 0).toNat * (2 : ℚ) ^ (max (-eb) 0).toNat)
        = b * ((2 : ℚ) ^ eb * (2 : ℚ) ^ (max (-eb) 0).toNat) * (10 : ℚ) ^ (max (-pa) 0).toNat := by ring
      _ = _ := by rw [h2]

/-- `cmpDecBin` compares `a · 10^pa` with `b · 2^eb` exactly. -/
theorem cmpDecBin_spec (a : ℕ) (pa : Int) (b : ℕ) (eb : Int) :
    (cmpDecBin a pa b eb = .lt ↔ (a : ℚ) * (10 : ℚ) ^ pa < (b : ℚ) * (2 : ℚ) ^ eb) ∧
      (cmpDecBin a pa b eb = .eq ↔ (a : ℚ) * (10 : ℚ) ^ pa = (b : ℚ) * (2 : ℚ) ^ eb) ∧
      (cmpDecBin a pa b eb = .gt ↔ (b : ℚ) * (2 : ℚ) ^ eb < (a : ℚ) * (10 : ℚ) ^ pa) := by
  obtain ⟨k1, k2⟩ := cmpDecBin_key a pa b eb
  have hD : (0 : ℚ) < (10 : ℚ) ^ (max (-pa) 0).toNat * (2 : ℚ) ^ (max (-eb) 0).toNat := by positivity
  unfold cmpDecBin
  generalize a * 10 ^ (max pa 0).toNat * 2 ^ (max (-eb) 0).toNat = A at k1
  generalize b * 2 ^ (max eb 0).toNat * 10 ^ (max (-pa) 0).toNat = B at k2
  generalize (a : ℚ) * (10 : ℚ) ^ pa = q1 at k1
  generalize (b : ℚ) * (2 : ℚ) ^ eb = q2 at k2
  have lt : q1 < q2 ↔ A < B := by
    rw [← mul_lt_mul_iff_of_pos_right hD, k1, k2]; exact_mod_cast Iff.rfl
  have eq : q1 = q2 ↔ A = B := by
    rw [← mul_left_inj' (ne_of_gt hD), k1, k2]; exact_mod_cast Iff.rfl
  have gt : q2 < q1 ↔ B < A := by
    rw [← mul_lt_mul_iff_of_pos_right hD, k1, k2]; exact_mod_cast Iff.rfl
  rw [lt, eq, gt]
  refine ⟨Nat.compare_eq_lt, Nat.compare_eq_eq, Nat.compare_eq_gt⟩

/-! ## The interval check -/

theorem inInterval_spec (x : Double64) (c : ℕ) (P : Int) :
    inInterval x c P = true ↔ InInterval x ((c : ℚ) * (10 : ℚ) ^ P) := by
  unfold inInterval InInterval
  simp only
  generalize (roundingInterval x).1 = lo
  generalize (roundingInterval x).2.1 = hi
  generalize (roundingInterval x).2.2 = incl
  obtain ⟨l1, l2, l3⟩ := cmpDecBin_spec c P lo (x.mantExp.2 - 2)
  obtain ⟨u1, u2, u3⟩ := cmpDecBin_spec c P hi (x.mantExp.2 - 2)
  generalize hcl : cmpDecBin c P lo (x.mantExp.2 - 2) = ol at l1 l2 l3
  generalize hch : cmpDecBin c P hi (x.mantExp.2 - 2) = oh at u1 u2 u3
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨hl, hh⟩
    constructor
    · cases ol
      · simp at hl
      · simp at hl; exact Or.inr ⟨hl, (l2.mp rfl).symm⟩
      · exact Or.inl (l3.mp rfl)
    · cases oh
      · exact Or.inl (u1.mp rfl)
      · simp at hh; exact Or.inr ⟨hh, u2.mp rfl⟩
      · simp at hh
  · rintro ⟨hl, hh⟩
    constructor
    · cases ol
      · exfalso
        have := l1.mp rfl
        rcases hl with h | h <;> [linarith; linarith [h.2]]
      · simp; rcases hl with h | h
        · exact absurd (l2.mp rfl) (ne_of_gt h)
        · exact h.1
      · rfl
    · cases oh
      · rfl
      · simp; rcases hh with h | h
        · exact absurd (u2.mp rfl) (ne_of_lt h)
        · exact h.1
      · exfalso
        have := u3.mp rfl
        rcases hh with h | h <;> [linarith; linarith [h.2]]

/-- The interval is convex. -/
theorem InInterval.convex {x : Double64} {a b c : ℚ} (ha : InInterval x a) (hb : InInterval x b)
    (h1 : a ≤ c) (h2 : c ≤ b) : InInterval x c := by
  unfold InInterval at *
  simp only at *
  obtain ⟨ha1, -⟩ := ha
  obtain ⟨-, hb2⟩ := hb
  constructor
  · rcases ha1 with h | h
    · exact Or.inl (lt_of_lt_of_le h h1)
    · rcases eq_or_lt_of_le h1 with e | e
      · exact Or.inr ⟨h.1, h.2.trans e⟩
      · exact Or.inl (h.2 ▸ e)
  · rcases hb2 with h | h
    · exact Or.inl (lt_of_le_of_lt h2 h)
    · rcases eq_or_lt_of_le h2 with e | e
      · exact Or.inr ⟨h.1, e.trans h.2⟩
      · exact Or.inl (h.2 ▸ e)

/-- A finite nonzero value lies in its own interval. -/
theorem mag_inInterval (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false) :
    InInterval x x.mag := by
  have hx := normal_of_finite x hf hz
  rw [inInterval_iff x _ _ hx]
  unfold Double64.mag
  have hp := two_zpow_pos x.mantExp.2
  rw [mul_div_assoc, div_self (ne_of_gt hp), mul_one]
  constructor
  · left; split_ifs <;> linarith
  · left; linarith

theorem mag_pos (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false) : 0 < x.mag := by
  have hx := normal_of_finite x hf hz
  unfold Double64.mag
  have : (1 : ℚ) ≤ x.mantExp.1 := by exact_mod_cast hx.bounds.1
  have := two_zpow_pos x.mantExp.2
  positivity

/-! ## Candidates -/

theorem binRatio_spec (M : ℕ) (E : Int) (hM : 0 < M) :
    0 < (binRatio M E).1 ∧ 0 < (binRatio M E).2 ∧
      ((binRatio M E).1 : ℚ) / (binRatio M E).2 = (M : ℚ) * (2 : ℚ) ^ E := by
  unfold binRatio
  split
  · rename_i hE
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hE
    refine ⟨by positivity, by norm_num, ?_⟩
    push_cast; simp
  · rename_i hE
    obtain ⟨n, hn⟩ : ∃ n : Nat, E = -(n : Int) := ⟨(-E).toNat, by omega⟩
    subst hn
    refine ⟨hM, by positivity, ?_⟩
    simp [zpow_neg, div_eq_mul_inv]

theorem decLog_eq (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false) :
    decLog x = Int.log 10 x.mag := by
  have hx := normal_of_finite x hf hz
  unfold decLog Double64.mag
  generalize x.mantExp = p at hx ⊢
  obtain ⟨M, E⟩ := p
  simp only at hx ⊢
  obtain ⟨a0, b0, e⟩ := binRatio_spec M E (by have := hx.bounds.1; omega)
  generalize binRatio M E = br at a0 b0 e
  obtain ⟨a, b⟩ := br
  simp only at a0 b0 e ⊢
  rw [floorLog10Ratio_eq _ _ a0 b0, e]

theorem candidates_eq (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false) (L : Int) (k : Nat) :
    candidates x L k = (⌊x.mag / (10 : ℚ) ^ (L - k + 1)⌋₊, L - k + 1) := by
  have hx := normal_of_finite x hf hz
  unfold candidates Double64.mag
  generalize x.mantExp = p at hx ⊢
  obtain ⟨M, E⟩ := p
  simp only at hx ⊢
  obtain ⟨a0, b0, e⟩ := binRatio_spec M E (by have := hx.bounds.1; omega)
  generalize binRatio M E = br at a0 b0 e
  obtain ⟨a, b⟩ := br
  simp only at a0 b0 e ⊢
  simp only [Prod.mk.injEq, and_true]
  generalize L - k + 1 = P
  rw [← Nat.floor_div_eq_div (K := ℚ)]
  congr 1
  rw [← e]
  push_cast
  by_cases hP : 0 ≤ P
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hP
    simp only [show max (-(n : Int)) 0 = 0 by omega, show max (n : Int) 0 = n by omega,
      Int.toNat_zero, Int.toNat_natCast, pow_zero, mul_one, zpow_natCast]
    rw [div_div]
  · obtain ⟨n, hn⟩ : ∃ n : Nat, P = -(n : Int) := ⟨(-P).toNat, by omega⟩
    subst hn
    simp only [show max (-(-(n : Int))) 0 = n by omega, show max (-(n : Int)) 0 = 0 by omega,
      Int.toNat_zero, Int.toNat_natCast, pow_zero, mul_one, zpow_neg, zpow_natCast]
    rw [div_inv_eq_mul, mul_div_right_comm]

theorem pickK_spec (x : Double64) (L : Int) (k : Nat) (c : ℕ) (P : Int) (h : pickK x L k = some (c, P)) :
    P = (candidates x L k).2 ∧ (c = (candidates x L k).1 ∨ c = (candidates x L k).1 + 1) ∧
      inInterval x c P = true := by
  unfold pickK at h
  simp only at h
  generalize candidates x L k = cand at h ⊢
  obtain ⟨f, P'⟩ := cand
  simp only at h ⊢
  split_ifs at h with h1 hn h2 h3 <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h
  · exact ⟨rfl, Or.inl rfl, ((Bool.and_eq_true _ _).mp h1).1⟩
  · exact ⟨rfl, Or.inr rfl, ((Bool.and_eq_true _ _).mp h1).2⟩
  · exact ⟨rfl, Or.inl rfl, h2⟩
  · exact ⟨rfl, Or.inr rfl, h3⟩

theorem pickK_some_of_in (x : Double64) (L : Int) (k : Nat) (hf : x.isFinite = true) (hz : x.isZero = false)
    (j : ℕ) (hj : InInterval x ((j : ℚ) * (10 : ℚ) ^ (L - k + 1))) : (pickK x L k).isSome := by
  have hv := mag_inInterval x hf hz
  have hvpos := mag_pos x hf hz
  have hc := candidates_eq x hf hz L k
  unfold pickK
  simp only
  rw [hc]
  simp only
  generalize hP : L - k + 1 = P at hj
  have hS : (0 : ℚ) < (10 : ℚ) ^ P := zpow_pos (by norm_num) P
  generalize hf' : ⌊x.mag / (10 : ℚ) ^ P⌋₊ = f
  have f1 : (f : ℚ) ≤ x.mag / (10 : ℚ) ^ P := by rw [← hf']; exact Nat.floor_le (le_of_lt (div_pos hvpos hS))
  have f2 : x.mag / (10 : ℚ) ^ P < f + 1 := by rw [← hf']; exact Nat.lt_floor_add_one _
  have f1' : (f : ℚ) * (10 : ℚ) ^ P ≤ x.mag := by rwa [le_div_iff₀ hS] at f1
  have f2' : x.mag < ((f + 1 : ℕ) : ℚ) * (10 : ℚ) ^ P := by push_cast; rwa [div_lt_iff₀ hS] at f2
  by_cases hle : (j : ℚ) * (10 : ℚ) ^ P ≤ x.mag
  · have hjf : j ≤ f := by
      rw [← hf']; apply Nat.le_floor; rw [le_div_iff₀ hS]; exact hle
    have hjf' : (j : ℚ) * (10 : ℚ) ^ P ≤ (f : ℚ) * (10 : ℚ) ^ P := by gcongr
    have hin : InInterval x ((f : ℚ) * (10 : ℚ) ^ P) := hj.convex hv hjf' f1'
    rw [← inInterval_spec] at hin
    cases hG : inInterval x (f + 1) P <;> simp_all
  · push_neg at hle
    have hfj : f + 1 ≤ j := by
      have : x.mag / (10 : ℚ) ^ P < j := by rw [div_lt_iff₀ hS]; exact hle
      have : f < j := by rw [← hf']; exact (Nat.floor_lt (le_of_lt (div_pos hvpos hS))).mpr this
      omega
    have hfj' : ((f + 1 : ℕ) : ℚ) * (10 : ℚ) ^ P ≤ (j : ℚ) * (10 : ℚ) ^ P := by gcongr
    have hin : InInterval x (((f + 1 : ℕ) : ℚ) * (10 : ℚ) ^ P) := hv.convex hj (le_of_lt f2') hfj'
    rw [← inInterval_spec] at hin
    cases hF : inInterval x f P <;> simp_all

/-! ## Seventeen digits suffice -/

theorem mag_bounds_log (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false) :
    (10 : ℚ) ^ (Int.log 10 x.mag) ≤ x.mag ∧ x.mag < (10 : ℚ) ^ (Int.log 10 x.mag + 1) := by
  have hv := mag_pos x hf hz
  have l1 := Int.zpow_log_le_self (b := 10) (by decide) hv
  have l2 := Int.lt_zpow_succ_log_self (b := 10) (by decide) x.mag
  push_cast at l1 l2
  exact ⟨l1, l2⟩

/-- The interval is wider than `10^(⌊log₁₀ x⌋ − 16)`, so it contains a 17-digit decimal. -/
theorem seventeen_digits (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false) :
    ∃ j : ℕ, InInterval x ((j : ℚ) * (10 : ℚ) ^ (Int.log 10 x.mag - 17 + 1)) := by
  have hx := normal_of_finite x hf hz
  generalize hME : x.mantExp = p at hx
  obtain ⟨M, E⟩ := p
  simp only at hx
  obtain ⟨hL1, -⟩ := mag_bounds_log x hf hz
  have hM1 := hx.bounds.1
  have hM2 := hx.bounds.2
  have hmag : x.mag = (M : ℚ) * (2 : ℚ) ^ E := by unfold Double64.mag; rw [hME]
  generalize hS : (10 : ℚ) ^ (Int.log 10 x.mag - 17 + 1) = S
  have hSpos : 0 < S := by rw [← hS]; exact zpow_pos (by norm_num) _
  have hp := two_zpow_pos E
  -- the spacing is at most x / 10^16
  have hSle : S * 10 ^ 16 ≤ (M : ℚ) * (2 : ℚ) ^ E := by
    rw [← hS, ← hmag]
    calc (10 : ℚ) ^ (Int.log 10 x.mag - 17 + 1) * 10 ^ 16
        = (10 : ℚ) ^ (Int.log 10 x.mag) := by
          rw [show Int.log 10 x.mag - 17 + 1 = Int.log 10 x.mag - 16 by ring, zpow_sub₀ (by norm_num)]
          field_simp
      _ ≤ x.mag := hL1
  -- the interval bounds in units of 2^E
  have key : ∀ y : ℚ, ((if x.frac = 0 ∧ x.biasedExp > 1 then (M : ℚ) - 1 / 4 else (M : ℚ) - 1 / 2) < y / (2 : ℚ) ^ E ∧
      y / (2 : ℚ) ^ E < (M : ℚ) + 1 / 2) → InInterval x y := by
    intro y ⟨h1, h2⟩
    have hx' : Normal x M E := hx
    rw [inInterval_iff x M E hx']
    exact ⟨Or.inl h1, Or.inl h2⟩
  -- the width exceeds the spacing
  have hwide : S < ((M : ℚ) + 1 / 2) * (2 : ℚ) ^ E -
      (if x.frac = 0 ∧ x.biasedExp > 1 then (M : ℚ) - 1 / 4 else (M : ℚ) - 1 / 2) * (2 : ℚ) ^ E := by
    split_ifs with hpow
    · -- a power of two: M = 2^52
      have hM52 : M = 2 ^ 52 := hx.pow_two hpow.1 (by omega)
      subst hM52
      push_cast at hSle
      nlinarith
    · have : (M : ℚ) + 1 ≤ 2 ^ 53 := by exact_mod_cast hM2
      nlinarith
  generalize (if x.frac = 0 ∧ x.biasedExp > 1 then (M : ℚ) - 1 / 4 else (M : ℚ) - 1 / 2) = lo' at key hwide
  -- the multiple just below the upper end
  generalize hHi : ((M : ℚ) + 1 / 2) * (2 : ℚ) ^ E = Hi at hwide
  have hHipos : 0 < Hi := by rw [← hHi]; positivity
  have hc1 : 1 ≤ ⌈Hi / S⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [ne_eq, Nat.ceil_eq_zero, not_le]; exact div_pos hHipos hSpos)
  generalize hC : ⌈Hi / S⌉₊ = C at hc1
  have hCle : Hi ≤ (C : ℚ) * S := by
    rw [← hC]; exact (div_le_iff₀ hSpos).mp (Nat.le_ceil _)
  have hClt : ((C : ℚ) - 1) * S < Hi := by
    have : (C : ℚ) < Hi / S + 1 := by rw [← hC]; exact Nat.ceil_lt_add_one (le_of_lt (div_pos hHipos hSpos))
    have : (C : ℚ) - 1 < Hi / S := by linarith
    have := (lt_div_iff₀ hSpos).mp this
    linarith
  refine ⟨C - 1, key _ ⟨?_, ?_⟩⟩
  · rw [Nat.cast_sub hc1, Nat.cast_one, lt_div_iff₀ hp]
    have e : ((C : ℚ) - 1) * S = C * S - S := by ring
    linarith
  · rw [Nat.cast_sub hc1, Nat.cast_one, div_lt_iff₀ hp, hHi]
    exact hClt

/-! ## The search -/

theorem search_some (x : Double64) (L : Int) (fuel k : Nat) (r : ℕ × Int)
    (h : searchShortest x L fuel k = some r) :
    ∃ k', k ≤ k' ∧ k' < k + fuel ∧ pickK x L k' = some r ∧ ∀ j, k ≤ j → j < k' → pickK x L j = none := by
  induction fuel generalizing k with
  | zero => simp [searchShortest] at h
  | succ fuel ih =>
    unfold searchShortest at h
    split at h
    · rename_i r' hr
      cases h
      exact ⟨k, le_refl _, by omega, hr, fun j h1 h2 => by omega⟩
    · rename_i hr
      obtain ⟨k', a, b, c, d⟩ := ih (k + 1) h
      refine ⟨k', by omega, by omega, c, fun j h1 h2 => ?_⟩
      rcases eq_or_lt_of_le h1 with e | e
      · subst e; exact hr
      · exact d j (by omega) h2

theorem search_isSome (x : Double64) (L : Int) (fuel k k' : Nat) (h1 : k ≤ k') (h2 : k' < k + fuel)
    (h : (pickK x L k').isSome) : (searchShortest x L fuel k).isSome := by
  induction fuel generalizing k with
  | zero => omega
  | succ fuel ih =>
    unfold searchShortest
    split
    · rfl
    · rename_i hr
      rcases eq_or_lt_of_le h1 with e | e
      · subst e; rw [hr] at h; simp at h
      · exact ih (k + 1) (by omega) (by omega)

/-! ## Significant digits -/

/-- `m` has at most `s` significant digits. -/
def IsSig (m s : ℕ) : Prop := ∃ m' t : ℕ, m = m' * 10 ^ t ∧ m' < 10 ^ s

theorem IsSig.mono {m s s' : ℕ} (h : IsSig m s) (hs : s ≤ s') : IsSig m s' := by
  obtain ⟨m', t, e, hlt⟩ := h
  exact ⟨m', t, e, lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hs)⟩

theorem isSig_of_le (c k : ℕ) (hk : 1 ≤ k) (h : c ≤ 10 ^ k) : IsSig c k := by
  rcases eq_or_lt_of_le h with e | e
  · exact ⟨1, k, by simp [e], Nat.one_lt_pow (by omega) (by norm_num)⟩
  · exact ⟨c, 0, by simp, e⟩

theorem stripTrailing_spec (fuel c : ℕ) (P : Int) :
    ((stripTrailing fuel c P).1 : ℚ) * (10 : ℚ) ^ (stripTrailing fuel c P).2 = (c : ℚ) * (10 : ℚ) ^ P ∧
      (0 < c → 0 < (stripTrailing fuel c P).1) ∧ (∀ s, IsSig c s → IsSig (stripTrailing fuel c P).1 s) := by
  induction fuel generalizing c P with
  | zero => exact ⟨rfl, id, fun _ h => h⟩
  | succ fuel ih =>
    unfold stripTrailing
    split
    · rename_i h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
      obtain ⟨h0, h10⟩ := h
      obtain ⟨a, b, c'⟩ := ih (c / 10) (P + 1)
      have hc : c = 10 * (c / 10) := by omega
      refine ⟨?_, fun _ => b (by omega), fun s hs => c' s ?_⟩
      · rw [a, zpow_add₀ (by norm_num)]
        conv => rhs; rw [hc]
        push_cast; ring
      · obtain ⟨m', t, e, hlt⟩ := hs
        by_cases ht : t = 0
        · subst ht
          exact ⟨c / 10, 0, by simp, by
            have : c / 10 ≤ c := Nat.div_le_self _ _
            simp at e; omega⟩
        · refine ⟨m', t - 1, ?_, hlt⟩
          rw [e]
          rw [show t = (t - 1) + 1 by omega, Nat.pow_succ]
          rw [show m' * (10 ^ (t - 1) * 10) = 10 * (m' * 10 ^ (t - 1)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
          simp
    · exact ⟨rfl, id, fun _ h => h⟩

/-! ## The printed decimal -/

theorem candidate_le (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false) (k : ℕ) :
    (candidates x (Int.log 10 x.mag) k).1 + 1 ≤ 10 ^ k := by
  rw [candidates_eq x hf hz]
  simp only
  obtain ⟨-, hL2⟩ := mag_bounds_log x hf hz
  have hS : (0 : ℚ) < (10 : ℚ) ^ (Int.log 10 x.mag - k + 1) := zpow_pos (by norm_num) _
  have hlt : x.mag / (10 : ℚ) ^ (Int.log 10 x.mag - k + 1) < (10 ^ k : ℕ) := by
    rw [div_lt_iff₀ hS]
    push_cast
    calc x.mag < (10 : ℚ) ^ (Int.log 10 x.mag + 1) := hL2
      _ = (10 : ℚ) ^ k * (10 : ℚ) ^ (Int.log 10 x.mag - k + 1) := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 1; ring
  have := (Nat.floor_lt (le_of_lt (div_pos (mag_pos x hf hz) hS))).mpr hlt
  omega

/-- The search finds a candidate for every finite nonzero value. -/
theorem search_found (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false) :
    ∃ r, searchShortest x (decLog x) 17 1 = some r := by
  obtain ⟨j, hj⟩ := seventeen_digits x hf hz
  have hs := search_isSome x (decLog x) 17 1 17 (by norm_num) (by norm_num)
    (by rw [decLog_eq x hf hz]; exact pickK_some_of_in x _ 17 hf hz j (by exact_mod_cast hj))
  exact Option.isSome_iff_exists.mp hs

theorem shortestDec_spec (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false) :
    0 < (shortestDec x).1 ∧ InInterval x (((shortestDec x).1 : ℚ) * (10 : ℚ) ^ (shortestDec x).2) := by
  obtain ⟨r, hr⟩ := search_found x hf hz
  obtain ⟨k', -, -, hk, -⟩ := search_some x _ 17 1 r hr
  obtain ⟨c, P⟩ := r
  obtain ⟨-, -, hin⟩ := pickK_spec x _ k' c P hk
  rw [inInterval_spec] at hin
  unfold shortestDec
  simp only [hr, Option.getD_some]
  obtain ⟨a, b, -⟩ := stripTrailing_spec (numDigits c) c P
  refine ⟨b ?_, by rw [a]; exact hin⟩
  -- a candidate in the interval is positive
  by_contra h0
  have hc : c = 0 := by omega
  subst hc
  have hv := mag_pos x hf hz
  have hx := normal_of_finite x hf hz
  rw [inInterval_iff x _ _ hx] at hin
  simp only [Nat.cast_zero, zero_mul, zero_div] at hin
  have hM := hx.bounds.1
  have : (1 : ℚ) ≤ x.mantExp.1 := by exact_mod_cast hM
  rcases hin.1 with h | h <;> split_ifs at h <;> [linarith; linarith; linarith [h.2]; linarith [h.2]]

/-- No decimal with fewer significant digits rounds to a finite nonzero value: if `m · 10^e`
(with `m` of at most `s` significant digits) rounds to `x`, the printed digits have at most `s`
significant digits. -/
theorem shortestDec_shortest (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false)
    (m : ℕ) (e : Int) (s : ℕ) (hm : 0 < m) (hs : IsSig m s)
    (h : roundBinary64 x.neg ((m : ℚ) * (10 : ℚ) ^ e) = x) : IsSig (shortestDec x).1 s := by
  have hd : 0 < (m : ℚ) * (10 : ℚ) ^ e := by positivity
  have hin := (round_eq_iff x hf hz _ hd).mp h
  obtain ⟨r, hr⟩ := search_found x hf hz
  obtain ⟨k', hk1, hk17, hk, hnone⟩ := search_some x _ 17 1 r hr
  obtain ⟨c, P⟩ := r
  obtain ⟨-, hcf, -⟩ := pickK_spec x _ k' c P hk
  have hcle : c ≤ 10 ^ k' := by
    have := candidate_le x hf hz k'
    rw [decLog_eq x hf hz] at hcf
    rcases hcf with e | e <;> omega
  -- the printed digits before stripping
  have hsig : IsSig c k' := isSig_of_le c k' hk1 hcle
  unfold shortestDec
  simp only [hr, Option.getD_some]
  apply (stripTrailing_spec (numDigits c) c P).2.2 s
  -- k' ≤ s, or s ≥ 17
  obtain ⟨m', t, hmt, hm'⟩ := hs
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · subst h0; simp at hm'; subst hm'; simp at hmt; omega
    · exact h0
  by_cases hs17 : 17 ≤ s
  · exact hsig.mono (by omega)
  apply hsig.mono
  by_contra hlt
  push_neg at hlt
  -- a multiple of 10^(L − s + 1) lies in the interval, so the search stops at s
  have hpick := hnone s (by omega) hlt
  have hsome : (pickK x (decLog x) s).isSome := by
    rw [decLog_eq x hf hz]
    generalize hL : Int.log 10 x.mag = L
    have hm'pos : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with h0 | h0
      · subst h0; simp at hmt; omega
      · exact h0
    have hdval : (m : ℚ) * (10 : ℚ) ^ e = (m' : ℚ) * (10 : ℚ) ^ ((t : Int) + e) := by
      rw [hmt, zpow_add₀ (by norm_num), zpow_natCast]; push_cast; ring
    rw [hdval] at hin
    by_cases hbig : L - s + 1 ≤ (t : Int) + e
    · refine pickK_some_of_in x _ s hf hz (m' * 10 ^ ((t : Int) + e - (L - s + 1)).toNat) ?_
      push_cast
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
      convert hin using 3
      omega
    · -- the decimal is below 10^L ≤ x, and 10^L is a multiple in between
      refine pickK_some_of_in x _ s hf hz (10 ^ (s - 1)) ?_
      obtain ⟨hL1, -⟩ := mag_bounds_log x hf hz
      rw [hL] at hL1
      have h10L : ((10 ^ (s - 1) : ℕ) : ℚ) * (10 : ℚ) ^ (L - s + 1) = (10 : ℚ) ^ L := by
        push_cast
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
        congr 1; omega
      rw [h10L]
      apply hin.convex (mag_inInterval x hf hz) _ hL1
      calc (m' : ℚ) * (10 : ℚ) ^ ((t : Int) + e) ≤ (10 ^ s : ℕ) * (10 : ℚ) ^ ((t : Int) + e) := by
            gcongr
        _ = (10 : ℚ) ^ ((s : Int) + ((t : Int) + e)) := by
            push_cast; rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
        _ ≤ (10 : ℚ) ^ L := zpow_le_zpow_right₀ (by norm_num) (by omega)
  rw [hpick] at hsome
  simp at hsome

end Tiramemsu.Codec
