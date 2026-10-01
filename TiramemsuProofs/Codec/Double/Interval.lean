/-
The rounding-interval characterization: a positive rational rounds to a finite nonzero double
`x` exactly when it lies in `x`'s rounding interval (the printer's `roundingInterval`): half a
unit in the last place on each side, a quarter below at a power of two above the smallest
normal exponent, ends included exactly when the significand is even.
-/
import TiramemsuProofs.Codec.Double.Parse

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Doubles]]

/-! ## Round half to even -/

theorem floor_cases (s : ℚ) (hs : 0 ≤ s) : (⌊s⌋₊ : ℚ) ≤ s ∧ s < ⌊s⌋₊ + 1 :=
  ⟨Nat.floor_le hs, Nat.lt_floor_add_one s⟩

/-- `rhe s = M` exactly when `s` is within half a unit of `M`, the ends counting only for an
even `M`. -/
theorem rhe_eq_iff (s : ℚ) (hs : 0 ≤ s) (M : ℕ) :
    rhe s = M ↔ (((M : ℚ) - 1 / 2 < s ∨ (s = (M : ℚ) - 1 / 2 ∧ M % 2 = 0)) ∧
      (s < (M : ℚ) + 1 / 2 ∨ (s = (M : ℚ) + 1 / 2 ∧ M % 2 = 0))) := by
  obtain ⟨f1, f2⟩ := floor_cases s hs
  generalize hf : ⌊s⌋₊ = f at f1 f2
  unfold rhe
  simp only [hf]
  constructor
  · intro h
    split_ifs at h with c1 c2 c3
    · subst h
      exact ⟨Or.inl (by linarith), Or.inl (by linarith)⟩
    · subst h; push_cast
      exact ⟨Or.inl (by linarith), Or.inl (by linarith)⟩
    · subst h
      have : s = f + 1 / 2 := by linarith [not_lt.mp c1, not_lt.mp c2]
      exact ⟨Or.inl (by linarith), Or.inr ⟨this, c3⟩⟩
    · subst h; push_cast
      have : s = f + 1 / 2 := by linarith [not_lt.mp c1, not_lt.mp c2]
      refine ⟨Or.inr ⟨by linarith, by omega⟩, Or.inl (by linarith)⟩
  · rintro ⟨lo, hi⟩
    -- the floor is M − 1 or M
    have hlo : (M : ℚ) - 1 / 2 ≤ s := by rcases lo with h | h <;> [linarith; linarith [h.1]]
    have hhi : s ≤ (M : ℚ) + 1 / 2 := by rcases hi with h | h <;> [linarith; linarith [h.1]]
    have hfM : f = M ∨ f + 1 = M := by
      have a : (f : ℚ) < M + 1 := by linarith
      have b : (M : ℚ) < f + 2 := by linarith
      have a' : f < M + 1 := by exact_mod_cast a
      have b' : M < f + 2 := by exact_mod_cast b
      omega
    rcases hfM with rfl | rfl
    · -- s ∈ [f, f + 1/2]
      by_cases c1 : s - f < 1 / 2
      · rw [if_pos c1]
      · rw [if_neg c1]
        have hs' : s = f + 1 / 2 := by linarith [not_lt.mp c1]
        rw [if_neg (by linarith)]
        rcases hi with h | h
        · exact absurd hs' (by linarith)
        · rw [if_pos h.2]
    · -- s ∈ [f + 1/2, f + 1)
      push_cast at lo hi hlo hhi
      by_cases c1 : s - f < 1 / 2
      · exfalso; linarith
      · rw [if_neg c1]
        by_cases c2 : 1 / 2 < s - f
        · rw [if_pos c2]
        · rw [if_neg c2]
          have hs' : s = f + 1 / 2 := by linarith [not_lt.mp c1, not_lt.mp c2]
          rcases lo with h | h
          · exact absurd hs' (by linarith)
          · rw [if_neg (by omega)]

/-! ## Finite values -/

theorem Double64.ofMantExp_ne (neg : Bool) (M : ℕ) (E : Int) (h : M ≠ 2 ^ 53) :
    Double64.ofMantExp neg M E = if M < 2 ^ 52 then Double64.ofFields neg 0 M
      else if E + 1075 ≥ 2047 then Double64.inf neg
      else Double64.ofFields neg (E + 1075).toNat (M - 2 ^ 52) := by
  unfold Double64.ofMantExp; simp only [if_neg h]

theorem Double64.ofMantExp_carry (neg : Bool) (E : Int) :
    Double64.ofMantExp neg (2 ^ 53) E = if E + 1 + 1075 ≥ 2047 then Double64.inf neg
      else Double64.ofFields neg (E + 1 + 1075).toNat 0 := by
  unfold Double64.ofMantExp; simp only [ite_true, lt_irrefl, ite_false, Nat.sub_self]

/-- The value of a finite nonzero double: its normalized significand and exponent. -/
structure Normal (x : Double64) (M : ℕ) (E : Int) : Prop where
  mantExp : x.mantExp = (M, E)
  finite : x.biasedExp ≤ 2046
  bounds : (1 ≤ M ∧ M < 2 ^ 53)
  sub : (x.biasedExp = 0 ∧ M < 2 ^ 52 ∧ E = -1074) ∨
    (1 ≤ x.biasedExp ∧ 2 ^ 52 ≤ M ∧ E = (x.biasedExp : Int) - 1075)

theorem normal_of_finite (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false) :
    Normal x x.mantExp.1 x.mantExp.2 := by
  have hb := Double64.biasedExp_lt x
  have hfr := Double64.frac_lt x
  simp only [Double64.isFinite, bne_iff_ne, ne_eq] at hf
  simp only [Double64.isZero, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hz
  unfold Double64.mantExp
  refine ⟨rfl, by omega, ?_, ?_⟩
  · split <;> constructor <;> omega
  · split
    · left; refine ⟨by assumption, by simpa using hfr, rfl⟩
    · right; refine ⟨by omega, by simp, rfl⟩

/-- A finite nonzero double is the `ofMantExp` of its significand and exponent. -/
theorem Normal.eq_ofMantExp {x : Double64} {M : ℕ} {E : Int} (h : Normal x M E) :
    Double64.ofMantExp x.neg M E = x := by
  have hx := Double64.eq_ofFields x
  have hm := h.mantExp
  have hb := h.bounds
  unfold Double64.mantExp at hm
  rw [Double64.ofMantExp_ne _ _ _ (by omega)]
  rcases h.sub with ⟨h0, hM, hE⟩ | ⟨h1, hM, hE⟩
  · simp only [h0, ite_true, Prod.mk.injEq] at hm
    rw [if_pos hM]
    conv => rhs; rw [hx]
    rw [h0, hm.1]
  · simp only [show x.biasedExp ≠ 0 by omega, ite_false, Prod.mk.injEq] at hm
    rw [if_neg (by omega), if_neg (by have := h.finite; omega)]
    conv => rhs; rw [hx]
    have e1 : (E + 1075).toNat = x.biasedExp := by omega
    have e2 : M - 2 ^ 52 = x.frac := by omega
    rw [e1, e2]

/-- A normal power of two has significand `2^52`. -/
theorem Normal.pow_two {x : Double64} {M : ℕ} {E : Int} (h : Normal x M E) (hf : x.frac = 0)
    (hb : 1 ≤ x.biasedExp) : M = 2 ^ 52 := by
  have hm := h.mantExp
  unfold Double64.mantExp at hm
  simp only [show x.biasedExp ≠ 0 by omega, ite_false, Prod.mk.injEq] at hm
  omega

/-- `inf` is not finite. -/
theorem Double64.inf_biasedExp (neg : Bool) : (Double64.inf neg).biasedExp = 2047 := by
  cases neg <;> decide

/-- `ofMantExp` results that are finite determine their significand and exponent. -/
theorem ofMantExp_eq_normal (neg : Bool) (Mr : ℕ) (Er : Int) (x : Double64) (M : ℕ) (E : Int)
    (hx : Normal x M E) (hMr : Mr ≤ 2 ^ 53) (hEr : -1074 ≤ Er)
    (hsub : Mr < 2 ^ 52 → Er = -1074) (h : Double64.ofMantExp neg Mr Er = x) :
    (Mr = M ∧ Er = E) ∨ (Mr = 2 ^ 53 ∧ M = 2 ^ 52 ∧ Er + 1 = E ∧ 2 ≤ x.biasedExp) ∨ (Mr = 0) := by
  have hxf := Double64.eq_ofFields x
  have hm := hx.mantExp
  unfold Double64.mantExp at hm
  have hfr := Double64.frac_lt x
  have hfin : ∀ e f, e ≤ 2046 → f < 2 ^ 52 → Double64.ofFields neg e f = x →
      e = x.biasedExp ∧ f = x.frac := by
    intro e f he hf hh
    rw [hxf] at hh
    obtain ⟨-, a, b⟩ := Double64.ofFields_inj (by omega) (Double64.biasedExp_lt x) hf hfr hh
    exact ⟨a, b⟩
  have hinf : Double64.inf neg ≠ x := by
    intro e
    have := hx.finite
    rw [← e, Double64.inf_biasedExp] at this
    omega
  by_cases hc : Mr = 2 ^ 53
  · subst hc
    rw [Double64.ofMantExp_carry] at h
    split_ifs at h with c
    · exact absurd h hinf
    · obtain ⟨e1, f1⟩ := hfin _ _ (by omega) (by omega) h
      right; left
      rcases hx.sub with ⟨h0, hM, hE⟩ | ⟨h1, hM, hE⟩
      · omega
      · simp only [show x.biasedExp ≠ 0 by omega, ite_false, Prod.mk.injEq] at hm
        refine ⟨rfl, by omega, by omega, by omega⟩
  · rw [Double64.ofMantExp_ne _ _ _ hc] at h
    by_cases hs : Mr < 2 ^ 52
    · rw [if_pos hs] at h
      obtain ⟨e1, f1⟩ := hfin _ _ (by omega) (by omega) h
      by_cases hz : Mr = 0
      · exact Or.inr (Or.inr hz)
      left
      rcases hx.sub with ⟨h0, hM, hE⟩ | ⟨h1, hM, hE⟩
      · simp only [h0, ite_true, Prod.mk.injEq] at hm
        exact ⟨by omega, by rw [hsub hs]; exact hE.symm⟩
      · omega
    · rw [if_neg hs] at h
      split_ifs at h with c
      · exact absurd h hinf
      · obtain ⟨e1, f1⟩ := hfin _ _ (by omega) (by omega) h
        left
        rcases hx.sub with ⟨h0, hM, hE⟩ | ⟨h1, hM, hE⟩
        · omega
        · simp only [show x.biasedExp ≠ 0 by omega, ite_false, Prod.mk.injEq] at hm
          exact ⟨by omega, by omega⟩

/-! ## The interval -/

/-- The rounding interval of `x` as a predicate on positive rationals (`lo`, `hi` in units of
`2^(E−2)`, from the printer's `roundingInterval`). -/
def InInterval (x : Double64) (r : ℚ) : Prop :=
  let u : ℚ := (2 : ℚ) ^ (x.mantExp.2 - 2)
  let lo := (roundingInterval x).1
  let hi := (roundingInterval x).2.1
  let incl := (roundingInterval x).2.2
  (((lo : ℚ) * u < r) ∨ (incl = true ∧ (lo : ℚ) * u = r)) ∧ ((r < (hi : ℚ) * u) ∨ (incl = true ∧ r = (hi : ℚ) * u))

theorem roundingInterval_eq (x : Double64) :
    roundingInterval x = ((if x.frac = 0 ∧ x.biasedExp > 1 then 4 * x.mantExp.1 - 1 else 4 * x.mantExp.1 - 2),
      4 * x.mantExp.1 + 2, x.mantExp.1 % 2 == 0) := by
  unfold roundingInterval
  simp

theorem zpow_two_sub (E : Int) (k : Int) : (2 : ℚ) ^ (E - k) = (2 : ℚ) ^ E / (2 : ℚ) ^ k := by
  rw [zpow_sub₀ (by norm_num)]

/-- In units of `2^E`: the interval is `[M − 1/2, M + 1/2]`, or `[M − 1/4, M + 1/2]` at a
power of two above the smallest normal exponent. -/
theorem inInterval_iff (x : Double64) (M : ℕ) (E : Int) (hx : Normal x M E) (r : ℚ) :
    InInterval x r ↔
      (((if x.frac = 0 ∧ x.biasedExp > 1 then (M : ℚ) - 1 / 4 else (M : ℚ) - 1 / 2) < r / (2 : ℚ) ^ E ∨
          (M % 2 = 0 ∧ (if x.frac = 0 ∧ x.biasedExp > 1 then (M : ℚ) - 1 / 4 else (M : ℚ) - 1 / 2) = r / (2 : ℚ) ^ E)) ∧
        (r / (2 : ℚ) ^ E < (M : ℚ) + 1 / 2 ∨ (M % 2 = 0 ∧ r / (2 : ℚ) ^ E = (M : ℚ) + 1 / 2))) := by
  have hm := hx.mantExp
  have hM1 := hx.bounds.1
  unfold InInterval
  rw [roundingInterval_eq, hm]
  simp only [beq_iff_eq]
  have hp : (0 : ℚ) < (2 : ℚ) ^ E := two_zpow_pos E
  have hu : (2 : ℚ) ^ (E - 2) = (2 : ℚ) ^ E / 4 := by
    rw [zpow_two_sub]; norm_num
  rw [hu]
  have key : ∀ (a : ℕ) (b : ℚ), (a : ℚ) * ((2 : ℚ) ^ E / 4) = (a / 4 : ℚ) * (2 : ℚ) ^ E := by
    intro a b; ring
  have c1 : ∀ c : ℚ, (c * ((2 : ℚ) ^ E / 4) < r ↔ c / 4 < r / (2 : ℚ) ^ E) := by
    intro c; rw [lt_div_iff₀ hp]; constructor <;> intro h <;> linarith
  have c2 : ∀ c : ℚ, (r < c * ((2 : ℚ) ^ E / 4) ↔ r / (2 : ℚ) ^ E < c / 4) := by
    intro c; rw [div_lt_iff₀ hp]; constructor <;> intro h <;> linarith
  have c3 : ∀ c : ℚ, (c * ((2 : ℚ) ^ E / 4) = r ↔ c / 4 = r / (2 : ℚ) ^ E) := by
    intro c; rw [eq_div_iff (ne_of_gt hp)]; constructor <;> intro h <;> linarith
  have c4 : ∀ c : ℚ, (r = c * ((2 : ℚ) ^ E / 4) ↔ r / (2 : ℚ) ^ E = c / 4) := by
    intro c; rw [div_eq_iff (ne_of_gt hp)]; constructor <;> intro h <;> linarith
  rw [c1, c2, c3, c4]
  have e1 : ((4 * M - 1 : ℕ) : ℚ) / 4 = (M : ℚ) - 1 / 4 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : ((4 * M - 2 : ℕ) : ℚ) / 4 = (M : ℚ) - 1 / 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e3 : ((4 * M + 2 : ℕ) : ℚ) / 4 = (M : ℚ) + 1 / 2 := by push_cast; ring
  split_ifs <;> simp only [e1, e2, e3] <;> tauto

/-! ## Binade facts of the reference rounding -/

theorem log_eq_of_bounds (r : ℚ) (hr : 0 < r) (t : Int) (h1 : (2 : ℚ) ^ t ≤ r) (h2 : r < (2 : ℚ) ^ (t + 1)) :
    Int.log 2 r = t := int_log_eq (b := 2) (by decide) hr (by exact_mod_cast h1) (by exact_mod_cast h2)

theorem round_eq (neg : Bool) (r : ℚ) (hr : 0 < r) :
    roundBinary64 neg r = Double64.ofMantExp neg (rhe (r / (2 : ℚ) ^ (max (Int.log 2 r) (-1022) - 52)))
      (max (Int.log 2 r) (-1022) - 52) := by
  unfold roundBinary64; rw [if_neg (not_le.mpr hr)]

theorem div_zpow_bounds (r : ℚ) (E : Int) (lo hi : ℚ) (h1 : lo * (2 : ℚ) ^ E ≤ r) (h2 : r < hi * (2 : ℚ) ^ E) :
    lo ≤ r / (2 : ℚ) ^ E ∧ r / (2 : ℚ) ^ E < hi := by
  have hp := two_zpow_pos E
  exact ⟨(le_div_iff₀ hp).mpr h1, (div_lt_iff₀ hp).mpr h2⟩

/-- The characterization: a positive rational rounds to a finite nonzero `x` (with `x`'s sign)
exactly when it lies in `x`'s rounding interval. -/
theorem round_eq_iff (x : Double64) (hf : x.isFinite = true) (hz : x.isZero = false) (r : ℚ) (hr : 0 < r) :
    roundBinary64 x.neg r = x ↔ InInterval x r := by
  have hx := normal_of_finite x hf hz
  generalize hME : x.mantExp = p at hx
  obtain ⟨M, E⟩ := p
  simp only at hx
  have hM1 := hx.bounds.1
  have hM2 := hx.bounds.2
  rw [inInterval_iff x M E hx r, round_eq _ _ hr]
  have hp := two_zpow_pos E
  have hrE : 0 ≤ r / (2 : ℚ) ^ E := le_of_lt (div_pos hr hp)
  constructor
  · -- a rounding to x lies in the interval
    intro h
    generalize hL : Int.log 2 r = t at h
    have l1 := Int.zpow_log_le_self (b := 2) (by decide) hr
    have l2 := Int.lt_zpow_succ_log_self (b := 2) (by decide) r
    push_cast at l1 l2
    rw [hL] at l1 l2
    generalize hEr : max t (-1022) - 52 = Er at h
    have hpr := two_zpow_pos Er
    have hs0 : 0 ≤ r / (2 : ℚ) ^ Er := le_of_lt (div_pos hr hpr)
    -- bounds of the scaled value and of its rounding
    have hsb : r / (2 : ℚ) ^ Er < 2 ^ 53 ∧ (-1022 ≤ t → (2 : ℚ) ^ 52 ≤ r / (2 : ℚ) ^ Er) ∧
        (t < -1022 → r / (2 : ℚ) ^ Er < 2 ^ 52) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [div_lt_iff₀ hpr]
        calc r < (2 : ℚ) ^ (t + 1) := l2
          _ ≤ (2 : ℚ) ^ (53 + Er) := zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ = 2 ^ 53 * (2 : ℚ) ^ Er := by rw [zpow_add₀ (by norm_num)]; norm_num
      · intro ht
        rw [le_div_iff₀ hpr]
        calc 2 ^ 52 * (2 : ℚ) ^ Er = (2 : ℚ) ^ (52 + Er) := by rw [zpow_add₀ (by norm_num)]; norm_num
          _ ≤ (2 : ℚ) ^ t := zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ ≤ r := l1
      · intro ht
        rw [div_lt_iff₀ hpr]
        calc r < (2 : ℚ) ^ (t + 1) := l2
          _ ≤ (2 : ℚ) ^ (52 + Er) := zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ = 2 ^ 52 * (2 : ℚ) ^ Er := by rw [zpow_add₀ (by norm_num)]; norm_num
    obtain ⟨hs53, hsn, hss⟩ := hsb
    have hMr53 : rhe (r / (2 : ℚ) ^ Er) ≤ 2 ^ 53 :=
      (rhe_bounds _ 0 (2 ^ 53) (by simpa using hs0) (by exact_mod_cast hs53)).2
    have hsubn : rhe (r / (2 : ℚ) ^ Er) < 2 ^ 52 → Er = -1074 := by
      intro hlt
      by_contra hne
      have ht : -1022 ≤ t := by omega
      have := (rhe_bounds _ (2 ^ 52) (2 ^ 53) (by exact_mod_cast hsn ht) (by exact_mod_cast hs53)).1
      omega
    have hres := ofMantExp_eq_normal x.neg _ Er x M E hx hMr53 (by omega) hsubn h
    have hR := (rhe_eq_iff _ hs0 _).mp rfl
    generalize hMr : rhe (r / (2 : ℚ) ^ Er) = Mr at hres hR hMr53 hsubn h
    rcases hres with ⟨hMeq, hEeq⟩ | ⟨hMeq, hM, hEE, hbe⟩ | hMeq
    · -- same significand and exponent
      rw [hMeq, hEeq] at hR
      have hsnE : -1022 ≤ t → (2 : ℚ) ^ 52 ≤ r / (2 : ℚ) ^ E := by rw [← hEeq]; exact hsn
      clear hsn
      refine ⟨?_, ?_⟩
      · split_ifs with hpow
        · -- a power of two above the smallest normal: the scaled value is at least M
          left
          rcases hx.sub with ⟨h0, -, -⟩ | ⟨-, hMl, hEv⟩
          · omega
          · have hMeq : M = 2 ^ 52 := by
              have := hME; unfold Double64.mantExp at this
              simp only [show x.biasedExp ≠ 0 by omega, ite_false, Prod.mk.injEq] at this
              omega
            have ht : -1022 ≤ t := by omega
            have := hsnE ht
            rw [hMeq]; push_cast; linarith
        · rcases hR.1 with h1 | h1
          · exact Or.inl h1
          · exact Or.inr ⟨h1.2, h1.1.symm⟩
      · rcases hR.2 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨h1.2, h1.1⟩
    · -- carry into x's binade from below
      subst hMeq
      have hEr' : Er = E - 1 := by omega
      subst hEr'
      have hfr : x.frac = 0 := by
        have := hME; unfold Double64.mantExp at this
        simp only [show x.biasedExp ≠ 0 by omega, ite_false, Prod.mk.injEq] at this
        omega
      have hscale : r / (2 : ℚ) ^ E = (r / (2 : ℚ) ^ (E - 1)) / 2 := by
        rw [zpow_sub₀ (by norm_num)]; field_simp
      rw [hscale, if_pos ⟨hfr, by omega⟩, hM]
      push_cast at hR ⊢
      constructor
      · rcases hR.1 with h1 | h1
        · left; linarith
        · right; refine ⟨by norm_num, by linarith [h1.1]⟩
      · left; linarith
    · -- rounding to zero is not a nonzero x
      exfalso
      subst hMeq
      rw [Double64.ofMantExp_ne _ _ _ (by norm_num), if_pos (by norm_num)] at h
      have h0 := Double64.ofFields_fields x.neg 0 0 (by norm_num) (by norm_num)
      rw [h] at h0
      simp only [Double64.isZero, h0.2.1, h0.2.2, beq_self_eq_true, Bool.and_self] at hz
      exact absurd hz (by decide)
  · -- a value in the interval rounds to x
    intro hin
    obtain ⟨hlo, hhi⟩ := hin
    have hsU : r / (2 : ℚ) ^ E ≤ (M : ℚ) + 1 / 2 := by
      rcases hhi with h | h <;> [exact le_of_lt h; exact le_of_eq h.2]
    have hsL : (if x.frac = 0 ∧ x.biasedExp > 1 then (M : ℚ) - 1 / 4 else (M : ℚ) - 1 / 2) ≤ r / (2 : ℚ) ^ E := by
      rcases hlo with h | h <;> [exact le_of_lt h; exact le_of_eq h.2]
    have hrw : r = (r / (2 : ℚ) ^ E) * (2 : ℚ) ^ E := by field_simp
    have hxe := hx.eq_ofMantExp
    rcases hx.sub with ⟨h0, hMs, hE⟩ | ⟨h1, hMl, hE⟩
    · -- subnormal x: r < 2^−1022, so the exponent is the subnormal one
      subst hE
      have hpow : ¬ (x.frac = 0 ∧ x.biasedExp > 1) := by omega
      rw [if_neg hpow] at hlo hsL
      have hrlt : r < (2 : ℚ) ^ (-1022 : Int) := by
        rw [hrw]
        calc r / (2 : ℚ) ^ (-1074 : Int) * (2 : ℚ) ^ (-1074 : Int) ≤ ((M : ℚ) + 1 / 2) * (2 : ℚ) ^ (-1074 : Int) := by gcongr
          _ < (2 ^ 52 : ℚ) * (2 : ℚ) ^ (-1074 : Int) := by
            gcongr
            have : (M : ℚ) + 1 ≤ 2 ^ 52 := by exact_mod_cast hMs
            linarith
          _ = (2 : ℚ) ^ (-1022 : Int) := by rw [show (2 ^ 52 : ℚ) = (2 : ℚ) ^ (52 : Int) by norm_num, ← zpow_add₀ (by norm_num)]; norm_num
      have ht : Int.log 2 r < -1022 := (Int.lt_zpow_iff_log_lt (b := 2) (by decide) hr).mp (by exact_mod_cast hrlt)
      rw [show max (Int.log 2 r) (-1022) - 52 = -1074 by omega]
      have hR : rhe (r / (2 : ℚ) ^ (-1074 : Int)) = M := by
        rw [rhe_eq_iff _ hrE]
        refine ⟨?_, ?_⟩
        · rcases hlo with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h.2.symm, h.1⟩
        · rcases hhi with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h.2, h.1⟩
      rw [hR, hxe]
    · by_cases hbig : (2 : ℚ) ^ (52 : Int) ≤ r / (2 : ℚ) ^ E
      · -- r is in x's binade: same exponent
        have ht : Int.log 2 r = 52 + E := by
          apply log_eq_of_bounds r hr
          · rw [hrw, zpow_add₀ (by norm_num)]
            exact mul_le_mul_of_nonneg_right hbig (le_of_lt hp)
          · rw [hrw, show 52 + E + 1 = 53 + E by ring, zpow_add₀ (by norm_num)]
            apply mul_lt_mul_of_pos_right _ hp
            calc r / (2 : ℚ) ^ E ≤ (M : ℚ) + 1 / 2 := hsU
              _ < (2 : ℚ) ^ (53 : Int) := by
                have : (M : ℚ) + 1 ≤ 2 ^ 53 := by exact_mod_cast hM2
                norm_num at this ⊢; linarith
        rw [show max (Int.log 2 r) (-1022) - 52 = E by omega]
        have hR : rhe (r / (2 : ℚ) ^ E) = M := by
          rw [rhe_eq_iff _ hrE]
          refine ⟨?_, ?_⟩
          · split_ifs at hlo with hpow
            · left
              have hM52 : M = 2 ^ 52 := by
                have := hME; unfold Double64.mantExp at this
                simp only [show x.biasedExp ≠ 0 by omega, ite_false, Prod.mk.injEq] at this
                omega
              rw [hM52]; push_cast; norm_num at hbig ⊢; linarith
            · rcases hlo with h | h
              · exact Or.inl h
              · exact Or.inr ⟨h.2.symm, h.1⟩
          · rcases hhi with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h.2, h.1⟩
        rw [hR, hxe]
      · -- r is below x's binade: M = 2^52
        push_neg at hbig
        have hM52 : M = 2 ^ 52 := by
          have : (M : ℚ) - 1 / 2 < 2 ^ 52 := by
            split_ifs at hsL <;> norm_num at hbig <;> linarith
          have : (M : ℚ) < 2 ^ 52 + 1 := by linarith
          have : M < 2 ^ 52 + 1 := by exact_mod_cast this
          omega
        subst hM52
        have hfr : x.frac = 0 := by
          have := hME; unfold Double64.mantExp at this
          simp only [show x.biasedExp ≠ 0 by omega, ite_false, Prod.mk.injEq] at this
          omega
        by_cases hb1 : x.biasedExp > 1
        · -- a power of two: the asymmetric lower quarter rounds up into x
          rw [if_pos ⟨hfr, hb1⟩] at hlo hsL
          have ht : Int.log 2 r = 51 + E := by
            apply log_eq_of_bounds r hr
            · rw [hrw, zpow_add₀ (by norm_num)]
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hp)
              calc (2 : ℚ) ^ (51 : Int) ≤ ((2 ^ 52 : ℕ) : ℚ) - 1 / 4 := by norm_num
                _ ≤ r / (2 : ℚ) ^ E := hsL
            · rw [hrw, show 51 + E + 1 = 52 + E by ring, zpow_add₀ (by norm_num)]
              exact mul_lt_mul_of_pos_right hbig hp
          rw [show max (Int.log 2 r) (-1022) - 52 = E - 1 by omega]
          have hscale : r / (2 : ℚ) ^ (E - 1) = 2 * (r / (2 : ℚ) ^ E) := by
            rw [zpow_sub₀ (by norm_num)]; field_simp
          have hR : rhe (r / (2 : ℚ) ^ (E - 1)) = 2 ^ 53 := by
            rw [hscale, rhe_eq_iff _ (by positivity)]
            push_cast at hlo ⊢
            norm_num at hbig
            refine ⟨?_, Or.inl (by linarith)⟩
            rcases hlo with h | h
            · left; linarith
            · right; refine ⟨by linarith [h.2], by norm_num⟩
          have hfin := hx.finite
          rw [hR, Double64.ofMantExp_carry, if_neg (show ¬ (E - 1 + 1 + 1075 ≥ 2047) by omega)]
          conv => rhs; rw [← hxe]
          rw [Double64.ofMantExp_ne _ _ _ (by norm_num), if_neg (show ¬ ((2 : ℕ) ^ 52 < 2 ^ 52) by norm_num),
            if_neg (show ¬ (E + 1075 ≥ 2047) by omega), show E - 1 + 1 + 1075 = E + 1075 by ring,
            Nat.sub_self]
        · -- the smallest normal: symmetric, the subnormal exponent applies
          have hbe1 : x.biasedExp = 1 := by omega
          rw [if_neg (by omega)] at hlo hsL
          have hE' : E = -1074 := by omega
          subst hE'
          have hrlt : r < (2 : ℚ) ^ (-1022 : Int) := by
            rw [hrw]
            calc r / (2 : ℚ) ^ (-1074 : Int) * (2 : ℚ) ^ (-1074 : Int) < (2 : ℚ) ^ (52 : Int) * (2 : ℚ) ^ (-1074 : Int) :=
                  mul_lt_mul_of_pos_right hbig hp
              _ = (2 : ℚ) ^ (-1022 : Int) := by rw [← zpow_add₀ (by norm_num)]; norm_num
          have ht : Int.log 2 r < -1022 := (Int.lt_zpow_iff_log_lt (b := 2) (by decide) hr).mp (by exact_mod_cast hrlt)
          rw [show max (Int.log 2 r) (-1022) - 52 = -1074 by omega]
          have hR : rhe (r / (2 : ℚ) ^ (-1074 : Int)) = 2 ^ 52 := by
            rw [rhe_eq_iff _ hrE]
            refine ⟨?_, ?_⟩
            · rcases hlo with h | h
              · exact Or.inl h
              · exact Or.inr ⟨h.2.symm, h.1⟩
            · rcases hhi with h | h
              · exact Or.inl h
              · exact Or.inr ⟨h.2, h.1⟩
          rw [hR, hxe]

end Tiramemsu.Codec
