/-
Proofs of the civil calendar: `civilFromDays` and `daysFromCivil` are inverse bijections
between all integers and all valid proleptic Gregorian dates.
-/
import Tiramemsu.Codec.Civil
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Dates And Times]]

namespace Civil

/-- Days from the start of an era (a March 1 of a year divisible by 400) to the start of
era-year `y` (0–400). -/
def S (y : Int) : Int := 365 * y + y / 4 - y / 100 + y / 400

/-- The era-year of a day of the era. -/
def yoeOf (doe : Int) : Int := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365

theorem yoe_eq (doe : Int) (h0 : 0 ≤ doe) (h1 : doe < 146096) :
    yoeOf doe = 100 * min (doe / 36524) 3 + 4 * ((doe - 36524 * min (doe / 36524) 3) / 1461)
      + min (((doe - 36524 * min (doe / 36524) 3) % 1461) / 365) 3 := by
  unfold yoeOf
  obtain ⟨c, hc⟩ : ∃ c, c = min (doe / 36524) 3 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by omega
  have hc3 : c ≤ 3 := by omega
  rw [← hc]
  interval_cases c <;> omega

theorem S_split (c q r : Int) (hc : 0 ≤ c) (hc3 : c ≤ 3) (hq : 0 ≤ q) (hq24 : q ≤ 24)
    (hr : 0 ≤ r) (hr3 : r ≤ 3) : S (100 * c + 4 * q + r) = 36524 * c + 1461 * q + 365 * r := by
  unfold S; omega

theorem S_century (c : Int) (hc : 0 ≤ c) (hc3 : c ≤ 3) :
    S (100 * (c + 1)) = 36524 * (c + 1) + (if c = 3 then 1 else 0) := by
  unfold S; interval_cases c <;> simp

/-- The era-year of a day is the year whose span contains it. -/
theorem yoe_spec (doe : Int) (h0 : 0 ≤ doe) (h1 : doe < 146097) :
    0 ≤ yoeOf doe ∧ yoeOf doe < 400 ∧ S (yoeOf doe) ≤ doe ∧ doe < S (yoeOf doe + 1) := by
  by_cases hlast : doe = 146096
  · subst hlast; decide
  have h1' : doe < 146096 := by omega
  rw [yoe_eq doe h0 h1']
  obtain ⟨c, hc⟩ : ∃ c, c = min (doe / 36524) 3 := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : 0 ≤ c := by omega
  have hc3 : c ≤ 3 := by omega
  have hs : doe - 36524 * c < 36524 := by omega
  have hs0 : 0 ≤ doe - 36524 * c := by omega
  obtain ⟨q, hq⟩ : ∃ q, q = (doe - 36524 * c) / 1461 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (doe - 36524 * c) % 1461 := ⟨_, rfl⟩
  rw [← hq, ← ht]
  have hq0 : 0 ≤ q := by omega
  have hq24 : q ≤ 24 := by omega
  have ht0 : 0 ≤ t := by omega
  have ht1 : t < 1461 := by omega
  have hdoe : doe = 36524 * c + 1461 * q + t := by omega
  obtain ⟨r, hr⟩ : ∃ r, r = min (t / 365) 3 := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 ≤ r := by omega
  have hr3 : r ≤ 3 := by omega
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [S_split c q r hc0 hc3 hq0 hq24 hr0 hr3]; omega
  · by_cases hr' : r < 3
    · have := S_split c q (r + 1) hc0 hc3 hq0 hq24 (by omega) (by omega)
      rw [show 100 * c + 4 * q + r + 1 = 100 * c + 4 * q + (r + 1) by ring, this]; omega
    · by_cases hq' : q < 24
      · have := S_split c (q + 1) 0 hc0 hc3 (by omega) (by omega) (le_refl _) (by omega)
        rw [show 100 * c + 4 * q + r + 1 = 100 * c + 4 * (q + 1) + 0 by omega, this]; omega
      · have := S_century c hc0 hc3
        rw [show 100 * c + 4 * q + r + 1 = 100 * (c + 1) by omega, this]
        split <;> omega

theorem S_mono {a b : Int} (_ha : 0 ≤ a) (hab : a < b) : S a < S b := by
  unfold S; omega

theorem S_mono_le {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) : S a ≤ S b := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact le_of_lt (S_mono ha h)

/-- The era-year of a day is unique. -/
theorem yoe_unique (doe y : Int) (h0 : 0 ≤ doe) (h1 : doe < 146097) (hy0 : 0 ≤ y) (hy1 : y < 400)
    (hlo : S y ≤ doe) (hhi : doe < S (y + 1)) : yoeOf doe = y := by
  obtain ⟨a0, a1, a2, a3⟩ := yoe_spec doe h0 h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := S_mono_le (by omega) (show yoeOf doe + 1 ≤ y by omega); omega
  · have := S_mono_le (by omega) (show y + 1 ≤ yoeOf doe by omega); omega

/-- Year lengths: era-year `y` (March-based) has 366 days exactly when the following
calendar year is a leap year. -/
theorem S_succ (y : Int) (hy0 : 0 ≤ y) (hy1 : y < 400) :
    S (y + 1) - S y = if (y + 1) % 4 = 0 ∧ ((y + 1) % 100 ≠ 0 ∨ (y + 1) % 400 = 0) then 366 else 365 := by
  unfold S; split <;> omega

/-- Month lengths in the March-based numbering (index 11 is February, at most 29 days). -/
def monthLen (mp : Int) : Int :=
  if mp = 11 then 29 else if mp = 1 ∨ mp = 3 ∨ mp = 6 ∨ mp = 8 then 30 else 31

/-- The month part: the day of the (March-based) year as month index and day. -/
theorem month_spec (doy : Int) (h0 : 0 ≤ doy) (h1 : doy ≤ 365) :
    0 ≤ (5 * doy + 2) / 153 ∧ (5 * doy + 2) / 153 ≤ 11 ∧
      1 ≤ doy - (153 * ((5 * doy + 2) / 153) + 2) / 5 + 1 ∧
      doy - (153 * ((5 * doy + 2) / 153) + 2) / 5 + 1 ≤ monthLen ((5 * doy + 2) / 153) ∧
      ((5 * doy + 2) / 153 = 11 → doy - (153 * ((5 * doy + 2) / 153) + 2) / 5 + 1 = doy - 336) := by
  generalize hm : (5 * doy + 2) / 153 = mp
  have hmp0 : 0 ≤ mp := by omega
  have hmp1 : mp ≤ 11 := by omega
  refine ⟨hmp0, hmp1, ?_⟩
  interval_cases mp <;> simp [monthLen] <;> omega

/-- The month index is recovered from the day of the year. -/
theorem month_inv (mp d : Int) (h0 : 0 ≤ mp) (h1 : mp ≤ 11) (hd : 1 ≤ d) (hd2 : d ≤ monthLen mp) :
    (5 * ((153 * mp + 2) / 5 + d - 1) + 2) / 153 = mp := by
  interval_cases mp <;> simp [monthLen] at hd2 <;> omega

end Civil

theorem isLeap_iff (y : Int) : isLeap y = true ↔ (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)) := by
  unfold isLeap
  by_cases h4 : y % 4 = 0 <;> by_cases h100 : y % 100 = 0 <;> by_cases h400 : y % 400 = 0 <;>
    simp [h4, h100, h400] <;> omega

namespace Civil

/-- The date of an era, an era-year and a day of the March-based year, through the month
index `mp`. -/
def fromParts (e Y doy mp : Int) : Int × Nat × Nat :=
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then Y + e * 400 + 1 else Y + e * 400, m.toNat, d.toNat)

/-- The day of the era of a day number. -/
def doeOf (z : Int) : Int := z + 719468 - (z + 719468) / 146097 * 146097

/-- The day of the March-based year. -/
def doyOf (doe Y : Int) : Int := doe - (365 * Y + Y / 4 - Y / 100)

theorem civilFromDays_eq (z : Int) :
    civilFromDays z = fromParts ((z + 719468) / 146097) (yoeOf (doeOf z))
      (doyOf (doeOf z) (yoeOf (doeOf z))) ((5 * doyOf (doeOf z) (yoeOf (doeOf z)) + 2) / 153) := rfl

/-- The day number of a March-based year `y'`, month index `mp` and day `d`. -/
def dayNumber (y' mp : Int) (d : Nat) : Int :=
  let era := y' / 400
  let yoe := y' - era * 400
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

theorem daysFromCivil_eq (y : Int) (m d : Nat) :
    daysFromCivil y m d = dayNumber (if m ≤ 2 then y - 1 else y)
      (if m > 2 then (m : Int) - 3 else (m : Int) + 9) d := rfl

end Civil

/-- Facts about the era decomposition used by `civilFromDays`. -/
theorem civil_parts (z : Int) :
    0 ≤ Civil.doeOf z ∧ Civil.doeOf z < 146097 ∧ 0 ≤ Civil.yoeOf (Civil.doeOf z) ∧
      Civil.yoeOf (Civil.doeOf z) < 400 ∧
      0 ≤ Civil.doyOf (Civil.doeOf z) (Civil.yoeOf (Civil.doeOf z)) ∧
      Civil.doyOf (Civil.doeOf z) (Civil.yoeOf (Civil.doeOf z)) ≤ 365 ∧
      (Civil.doyOf (Civil.doeOf z) (Civil.yoeOf (Civil.doeOf z)) = 365 →
        (Civil.yoeOf (Civil.doeOf z) + 1) % 4 = 0 ∧ ((Civil.yoeOf (Civil.doeOf z) + 1) % 100 ≠ 0 ∨
          (Civil.yoeOf (Civil.doeOf z) + 1) % 400 = 0)) := by
  have hd0 : 0 ≤ Civil.doeOf z := by unfold Civil.doeOf; omega
  have hd1 : Civil.doeOf z < 146097 := by unfold Civil.doeOf; omega
  generalize Civil.doeOf z = doe at hd0 hd1 ⊢
  obtain ⟨y0, y1, ylo, yhi⟩ := Civil.yoe_spec doe hd0 hd1
  have hlen := Civil.S_succ (Civil.yoeOf doe) y0 y1
  generalize Civil.yoeOf doe = Y at y0 y1 ylo yhi hlen ⊢
  have hS : Civil.S Y = 365 * Y + Y / 4 - Y / 100 := by unfold Civil.S; omega
  unfold Civil.doyOf
  refine ⟨hd0, hd1, y0, y1, by omega, by split at hlen <;> omega, ?_⟩
  intro h365
  split at hlen
  · assumption
  · omega

theorem doeOf_eq (z : Int) : z = (z + 719468) / 146097 * 146097 + Civil.doeOf z - 719468 := by
  unfold Civil.doeOf; omega

/-- `daysFromCivil` after `civilFromDays` is the identity on all integers. -/
theorem daysFromCivil_civilFromDays (z : Int) :
    daysFromCivil (civilFromDays z).1 (civilFromDays z).2.1 (civilFromDays z).2.2 = z := by
  have hp := civil_parts z
  have hz := doeOf_eq z
  rw [Civil.civilFromDays_eq]
  generalize (z + 719468) / 146097 = e at hz ⊢
  generalize Civil.doeOf z = doe at hp hz ⊢
  generalize Civil.yoeOf doe = Y at hp ⊢
  have hdoy : Civil.doyOf doe Y = doe - (365 * Y + Y / 4 - Y / 100) := rfl
  generalize Civil.doyOf doe Y = doy at hp hdoy ⊢
  obtain ⟨hd0, hd1, y0, y1, dy0, dy1, _⟩ := hp
  have hm := Civil.month_spec doy dy0 dy1
  generalize (5 * doy + 2) / 153 = mp at hm ⊢
  obtain ⟨m0, m1, md1, _, _⟩ := hm
  subst hz
  have hE : (Y + e * 400) / 400 = e := by omega
  have hE1 : (Y + e * 400 + 1 - 1) / 400 = e := by omega
  have hY400 : Y / 400 = 0 := by omega
  have hY4 : (Y + e * 400 - (Y + e * 400) / 400 * 400) = Y := by omega
  simp only [Civil.fromParts, daysFromCivil]
  interval_cases mp <;> simp <;> simp only [hE, Int.add_sub_cancel] <;> omega

/-- A day number converts to a valid date. -/
theorem validYMD_civilFromDays (z : Int) :
    validYMD (civilFromDays z).1 (civilFromDays z).2.1 (civilFromDays z).2.2 = true := by
  have hp := civil_parts z
  rw [Civil.civilFromDays_eq]
  generalize (z + 719468) / 146097 = e
  generalize Civil.doeOf z = doe at hp ⊢
  generalize Civil.yoeOf doe = Y at hp ⊢
  generalize Civil.doyOf doe Y = doy at hp ⊢
  obtain ⟨hd0, hd1, y0, y1, dy0, dy1, hleap⟩ := hp
  have hm := Civil.month_spec doy dy0 dy1
  generalize (5 * doy + 2) / 153 = mp at hm ⊢
  obtain ⟨m0, m1, md1, mdle, mfeb⟩ := hm
  simp only [Civil.fromParts]
  generalize hd : doy - (153 * mp + 2) / 5 + 1 = d at md1 mdle mfeb ⊢
  simp only [validYMD, Bool.and_eq_true, decide_eq_true_eq]
  interval_cases mp <;> simp [Civil.monthLen] at mdle <;> simp [daysInMonth] <;> try omega
  -- February (mp = 11): day 29 only in leap years
  have hd' := mfeb rfl
  split
  · omega
  · rename_i hnl
    by_contra hc
    have h365 : doy = 365 := by omega
    apply hnl
    rw [isLeap_iff]
    obtain ⟨a, b⟩ := hleap h365
    refine ⟨by omega, ?_⟩
    rcases b with b | b
    · left; omega
    · right; omega

/-- `civilFromDays` after `daysFromCivil` is the identity on valid dates. -/
theorem civilFromDays_daysFromCivil (y : Int) (m d : Nat) (hv : validYMD y m d = true) :
    civilFromDays (daysFromCivil y m d) = (y, m, d) := by
  simp only [validYMD, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨hm1, hm12⟩, hd1⟩, hdim⟩ := hv
  -- the month index and its length
  have hmp0 : 0 ≤ (if m > 2 then (m : Int) - 3 else (m : Int) + 9) := by split <;> omega
  have hmp1 : (if m > 2 then (m : Int) - 3 else (m : Int) + 9) ≤ 11 := by split <;> omega
  have hdlen : (d : Int) ≤ Civil.monthLen (if m > 2 then (m : Int) - 3 else (m : Int) + 9) := by
    have : m ≤ 12 := hm12
    interval_cases m <;> simp [daysInMonth] at hdim <;> simp [Civil.monthLen] <;>
      (try split at hdim) <;> omega
  -- February 29 only in leap years
  have hfeb : m = 2 → d = 29 → (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)) := by
    intro hm2 hd29
    subst hm2 hd29
    simp [daysInMonth] at hdim
    split at hdim
    · rename_i hl
      exact (isLeap_iff y).mp hl
    · omega
  rw [Civil.daysFromCivil_eq]
  generalize hy'def : (if m ≤ 2 then y - 1 else y) = y'
  generalize hmp : (if m > 2 then (m : Int) - 3 else (m : Int) + 9) = mp at hmp0 hmp1 hdlen ⊢
  have hmback : (if mp < 10 then mp + 3 else mp - 9) = (m : Int) := by
    rw [← hmp]; split_ifs <;> omega
  have hyback : (if (if mp < 10 then mp + 3 else mp - 9) ≤ 2 then y' + 1 else y') = y := by
    rw [hmback, ← hy'def]; split_ifs <;> omega
  have hfeb' : mp = 11 → (d : Int) = 29 → (y' + 1) % 4 = 0 ∧ ((y' + 1) % 100 ≠ 0 ∨ (y' + 1) % 400 = 0) := by
    intro h11 h29
    have hm2 : m = 2 := by rw [← hmp] at h11; split at h11 <;> omega
    have hy'' : y' = y - 1 := by rw [← hy'def]; simp [hm2]
    obtain ⟨a, b⟩ := hfeb hm2 (by omega)
    refine ⟨by omega, ?_⟩
    rcases b with b | b
    · left; omega
    · right; omega
  have hmi := Civil.month_inv mp d hmp0 hmp1 (by omega) hdlen
  have hyoe0 : 0 ≤ y' - y' / 400 * 400 := by omega
  have hyoe1 : y' - y' / 400 * 400 < 400 := by omega
  have hlen := Civil.S_succ _ hyoe0 hyoe1
  have hle : (153 * mp + 2) / 5 + (d : Int) - 1 ≤ 365 := by
    have := hdlen
    interval_cases mp <;> simp [Civil.monthLen] at this <;> omega
  have hdoy0 : 0 ≤ (153 * mp + 2) / 5 + (d : Int) - 1 := by omega
  -- the day lies inside its era-year
  have hdoy1 : (153 * mp + 2) / 5 + (d : Int) - 1 <
      Civil.S (y' - y' / 400 * 400 + 1) - Civil.S (y' - y' / 400 * 400) := by
    rw [hlen]
    split
    · omega
    · rename_i hn
      by_contra hc
      have hmp11 : mp = 11 := by
        by_contra hne
        have := hdlen
        interval_cases mp <;> simp [Civil.monthLen] at this <;> omega
      have hd29 : (d : Int) = 29 := by subst hmp11; omega
      obtain ⟨a, b⟩ := hfeb' hmp11 hd29
      apply hn
      refine ⟨by omega, ?_⟩
      rcases b with b | b
      · left; omega
      · right; omega
  generalize hera : y' / 400 = era at hyoe0 hyoe1 hlen hdoy1
  generalize hyoe : y' - era * 400 = yoe at hyoe0 hyoe1 hlen hdoy1
  have hS : Civil.S yoe = 365 * yoe + yoe / 4 - yoe / 100 := by unfold Civil.S; omega
  have hS400 : Civil.S (yoe + 1) ≤ 146097 := by
    have := Civil.S_mono_le (show 0 ≤ yoe + 1 by omega) (show yoe + 1 ≤ 400 by omega)
    have h400 : Civil.S 400 = 146097 := by decide
    omega
  generalize hdoy : (153 * mp + 2) / 5 + (d : Int) - 1 = doy at hle hdoy0 hdoy1
  obtain ⟨doe, hdoe⟩ : ∃ doe, doe = yoe * 365 + yoe / 4 - yoe / 100 + doy := ⟨_, rfl⟩
  have hdoe0 : 0 ≤ doe := by omega
  have hdoe1 : doe < 146097 := by omega
  have hyoeOf : Civil.yoeOf doe = yoe :=
    Civil.yoe_unique doe yoe hdoe0 hdoe1 hyoe0 hyoe1 (by omega) (by omega)
  have hnum : Civil.dayNumber y' mp d = era * 146097 + doe - 719468 := by
    simp only [Civil.dayNumber]; rw [hera, hyoe, hdoy, hdoe]
  rw [Civil.civilFromDays_eq, hnum]
  have h1 : (era * 146097 + doe - 719468 + 719468) / 146097 = era := by omega
  have h2 : Civil.doeOf (era * 146097 + doe - 719468) = doe := by unfold Civil.doeOf; omega
  rw [h1, h2, hyoeOf]
  have h3 : Civil.doyOf doe yoe = doy := by unfold Civil.doyOf; omega
  rw [hdoy] at hmi
  rw [h3, hmi]
  simp only [Civil.fromParts]
  have h4 : doy - (153 * mp + 2) / 5 + 1 = (d : Int) := by omega
  rw [h4, Int.toNat_natCast]
  have hyy : yoe + era * 400 = y' := by omega
  rw [hyy, hmback, Int.toNat_natCast]
  rw [hmback] at hyback
  simp only [Prod.mk.injEq, and_true]
  exact hyback

end Tiramemsu.Codec
