/-
The sorted range scans on the model store (nested-loop-join "Sorted range-scan interface" and
"Index choice"):
- a range scan returns exactly the statements visible in the view whose leading key columns
  equal the prefix, sorted by the order's key (eid last);
- a seek returns the least next-column key at or after the bound among them;
- removing consecutive equal `(s, p, o)` from a scan yields each distinct visible `(s, p, o)`
  exactly once.
-/
import Tiramemsu.Exec.Scan
import TiramemsuProofs.Store.Reads
import TiramemsuProofs.Store.Order
import TiramemsuProofs.Store.Model

namespace Tiramemsu.Exec

open Tiramemsu.Store Tiramemsu.Engine

--# @lat: [[verification#Proven Query Semantics]]

/-! ## Scans on the model -/

theorem scanSpec_valid (ord : IndexOrder) (v : Store.View) (pfx : List Int64) (h : pfx.length ≤ 3) :
    (scanSpec ord v pfx).valid = true := by
  unfold scanSpec ScanSpec.valid IndexOrder.family
  by_cases hv : v.tx = .now <;> cases ord <;> simp [hv, Family.maxPrefix, Family.isLive, h]

/-- A range scan run on a model state is the model scan. -/
theorem rangeScan_model (st : ModelState) (ord : IndexOrder) (v : Store.View) (pfx : List Int64)
    (h : pfx.length ≤ 3) :
    (rangeScan ord v pfx).onModel st = .ok (st.scanList (scanSpec ord v pfx)) := by
  unfold rangeScan RProg.onModel
  rw [RProg.runPure_bind, RProg.runPure_lift, ROp.model_scan, if_pos (scanSpec_valid ord v pfx h)]
  simp [bind, Except.bind]
  rfl

/-- The row predicate of a range scan: visible in the view and agreeing with the prefix (the
partial-index filter of a live family is implied by the `now` view). -/
theorem scan_matches_iff (ord : IndexOrder) (v : Store.View) (pfx : List Int64) (r : TripleRow) :
    (scanSpec ord v pfx).matches r = (v.admits r && (scanSpec ord v pfx).prefixOk r) := by
  obtain ⟨tx, valid⟩ := v
  cases tx <;> cases ord <;>
    simp [ScanSpec.matches, scanSpec, IndexOrder.family, Family.rowFilter, ScanSpec.boundsOk, Store.View.admits,
      TxSel.admits, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

/-- nested-loop-join: on the model store a scan returns exactly the visible statements that
match the prefix, sorted by the order's key (eid last). -/
theorem rangeScan_spec (st : ModelState) (ord : IndexOrder) (v : Store.View) (pfx : List Int64)
    (h : pfx.length ≤ 3) :
    ∃ rows, (rangeScan ord v pfx).onModel st = .ok rows ∧
      (∀ r, r ∈ rows ↔ r ∈ st.triples ∧ v.admits r = true ∧ (scanSpec ord v pfx).prefixOk r = true) ∧
      rows.Pairwise (fun a b => keyLe (ord.family v) a b = true) := by
  refine ⟨_, rangeScan_model st ord v pfx h, fun r => ?_, ?_⟩
  · rw [scanList_mem]
    unfold ScanSpec.Matches
    rw [scan_matches_iff]
    simp
  · exact List.pairwise_mergeSort (keyLe_trans _) (keyLe_total _) _

/-! ## Adjacent deduplication -/

theorem mem_dedupAdjFrom (last : TripleRow) : ∀ (l : List TripleRow) (x : Int64 × Int64 × Int64),
    x ∈ (dedupAdjFrom last l).map spo → x ∈ l.map spo
  | [], x, h => by simp [dedupAdjFrom] at h
  | b :: rest, x, h => by
    simp only [dedupAdjFrom] at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_dedupAdjFrom last rest x h)
    · simp only [List.map_cons, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (mem_dedupAdjFrom b rest x h)

theorem mem_dedupAdjFrom' (last : TripleRow) : ∀ (l : List TripleRow) (x : Int64 × Int64 × Int64),
    x ∈ l.map spo → x ∈ (dedupAdjFrom last l).map spo ∨ x = spo last
  | [], x, h => by simp at h
  | b :: rest, x, h => by
    simp only [List.map_cons, List.mem_cons] at h
    simp only [dedupAdjFrom]
    split
    · rename_i he
      rcases h with rfl | h
      · exact Or.inr (by simpa using (beq_iff_eq.1 he).symm)
      · exact mem_dedupAdjFrom' last rest x h
    · rcases h with rfl | h
      · exact Or.inl (by simp)
      · rcases mem_dedupAdjFrom' b rest x h with h' | h'
        · exact Or.inl (by simp [h'])
        · exact Or.inl (by simp [h'])

/-- Deduplication keeps exactly the contents of the scan. -/
theorem mem_dedupAdj (l : List TripleRow) (x : Int64 × Int64 × Int64) :
    x ∈ (dedupAdj l).map spo ↔ x ∈ l.map spo := by
  cases l with
  | nil => simp [dedupAdj]
  | cons a rest =>
    simp only [dedupAdj, List.map_cons, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (mem_dedupAdjFrom a rest x h)
    · rintro (h | h)
      · exact Or.inl h
      · rcases mem_dedupAdjFrom' a rest x h with h' | h'
        · exact Or.inr h'
        · exact Or.inl h'

/-- The leading three key components of a statement in a family. -/
def lead3 (f : Family) (r : TripleRow) : List (Option Int) := (keyOf f r).take 3

theorem cmpKey_append : ∀ (a b c d : List (Option Int)), a.length = c.length →
    cmpKey (a ++ b) (c ++ d) = match cmpKey a c with | .eq => cmpKey b d | o => o
  | [], b, [], d, _ => by simp [cmpKey]
  | x :: xs, b, y :: ys, d, h => by
    simp only [List.cons_append, cmpKey]
    cases cmpOpt x y with
    | eq => exact cmpKey_append xs b ys d (by simpa using h)
    | lt => rfl
    | gt => rfl

theorem keyOf_lead (f : Family) (r : TripleRow) : keyOf f r = lead3 f r ++ (keyOf f r).drop 3 := by
  simp [lead3]

theorem lead3_length (f : Family) (hf : f.maxPrefix = 3) (r : TripleRow) : (lead3 f r).length = 3 := by
  cases f <;> simp_all [lead3, keyOf, Family.cols, Family.perm, Family.maxPrefix]

/-- The non-strict key order bounds the leading components. -/
theorem lead3_le {f : Family} (hf : f.maxPrefix = 3) {a b : TripleRow} (h : keyLe f a b = true) :
    cmpKey (lead3 f a) (lead3 f b) ≠ .gt := by
  intro hg
  unfold keyLe keyCmp at h
  rw [keyOf_lead f a, keyOf_lead f b, cmpKey_append _ _ _ _ (by rw [lead3_length f hf, lead3_length f hf]), hg] at h
  simp at h

/-- In the six triple families the leading components are the content, permuted. -/
theorem lead3_spo {f : Family} (hf : f.maxPrefix = 3) {a b : TripleRow} :
    lead3 f a = lead3 f b ↔ spo a = spo b := by
  cases f <;> simp_all [lead3, keyOf, Family.cols, Family.perm, Family.maxPrefix, keyComp, Col.get, spo,
    Int64.toInt_inj] <;> tauto

theorem dedupAdjFrom_lt {f : Family} (hf : f.maxPrefix = 3) : ∀ (last : TripleRow) (l : List TripleRow),
    (last :: l).Pairwise (fun a b => keyLe f a b = true) →
    (∀ b ∈ dedupAdjFrom last l, cmpKey (lead3 f last) (lead3 f b) = .lt) ∧
      (dedupAdjFrom last l).Pairwise (fun a b => cmpKey (lead3 f a) (lead3 f b) = .lt)
  | _, [], _ => by simp [dedupAdjFrom]
  | last, b :: rest, h => by
    have hl : ∀ x ∈ b :: rest, keyLe f last x = true := (List.pairwise_cons.1 h).1
    have hrest : (b :: rest).Pairwise (fun a b => keyLe f a b = true) := (List.pairwise_cons.1 h).2
    simp only [dedupAdjFrom]
    split
    · rename_i he
      have h' : (last :: rest).Pairwise (fun a b => keyLe f a b = true) :=
        List.pairwise_cons.2 ⟨fun x hx => hl x (List.mem_cons_of_mem _ hx), (List.pairwise_cons.1 hrest).2⟩
      exact dedupAdjFrom_lt hf last rest h'
    · rename_i hne
      have ih := dedupAdjFrom_lt hf b rest hrest
      have hlb : cmpKey (lead3 f last) (lead3 f b) = .lt := by
        have hle := lead3_le hf (hl b (List.mem_cons_self ..))
        have hneq : lead3 f last ≠ lead3 f b := fun e => hne (by simpa using (lead3_spo hf).1 e)
        cases hc : cmpKey (lead3 f last) (lead3 f b)
        · rfl
        · exact absurd (cmpKey_eq_iff.1 hc) hneq
        · exact absurd hc hle
      refine ⟨fun x hx => ?_, List.pairwise_cons.2 ⟨ih.1, ih.2⟩⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hlb
      · exact cmpKey_lt_trans hlb (ih.1 x hx)

/-- nested-loop-join: removing consecutive equal `(s, p, o)` from a scan of a triple family
yields each distinct `(s, p, o)` of the scan exactly once. -/
theorem dedupAdj_spec {f : Family} (hf : f.maxPrefix = 3) (l : List TripleRow)
    (hs : l.Pairwise (fun a b => keyLe f a b = true)) :
    ((dedupAdj l).map spo).Nodup ∧ ∀ x, x ∈ (dedupAdj l).map spo ↔ x ∈ l.map spo := by
  refine ⟨?_, mem_dedupAdj l⟩
  cases l with
  | nil => simp [dedupAdj]
  | cons a rest =>
    have h := dedupAdjFrom_lt hf a rest hs
    have hp : (dedupAdj (a :: rest)).Pairwise (fun a b => cmpKey (lead3 f a) (lead3 f b) = .lt) :=
      List.pairwise_cons.2 ⟨h.1, h.2⟩
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact hp.imp fun {x y} hxy e => by
      rw [← (lead3_spo hf).2 e, cmpKey_refl] at hxy; cases hxy

theorem family_max3 (ord : IndexOrder) (v : Store.View) : (ord.family v).maxPrefix = 3 := by
  unfold IndexOrder.family; split <;> cases ord <;> rfl

/-- nested-loop-join "Index choice": on the model store, the deduplicated scan holds each
distinct visible `(s, p, o)` matching the prefix exactly once. -/
theorem dedupAdj_scan (st : ModelState) (ord : IndexOrder) (v : Store.View) (pfx : List Int64)
    (h : pfx.length ≤ 3) :
    ∃ rows, (rangeScan ord v pfx).onModel st = .ok rows ∧ ((dedupAdj rows).map spo).Nodup ∧
      ∀ x, x ∈ (dedupAdj rows).map spo ↔
        ∃ r ∈ st.triples, v.admits r = true ∧ (scanSpec ord v pfx).prefixOk r = true ∧ spo r = x := by
  obtain ⟨rows, hr, hm, hs⟩ := rangeScan_spec st ord v pfx h
  obtain ⟨hn, hmem⟩ := dedupAdj_spec (family_max3 ord v) rows hs
  refine ⟨rows, hr, hn, fun x => ?_⟩
  rw [hmem, List.mem_map]
  constructor
  · rintro ⟨r, hr', rfl⟩
    obtain ⟨a, b, c⟩ := (hm r).1 hr'
    exact ⟨r, a, b, c, rfl⟩
  · rintro ⟨r, a, b, c, rfl⟩
    exact ⟨r, (hm r).2 ⟨a, b, c⟩, rfl⟩

/-! ## Seek -/

/-- The least next-column key at or after `lo`: the head of the bounded scan. -/
theorem seek_model (st : ModelState) (ord : IndexOrder) (v : Store.View) (pfx : List Int64) (lo : Int64)
    (h : pfx.length ≤ 3) :
    (seek ord v pfx lo).onModel st =
      .ok ((st.scanList { scanSpec ord v pfx with lo := some (.incl lo) }).head?.map (nextCol ord pfx.length)) := by
  unfold seek RProg.onModel
  have hv : ({ scanSpec ord v pfx with lo := some (.incl lo) } : ScanSpec).valid = true := by
    have := scanSpec_valid ord v pfx h
    simpa [ScanSpec.valid] using this
  rw [RProg.runPure_bind, RProg.runPure_lift, ROp.model_scan, if_pos hv]
  simp [bind, Except.bind]
  rfl

/-- The rows of a bounded scan: visible, matching the prefix, next column at or after `lo`. -/
theorem bounded_matches (ord : IndexOrder) (v : Store.View) (pfx : List Int64) (lo : Int64)
    (hk : pfx.length < 3) (r : TripleRow) :
    ({ scanSpec ord v pfx with lo := some (.incl lo) } : ScanSpec).matches r =
      (v.admits r && (scanSpec ord v pfx).prefixOk r && decide (lo.toInt ≤ (nextCol ord pfx.length r).toInt)) := by
  obtain ⟨tx, valid⟩ := v
  have hk' : pfx.length = 0 ∨ pfx.length = 1 ∨ pfx.length = 2 := by omega
  rcases hk' with h0 | h1 | h2 <;>
  cases tx <;> cases ord <;>
    simp [ScanSpec.matches, scanSpec, IndexOrder.family, Family.rowFilter, ScanSpec.boundsOk, ScanSpec.boundCol,
      Store.View.admits, TxSel.admits, Bound.admitsLo, nextCol, Family.cols, Family.perm, Col.get, ScanSpec.prefixOk, *,
      Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

/-- Along a scan sorted by a triple family's key, rows agreeing on the prefix have
non-decreasing next columns. -/
theorem nextCol_mono (ord : IndexOrder) (v : Store.View) (pfx : List Int64) (hk : pfx.length < 3)
    {a b : TripleRow} (ha : (scanSpec ord v pfx).prefixOk a = true) (hb : (scanSpec ord v pfx).prefixOk b = true)
    (hle : keyLe (ord.family v) a b = true) :
    (nextCol ord pfx.length a).toInt ≤ (nextCol ord pfx.length b).toInt := by
  have hl := lead3_le (family_max3 ord v) hle
  obtain ⟨tx, valid⟩ := v
  match pfx, hk with
  | [], _ =>
    cases tx <;> cases ord <;>
      simp_all [lead3, keyOf, Family.cols, Family.perm, IndexOrder.family, keyComp, Col.get, cmpKey, cmpOpt, nextCol,
        compare, compareOfLessAndEq] <;> split_ifs at hl <;> simp_all <;> omega
  | [x], _ =>
    cases tx <;> cases ord <;>
      simp_all [lead3, keyOf, Family.cols, Family.perm, IndexOrder.family, keyComp, Col.get, cmpKey, cmpOpt, nextCol,
        ScanSpec.prefixOk, scanSpec, compare, compareOfLessAndEq] <;> split_ifs at hl <;> simp_all <;> omega
  | [x, y], _ =>
    cases tx <;> cases ord <;>
      simp_all [lead3, keyOf, Family.cols, Family.perm, IndexOrder.family, keyComp, Col.get, cmpKey, cmpOpt, nextCol,
        ScanSpec.prefixOk, scanSpec, compare, compareOfLessAndEq] <;> split_ifs at hl <;> simp_all <;> omega

/-- nested-loop-join: on the model store a seek returns the least next-column key at or after
`lo` among the visible statements matching the prefix, or nothing when there is none. -/
theorem seek_least (st : ModelState) (ord : IndexOrder) (v : Store.View) (pfx : List Int64) (lo : Int64)
    (hk : pfx.length < 3) :
    ∃ k?, (seek ord v pfx lo).onModel st = .ok k? ∧
      (∀ k, k? = some k → (∃ r ∈ st.triples, v.admits r = true ∧ (scanSpec ord v pfx).prefixOk r = true ∧
          nextCol ord pfx.length r = k) ∧ lo.toInt ≤ k.toInt) ∧
      (∀ r ∈ st.triples, v.admits r = true → (scanSpec ord v pfx).prefixOk r = true →
          lo.toInt ≤ (nextCol ord pfx.length r).toInt →
          ∃ k, k? = some k ∧ k.toInt ≤ (nextCol ord pfx.length r).toInt) := by
  refine ⟨_, seek_model st ord v pfx lo (by omega), ?_, ?_⟩
  · intro k hk'
    match hh : (st.scanList { scanSpec ord v pfx with lo := some (.incl lo) }) with
    | [] => rw [hh] at hk'; cases hk'
    | r :: rest =>
      rw [hh] at hk'
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hk'
      have hr : r ∈ st.scanList { scanSpec ord v pfx with lo := some (.incl lo) } := by rw [hh]; simp
      rw [scanList_mem] at hr
      obtain ⟨hmem, hm⟩ := hr
      unfold ScanSpec.Matches at hm
      rw [bounded_matches ord v pfx lo hk r] at hm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      exact ⟨⟨r, hmem, hm.1.1, hm.1.2, hk'⟩, hk' ▸ hm.2⟩
  · intro r hmem hadm hpre hlo
    have hr : r ∈ st.scanList { scanSpec ord v pfx with lo := some (.incl lo) } := by
      rw [scanList_mem]
      refine ⟨hmem, ?_⟩
      unfold ScanSpec.Matches
      rw [bounded_matches ord v pfx lo hk r]
      simp [hadm, hpre, hlo]
    have hs : (st.scanList { scanSpec ord v pfx with lo := some (.incl lo) }).Pairwise
        (fun a b => keyLe (ord.family v) a b = true) := List.pairwise_mergeSort (keyLe_trans _) (keyLe_total _) _
    match hh : (st.scanList { scanSpec ord v pfx with lo := some (.incl lo) }), hs, hr with
    | [], _, hr => cases hr
    | h :: rest, hs, hr =>
      refine ⟨nextCol ord pfx.length h, by simp, ?_⟩
      rcases List.mem_cons.1 hr with rfl | hr
      · exact le_refl _
      · have hh' : h ∈ st.scanList { scanSpec ord v pfx with lo := some (.incl lo) } := by rw [hh]; simp
        rw [scanList_mem] at hh'
        have hm := hh'.2
        unfold ScanSpec.Matches at hm
        rw [bounded_matches ord v pfx lo hk h] at hm
        simp only [Bool.and_eq_true] at hm
        exact nextCol_mono ord v pfx hk hm.1.2 hpre ((List.pairwise_cons.1 hs).1 r hr)

end Tiramemsu.Exec
