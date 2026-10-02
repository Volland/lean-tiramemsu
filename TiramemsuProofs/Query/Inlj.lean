/-
Index nested-loop evaluation on the model store (nested-loop-join "Join-order independence"):
one step scans each pattern under an outer row through the key prefix of its bound positions
(or the eid lookup), and the rows it returns that are compatible with the outer row are those
of the pattern's reference bag; so the nested loop over any order of stored patterns is the
reference natural join of their bags. This is the M3b contract: any planner order is correct.
All statements assume `IdBridge` on the model state.
-/
import TiramemsuProofs.Query.EvRun
import TiramemsuProofs.Query.JoinLaws
import TiramemsuProofs.Query.DenoteJoin
import TiramemsuProofs.Query.Aggregate

namespace Tiramemsu.Exec

open Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem

--# @lat: [[verification#Proven Query Semantics]]

/-! ## Decoded statement positions -/

/-- The decoded value of an id (`default` when it does not decode). -/
def dv (st : ModelState) (x : Int64) : Value :=
  match decodeId st x with
  | .ok v => v
  | .error _ => default

section
variable {st : ModelState} (hB : IdBridge st)
include hB

theorem decodeId_dv {r : TripleRow} (hr : r ∈ st.triples) {x : Int64} (hx : x ∈ stmtIds r) :
    decodeId st x = .ok (dv st x) := by
  obtain ⟨v, hv⟩ := hB.decodes r hr x hx
  unfold dv; rw [hv]

theorem lookupId_dv {r : TripleRow} (hr : r ∈ st.triples) {x : Int64} (hx : x ∈ stmtIds r) :
    lookupId st (dv st x) = some x :=
  hB.complete r hr x hx _ (decodeId_dv hB hr hx)

/-- Two statement positions with equal values are the same id. -/
theorem dv_inj {r r' : TripleRow} (hr : r ∈ st.triples) (hr' : r' ∈ st.triples) {x x' : Int64}
    (hx : x ∈ stmtIds r) (hx' : x' ∈ stmtIds r') (h : dv st x = dv st x') : x = x' := by
  have a := lookupId_dv hB hr hx
  have b := lookupId_dv hB hr' hx'
  rw [h] at a; rw [a] at b; exact Option.some.inj b

end

theorem mem_stmtIds_s (r : TripleRow) : r.s ∈ stmtIds r := by simp [stmtIds]
theorem mem_stmtIds_p (r : TripleRow) : r.p ∈ stmtIds r := by simp [stmtIds]
theorem mem_stmtIds_o (r : TripleRow) : r.o ∈ stmtIds r := by simp [stmtIds]
theorem mem_stmtIds_eid (r : TripleRow) : r.eid ∈ stmtIds r := by simp [stmtIds]

/-! ## Row cells -/

theorem get_eq_cell (r : Row) (i : Nat) : r.get i = cell r i := by
  unfold Row.get cell
  rw [List.getD_eq_getElem?_getD]
  cases r[i]? with
  | none => rfl
  | some x => cases x <;> rfl

theorem get_setAt_self (r : Row) (i : Nat) (x : Option Value) : (r.setAt i x).get i = x := by
  unfold Row.setAt Row.get
  split
  · next h => simp [h]
  · next h =>
    rw [List.getElem?_append_right (by simp; omega)]
    simp
    have : i - (r.length + (i - r.length)) = 0 := by omega
    simp [this]

theorem get_setAt_ne (r : Row) {i j : Nat} (x : Option Value) (h : j ≠ i) : (r.setAt i x).get j = r.get j := by
  unfold Row.setAt Row.get
  split
  · simp [Ne.symm h]
  · next hi =>
    by_cases hj : j < r.length
    · rw [List.append_assoc, List.getElem?_append_left hj]
    · rw [List.getElem?_eq_none (l := r) (by omega), List.append_assoc,
        List.getElem?_append_right (by omega)]
      by_cases hj2 : j - r.length < i - r.length
      · rw [List.getElem?_append_left (by simpa using hj2), List.getElem?_replicate]; simp [hj2]
      · rw [List.getElem?_append_right (by simp; omega)]
        simp only [List.length_replicate]
        rw [List.getElem?_singleton]
        have : j - r.length - (i - r.length) ≠ 0 := by omega
        simp [this]

/-- A row extends another: every bound cell is kept. -/
def Ext (row row' : Row) : Prop := ∀ i u, row.get i = some u → row'.get i = some u

theorem Ext.refl (row : Row) : Ext row row := fun _ _ h => h
theorem Ext.trans {a b c : Row} (h1 : Ext a b) (h2 : Ext b c) : Ext a c := fun i u h => h2 i u (h1 i u h)

theorem bindVal_spec {E : Env} {v : Var} {w : Value} {row row' : Row} (h : bindVal E v w row = some row') :
    Ext row row' ∧ row'.get (E.idx v) = some w := by
  unfold bindVal at h
  simp only at h
  split at h
  · next w' hw =>
    split at h
    · next he =>
      cases h
      refine ⟨Ext.refl _, ?_⟩
      rw [hw]; simp only [beq_iff_eq] at he; rw [he]
    · cases h
  · next hw =>
    cases h
    refine ⟨fun i u hi => ?_, get_setAt_self _ _ _⟩
    by_cases hii : i = E.idx v
    · subst hii; rw [hw] at hi; cases hi
    · rw [get_setAt_ne _ _ hii]; exact hi

/-- Compatible rows agree where both are bound. -/
theorem compat_get {m : Missing} {P Q : Schema} {a b : Row} (h : compat m P Q a b = true) {i : Nat}
    {x y : Value} (ha : a.get i = some x) (hb : b.get i = some y) : x = y := by
  have := (compat_iff.1 h) i
  rw [get_eq_cell] at ha hb
  rw [ha, hb] at this
  simpa [cellCompat] using this

/-! ## Matching one position -/

/-- The pure match of a pattern position against a decoded stored position. -/
def mpos (E : Env) (t : TermOrVar) (w : Value) (x : Int64) (row : Row) : Option Row :=
  match t with
  | .var v => bindVal E v w row
  | .const c => if w == c.canonical then some row else none
  | .id o => if o.raw == x then some row else none
  | .param _ => none

theorem ev_bindE (st : ModelState) (E : Env) (t : TermOrVar) {x : Int64} {w : Value}
    (hx : decodeId st x = .ok w) (row : Row) :
    ev st (bindE E t x row) = .ok (.ok (mpos E t w x row)) := by
  cases t with
  | var v => unfold bindE; rw [ev_bind, ev_decodeE st hx]; rfl
  | const c => unfold bindE; rw [ev_bind, ev_decodeE st hx]; rfl
  | id o => rfl
  | param _ => rfl

theorem matchPos_eq (st : ModelState) (E : Env) (t : TermOrVar) {x : Int64} {w : Value}
    (hx : decodeId st x = .ok w) (row : Row) :
    matchPos (E.at st) t x row = .ok (mpos E t w x row) := by
  cases t with
  | var v => simp only [matchPos, Env.at, hx]; rfl
  | const c => simp only [matchPos, Env.at, hx]; rfl
  | id o => rfl
  | param _ => rfl

/-! ## Index choice -/

/-- A bound position agrees with a stored id. -/
def optOk : Option Int64 → Int64 → Bool
  | none, _ => true
  | some x, y => y == x

theorem prefixOk_indexFor (v : Store.View) (s p o : Option Int64) (r : TripleRow) :
    (scanSpec (indexFor s p o).1 v (indexFor s p o).2).prefixOk r =
      (optOk s r.s && optOk p r.p && optOk o r.o) := by
  obtain ⟨tx, valid⟩ := v
  cases s <;> cases p <;> cases o <;> cases tx <;>
    simp [indexFor, scanSpec, ScanSpec.prefixOk, IndexOrder.family, Family.cols, Family.perm, Col.get, optOk] <;>
    simp [Bool.and_comm, Bool.and_left_comm]

theorem indexFor_length (s p o : Option Int64) : (indexFor s p o).2.length ≤ 3 := by
  cases s <;> cases p <;> cases o <;> simp [indexFor]

theorem scanList_perm (st : ModelState) (ord : IndexOrder) (v : Store.View) (pfx : List Int64) :
    (st.scanList (scanSpec ord v pfx)).Perm
      (st.triples.filter fun r => v.admits r && (scanSpec ord v pfx).prefixOk r) := by
  unfold ModelState.scanList
  refine (List.mergeSort_perm _ _).trans ?_
  rw [List.filter_congr (fun r _ => scan_matches_iff ord v pfx r)]

/-! ## Graph memberships -/

/-- The graphs of a statement as `denote` reads them, on decoded values. -/
def memList (st : ModelState) (v : Store.View) (e : Int64) : List Value :=
  ((visibleRows st v).filter (·.s == e)).filterMap fun m =>
    if dv st m.p == .iri Engine.Vocab.sysInGraph then some (dv st m.o) else none

theorem iri_inGraph_canonical : (Value.iri Engine.Vocab.sysInGraph).canonical = .iri Engine.Vocab.sysInGraph := by
  decide

theorem visible_mem {st : ModelState} {v : Store.View} {r : TripleRow} (h : r ∈ visibleRows st v) :
    r ∈ st.triples :=
  (List.mem_filter.1 h).1

section
variable {st : ModelState} (hB : IdBridge st)
include hB

theorem membershipsOf_eq (v : Store.View) (e : Int64) : membershipsOf st v e = .ok (memList st v e) := by
  unfold membershipsOf memList
  rw [show (do
      let ms ← ((visibleRows st v).filter (·.s == e)).mapM fun m => do
        if (← decodeId st m.p) == .iri Engine.Vocab.sysInGraph then
          return some (← decodeId st m.o)
        else return none
      return ms.filterMap id : Except LErr (List Value)) = _ from rfl]
  rw [mapM_ok_of _ (fun m => if dv st m.p == .iri Engine.Vocab.sysInGraph then some (dv st m.o) else none)]
  · simp [List.filterMap_map]
  · intro m hm
    have hm' := visible_mem (List.mem_filter.1 hm).1
    rw [decodeId_dv hB hm' (mem_stmtIds_p m)]
    show (if dv st m.p == _ then _ else _) = _
    split
    · rw [decodeId_dv hB hm' (mem_stmtIds_o m)]; rfl
    · rfl

omit hB in
theorem memList_eq (v : Store.View) (e : Int64) :
    memList st v e = ((st.triples.filter fun m => v.admits m && m.s == e &&
      dv st m.p == .iri Engine.Vocab.sysInGraph).map fun m => dv st m.o) := by
  unfold memList visibleRows
  rw [List.filter_filter]
  induction st.triples with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.filter_cons]
    by_cases h1 : (m.s == e && v.admits m) = true
    · simp only [h1, ite_true, List.filterMap_cons]
      have h1' : (v.admits m && m.s == e) = true := by rw [Bool.and_comm]; exact h1
      by_cases h2 : (dv st m.p == .iri Engine.Vocab.sysInGraph) = true
      · simp only [h2, h1', ite_true, Bool.and_self, List.map_cons, ih]
      · simp only [h2, h1', Bool.and_false, Bool.false_eq_true, ↓reduceIte, ih]
    · have h1' : (v.admits m && m.s == e) = false := by
        rw [Bool.and_comm]; simpa using h1
      simp only [h1, h1', Bool.false_and, Bool.false_eq_true, ↓reduceIte, ih]

theorem ev_membershipsE (v : Store.View) (e : Int64) :
    ∃ L, ev st (membershipsE v e) = .ok (.ok L) ∧ L.Perm (memList st v e) := by
  unfold membershipsE
  rw [ev_bind, ev_lookupE]
  simp only
  rw [memList_eq]
  cases hig : lookupId st (.iri Engine.Vocab.sysInGraph) with
  | none =>
    refine ⟨[], rfl, ?_⟩
    rw [List.filter_eq_nil_iff.2, List.map_nil]
    intro m hm h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have := lookupId_dv hB hm (mem_stmtIds_p m)
    rw [h.2, hig] at this; cases this
  | some ig =>
    simp only
    rw [ev_bind, ev_rangeScan st .spo v [e, ig] (by simp)]
    simp only
    have hsub : ∀ m ∈ st.scanList (scanSpec .spo v [e, ig]), m ∈ st.triples := fun m hm =>
      (mem_scanList_iff.1 hm).1
    rw [ev_mapM st (g := fun m => dv st m.o) _ (fun m hm => ev_decodeE st
      (decodeId_dv hB (hsub m hm) (mem_stmtIds_o m)))]
    refine ⟨_, rfl, ?_⟩
    refine ((scanList_perm st .spo v [e, ig]).map _).trans ?_
    rw [List.filter_congr (q := fun m => v.admits m && m.s == e &&
      dv st m.p == .iri Engine.Vocab.sysInGraph)]
    intro m hm
    have hp := prefixOk_indexFor v (some e) (some ig) none m
    simp only [indexFor] at hp
    rw [hp]
    simp only [optOk, Bool.and_true]
    by_cases hp' : m.p = ig
    · have hd := hB.sound m hm m.p (mem_stmtIds_p m) _ (hp' ▸ hig)
      rw [iri_inGraph_canonical, decodeId_dv hB hm (mem_stmtIds_p m)] at hd
      injection hd with hd
      rw [hp'] at hd
      simp [hp', hd]
    · have : (dv st m.p == .iri Engine.Vocab.sysInGraph) = false := by
        rw [beq_eq_false_iff_ne]
        intro h
        have := lookupId_dv hB hm (mem_stmtIds_p m)
        rw [h, hig] at this
        exact hp' (Option.some.inj this).symm
      simp [hp', this]

end

/-! ## The rows of one statement -/

/-- The row a statement binds before graph expansion. -/
def m0 (st : ModelState) (E : Env) (t : TriplePattern) (r : TripleRow) : Option Row :=
  (mpos E t.s (dv st r.s) r.s (Row.empty E.n)).bind fun row =>
  (mpos E t.p (dv st r.p) r.p row).bind fun row =>
  (mpos E t.o (dv st r.o) r.o row).bind fun row =>
  match t.eid with
  | some ev => bindVal E ev (dv st r.eid) row
  | none => some row

/-- The graph-selector expansion of a matched row, given the statement's graphs. -/
def gRows (E : Env) (g : GraphSel) (ms : List Value) (row : Row) : List Row :=
  match g with
  | .any => [row]
  | .set gs =>
    let want := gs.filterMap fun t => match t with | .const c => some c.canonical | _ => none
    if ms.any want.contains then [row] else []
  | .var gv => ms.filterMap fun m => bindVal E gv m row

/-- The rows one statement contributes to a stored pattern. -/
def sRows (st : ModelState) (E : Env) (v : Store.View) (t : TriplePattern) (r : TripleRow) : List Row :=
  match m0 st E t r with
  | none => []
  | some row => gRows E t.graph (memList st v r.eid) row

theorem gRows_perm (E : Env) (g : GraphSel) {ms ms' : List Value} (h : ms.Perm ms') (row : Row) :
    (gRows E g ms row).Perm (gRows E g ms' row) := by
  cases g with
  | any => exact List.Perm.refl _
  | set gs =>
    simp only [gRows]
    have : ms.any (fun m => (gs.filterMap fun t => match t with | .const c => some c.canonical | _ => none).contains m) =
        ms'.any (fun m => (gs.filterMap fun t => match t with | .const c => some c.canonical | _ => none).contains m) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      exact ⟨fun ⟨x, hx, h2⟩ => ⟨x, h.subset hx, h2⟩, fun ⟨x, hx, h2⟩ => ⟨x, h.symm.subset hx, h2⟩⟩
    rw [this]
  | var gv => exact h.filterMap _

/-! ## What a pattern row records -/

/-- What a row of a pattern records about one stored position (`w` its value, `y` its id). -/
def PosFact (E : Env) (tv : TermOrVar) (w : Value) (y : Int64) (x : Row) : Prop :=
  match tv with
  | .var v => x.get (E.idx v) = some w
  | .const c => w = c.canonical
  | .id o => y = o.raw
  | .param _ => False

theorem mpos_spec {E : Env} {tv : TermOrVar} {w : Value} {y : Int64} {row row' : Row}
    (h : mpos E tv w y row = some row') : Ext row row' ∧ ∀ x, Ext row' x → PosFact E tv w y x := by
  cases tv with
  | var v =>
    obtain ⟨h1, h2⟩ := bindVal_spec h
    exact ⟨h1, fun x hx => hx _ _ h2⟩
  | const c =>
    simp only [mpos] at h
    split at h
    · next he => cases h; exact ⟨Ext.refl _, fun _ _ => by simp only [PosFact]; simpa using he⟩
    · cases h
  | id o =>
    simp only [mpos] at h
    split at h
    · next he => cases h; exact ⟨Ext.refl _, fun _ _ => by simp only [PosFact]; exact (by simpa using he : o.raw = y).symm⟩
    · cases h
  | param _ => cases h

theorem gRows_ext {E : Env} {g : GraphSel} {ms : List Value} {row x : Row} (h : x ∈ gRows E g ms row) :
    Ext row x := by
  cases g with
  | any => simp [gRows] at h; subst h; exact Ext.refl _
  | set gs =>
    simp only [gRows] at h
    split at h
    · simp at h; subst h; exact Ext.refl _
    · cases h
  | var gv =>
    simp only [gRows, List.mem_filterMap] at h
    obtain ⟨_, _, hb⟩ := h
    exact (bindVal_spec hb).1

/-- The facts a pattern row records about its statement. -/
theorem sRows_pos {st : ModelState} {E : Env} {v : Store.View} {t : TriplePattern} {r : TripleRow} {x : Row}
    (h : x ∈ sRows st E v t r) :
    PosFact E t.s (dv st r.s) r.s x ∧ PosFact E t.p (dv st r.p) r.p x ∧ PosFact E t.o (dv st r.o) r.o x ∧
      ∀ ev, t.eid = some ev → x.get (E.idx ev) = some (dv st r.eid) := by
  unfold sRows m0 at h
  cases h1 : mpos E t.s (dv st r.s) r.s (Row.empty E.n) with
  | none => rw [h1] at h; cases h
  | some row1 =>
    rw [h1] at h
    simp only [Option.bind] at h
    cases h2 : mpos E t.p (dv st r.p) r.p row1 with
    | none => rw [h2] at h; cases h
    | some row2 =>
      rw [h2] at h
      simp only at h
      cases h3 : mpos E t.o (dv st r.o) r.o row2 with
      | none => rw [h3] at h; cases h
      | some row3 =>
        rw [h3] at h
        simp only at h
        obtain ⟨e1, f1⟩ := mpos_spec h1
        obtain ⟨e2, f2⟩ := mpos_spec h2
        obtain ⟨e3, f3⟩ := mpos_spec h3
        have key : ∀ row4, Ext row3 row4 → x ∈ gRows E t.graph (memList st v r.eid) row4 →
            PosFact E t.s (dv st r.s) r.s x ∧ PosFact E t.p (dv st r.p) r.p x ∧ PosFact E t.o (dv st r.o) r.o x := by
          intro row4 e4 hx
          have e := Ext.trans e4 (gRows_ext hx)
          exact ⟨f1 x (Ext.trans e2 (Ext.trans e3 e)), f2 x (Ext.trans e3 e), f3 x e⟩
        cases he : t.eid with
        | none =>
          rw [he] at h
          exact ⟨(key row3 (Ext.refl _) h).1, (key row3 (Ext.refl _) h).2.1, (key row3 (Ext.refl _) h).2.2,
            fun ev hev => by cases hev⟩
        | some ev =>
          rw [he] at h
          simp only at h
          cases h4 : bindVal E ev (dv st r.eid) row3 with
          | none => rw [h4] at h; cases h
          | some row4 =>
            rw [h4] at h
            obtain ⟨e4, g4⟩ := bindVal_spec h4
            obtain ⟨k1, k2, k3⟩ := key row4 e4 h
            refine ⟨k1, k2, k3, fun ev' hev => ?_⟩
            cases hev
            exact gRows_ext h _ _ g4

/-- Without an eid variable and graph selector, a statement's rows depend only on its content. -/
theorem sRows_congr {st : ModelState} {E : Env} {v : Store.View} {t : TriplePattern} (he : t.eid = none)
    (hg : t.graph = .any) {r r' : TripleRow} (h : spo r = spo r') : sRows st E v t r = sRows st E v t r' := by
  simp only [spo, Prod.mk.injEq] at h
  obtain ⟨hs, hp, ho⟩ := h
  unfold sRows m0
  rw [he, hg, hs, hp, ho]
  simp [gRows]

section
variable {st : ModelState} (hB : IdBridge st)
include hB

theorem posFact_inj {E : Env} {tv : TermOrVar} {r r' : TripleRow} (hr : r ∈ st.triples) (hr' : r' ∈ st.triples)
    {y y' : Int64} (hy : y ∈ stmtIds r) (hy' : y' ∈ stmtIds r') {x : Row}
    (h : PosFact E tv (dv st y) y x) (h' : PosFact E tv (dv st y') y' x) : y = y' := by
  cases tv with
  | var v => simp only [PosFact] at h h'; rw [h] at h'; exact dv_inj hB hr hr' hy hy' (Option.some.inj h')
  | const c => simp only [PosFact] at h h'; exact dv_inj hB hr hr' hy hy' (h.trans h'.symm)
  | id o => simp only [PosFact] at h h'; exact h.trans h'.symm
  | param _ => cases h

/-- A row of two statements of a stored pattern determines their content. -/
theorem sRows_inj {E : Env} {v : Store.View} {t : TriplePattern} {r r' : TripleRow}
    (hr : r ∈ st.triples) (hr' : r' ∈ st.triples) {x : Row} (h : x ∈ sRows st E v t r)
    (h' : x ∈ sRows st E v t r') : spo r = spo r' := by
  obtain ⟨a1, a2, a3, -⟩ := sRows_pos h
  obtain ⟨b1, b2, b3, -⟩ := sRows_pos h'
  simp only [spo]
  rw [posFact_inj hB hr hr' (mem_stmtIds_s r) (mem_stmtIds_s r') a1 b1,
    posFact_inj hB hr hr' (mem_stmtIds_p r) (mem_stmtIds_p r') a2 b2,
    posFact_inj hB hr hr' (mem_stmtIds_o r) (mem_stmtIds_o r') a3 b3]

theorem storedRows_eq (E : Env) (v : Store.View) (t : TriplePattern) {r : TripleRow} (hr : r ∈ st.triples) :
    storedRows (E.at st) v t r = .ok (sRows st E v t r) := by
  unfold storedRows sRows m0
  simp only [bindOpt, Env.at_n]
  rw [matchPos_eq st E t.s (decodeId_dv hB hr (mem_stmtIds_s r))]
  simp only [bind, Except.bind]
  cases mpos E t.s (dv st r.s) r.s (Row.empty E.n) with
  | none => rfl
  | some row1 =>
    simp only [Option.bind]
    rw [matchPos_eq st E t.p (decodeId_dv hB hr (mem_stmtIds_p r))]
    cases mpos E t.p (dv st r.p) r.p row1 with
    | none => rfl
    | some row2 =>
      simp only
      rw [matchPos_eq st E t.o (decodeId_dv hB hr (mem_stmtIds_o r))]
      cases mpos E t.o (dv st r.o) r.o row2 with
      | none => rfl
      | some row3 =>
        simp only
        have hgr : ∀ row, graphRows (E.at st) v t.graph r.eid row = .ok (gRows E t.graph (memList st v r.eid) row) := by
          intro row
          cases hg : t.graph with
          | any => rfl
          | set gs =>
            simp only [graphRows, Env.at_st, membershipsOf_eq hB, gRows, bind, Except.bind]; rfl
          | var gv =>
            simp only [graphRows, Env.at_st, membershipsOf_eq hB, gRows, bind, Except.bind]; rfl
        cases t.eid with
        | none => exact hgr row3
        | some ev =>
          simp only [Env.at_st, decodeId_dv hB hr (mem_stmtIds_eid r)]
          show (match bindVal (E.at st) ev (dv st r.eid) row3 with
            | none => pure [] | some row => graphRows (E.at st) v t.graph r.eid row : Except LErr (List Row)) = _
          rw [bindVal_at]
          cases bindVal E ev (dv st r.eid) row3 with
          | none => rfl
          | some row4 => exact hgr row4

theorem ev_patRowsOf (E : Env) (v : Store.View) (t : TriplePattern) {r : TripleRow} (hr : r ∈ st.triples) :
    ∃ L, ev st (patRowsOf E v t r) = .ok (.ok L) ∧ L.Perm (sRows st E v t r) := by
  unfold patRowsOf sRows m0
  rw [ev_bind, ev_bindE st E t.s (decodeId_dv hB hr (mem_stmtIds_s r))]
  cases mpos E t.s (dv st r.s) r.s (Row.empty E.n) with
  | none => exact ⟨[], rfl, List.Perm.refl _⟩
  | some row1 =>
    simp only [Option.bind]
    rw [ev_bind, ev_bindE st E t.p (decodeId_dv hB hr (mem_stmtIds_p r))]
    cases mpos E t.p (dv st r.p) r.p row1 with
    | none => exact ⟨[], rfl, List.Perm.refl _⟩
    | some row2 =>
      simp only
      rw [ev_bind, ev_bindE st E t.o (decodeId_dv hB hr (mem_stmtIds_o r))]
      cases mpos E t.o (dv st r.o) r.o row2 with
      | none => exact ⟨[], rfl, List.Perm.refl _⟩
      | some row3 =>
        simp only
        have hg : ∀ row, ∃ L, ev st (match t.graph with
            | .any => (pure [row] : EvM (List Row))
            | .set gs => do
              let ms ← membershipsE v r.eid
              pure (if ms.any (gs.filterMap fun g => match g with | .const c => some c.canonical | _ => none).contains
                then [row] else [])
            | .var gv => do
              let ms ← membershipsE v r.eid
              pure (ms.filterMap fun m => bindVal E gv m row)) = .ok (.ok L) ∧
            L.Perm (gRows E t.graph (memList st v r.eid) row) := by
          intro row
          obtain ⟨L, hL, hp⟩ := ev_membershipsE hB v r.eid
          cases hgr : t.graph with
          | any => exact ⟨_, rfl, List.Perm.refl _⟩
          | set gs =>
            refine ⟨_, by rw [ev_bind, hL]; rfl, ?_⟩
            exact gRows_perm E (.set gs) hp row
          | var gv =>
            refine ⟨_, by rw [ev_bind, hL]; rfl, ?_⟩
            exact gRows_perm E (.var gv) hp row
        cases t.eid with
        | none =>
          rw [ev_bind]
          exact hg row3
        | some ev' =>
          rw [ev_bind, ev_decodeE st (decodeId_dv hB hr (mem_stmtIds_eid r))]
          simp only
          rw [ev_bind, ev_pure]
          simp only
          cases bindVal E ev' (dv st r.eid) row3 with
          | none => exact ⟨[], rfl, List.Perm.refl _⟩
          | some row4 => exact hg row4

/-- The bag of a stored pattern on the model, on decoded values. -/
def tpBag (st : ModelState) (E : Env) (t : TriplePattern) : Bag :=
  let v := resolveView st t.view
  let bag := (visibleRows st v).flatMap (sRows st E v t)
  if E.sem.graphSet == .setOfTriples && t.eid.isNone then bag.eraseDups else bag

theorem triplePat_eq (E : Env) {t : TriplePattern} (ht : t.p.virtual? = none) :
    triplePat (E.at st) t = .ok (tpBag st E t) := by
  unfold triplePat tpBag collectRows
  simp only [ht, Env.at_st, Env.at_sem]
  rw [mapM_ok_of _ (sRows st E (resolveView st t.view) t) _
    (fun r hr => storedRows_eq hB E _ t (visible_mem hr))]
  simp [List.flatMap]

end

/-! ## List facts -/

theorem mem_of_mem_dedupAdjFrom (last : TripleRow) : ∀ (l : List TripleRow) (r : TripleRow),
    r ∈ dedupAdjFrom last l → r ∈ l
  | [], _, h => by simp [dedupAdjFrom] at h
  | b :: rest, r, h => by
    simp only [dedupAdjFrom] at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_of_mem_dedupAdjFrom last rest r h)
    · rcases List.mem_cons.1 h with h | h
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_of_mem_dedupAdjFrom b rest r h)

theorem mem_of_mem_dedupAdj {l : List TripleRow} {r : TripleRow} (h : r ∈ dedupAdj l) : r ∈ l := by
  cases l with
  | nil => simp [dedupAdj] at h
  | cons a rest =>
    simp only [dedupAdj] at h
    rcases List.mem_cons.1 h with h | h
    · exact h ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_mem_dedupAdjFrom a rest r h)

/-- Dropping inputs that contribute no kept rows. -/
theorem flatMap_filter_pred {α : Type} (S : List α) (pred : α → Bool) (f : α → List Row) (c : Row → Bool)
    (hn : ∀ r ∈ S, pred r = false → ∀ x ∈ f r, c x = false) :
    ((S.filter pred).flatMap f).filter c = (S.flatMap f).filter c := by
  induction S with
  | nil => rfl
  | cons r rs ih =>
    have ih' := ih (fun r' hr' => hn r' (List.mem_cons_of_mem _ hr'))
    by_cases hp : pred r = true
    · simp [hp, List.filter_append, ih']
    · have : (f r).filter c = [] := List.filter_eq_nil_iff.2 fun x hx => by
        simp [hn r (List.mem_cons_self ..) (by simpa using hp) x hx]
      simp [hp, List.filter_append, ih', this]

/-- Bag mode: candidates are a filter of the visible statements that loses no kept row. -/
theorem bag_mode {S C : List TripleRow} {pred : TripleRow → Bool} {f g : TripleRow → List Row}
    {c : Row → Bool} (hC : C.Perm (S.filter pred)) (hn : ∀ r ∈ S, pred r = false → ∀ x ∈ f r, c x = false)
    (hg : ∀ r ∈ C, (g r).Perm (f r)) :
    ((C.flatMap g).filter c).Perm ((S.flatMap f).filter c) := by
  rw [← flatMap_filter_pred S pred f c hn]
  exact (((flatMap_perm_congr hg).trans (hC.flatMap_right f))).filter c

/-- Set mode: a duplicate-free list with the kept rows of `R` is the deduplicated `R`, filtered. -/
theorem set_mode {L R : List Row} {c : Row → Bool} (hL : L.Nodup) (hmem : ∀ x, c x = true → (x ∈ L ↔ x ∈ R)) :
    (L.filter c).Perm (R.eraseDups.filter c) := by
  refine (List.perm_ext_iff_of_nodup (hL.filter c) ((nodup_eraseDups R).filter c)).2 fun x => ?_
  rw [List.mem_filter, List.mem_filter, List.mem_eraseDups]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(hmem x h2).1 h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(hmem x h2).2 h1, h2⟩

theorem filter_eid_eq {l : List TripleRow} (hl : l.Pairwise fun a b => a.eid ≠ b.eid) (e : Int64) :
    l.filter (fun r => r.eid == e) = (l.find? (·.eid == e)).toList := by
  induction l with
  | nil => rfl
  | cons r rs ih =>
    rw [List.pairwise_cons] at hl
    by_cases he : (r.eid == e) = true
    · rw [List.filter_cons, ite_cond_eq_true _ _ (eq_true he), List.find?_cons, he, Option.toList_some]
      rw [List.filter_eq_nil_iff.2]
      intro x hx hxe
      exact hl.1 x hx ((beq_iff_eq.1 he).trans (beq_iff_eq.1 hxe).symm)
    · rw [List.filter_cons, ite_cond_eq_false _ _ (eq_false he), List.find?_cons, (by simpa using he : (r.eid == e) = false)]
      exact ih hl.2

/-! ## Bound positions -/

/-- A pattern position under an outer row, on the model. -/
def posIdP (st : ModelState) (E : Env) (a : Row) : TermOrVar → Option (Option Int64)
  | .var v => match a.get (E.idx v) with
    | some val => (lookupId st val).map some
    | none => some none
  | .const c => (lookupId st c.canonical).map some
  | .id o => some (some o.raw)
  | .param _ => none

theorem ev_posId (st : ModelState) (E : Env) (a : Row) (tv : TermOrVar) :
    ev st (posId E a tv) = .ok (.ok (posIdP st E a tv)) := by
  cases tv with
  | var v =>
    simp only [posId, posIdP]
    cases a.get (E.idx v) with
    | none => rfl
    | some val => simp only; rw [ev_bind, ev_lookupE]; rfl
  | const c => unfold posId posIdP; rw [ev_bind, ev_lookupE]; rfl
  | id o => rfl
  | param _ => rfl

section
variable {st : ModelState} (hB : IdBridge st)
include hB

/-- A statement position of a compatible pattern row passes its key-prefix constraint. -/
theorem posIdP_ok {E : Env} {a x : Row} {m : Missing} {P Q : Schema} (hc : compat m P Q a x = true)
    {tv : TermOrVar} {r : TripleRow} (hr : r ∈ st.triples) {y : Int64} (hy : y ∈ stmtIds r)
    (hf : PosFact E tv (dv st y) y x) : ∃ o, posIdP st E a tv = some o ∧ optOk o y = true := by
  cases tv with
  | var v =>
    simp only [PosFact] at hf
    cases ha : a.get (E.idx v) with
    | none => exact ⟨none, by simp only [posIdP, ha], rfl⟩
    | some val =>
      have := compat_get hc ha hf
      subst this
      refine ⟨some y, ?_, by simp [optOk]⟩
      simp only [posIdP, ha, lookupId_dv hB hr hy, Option.map_some]
  | const c =>
    simp only [PosFact] at hf
    refine ⟨some y, ?_, by simp [optOk]⟩
    simp only [posIdP, ← hf, lookupId_dv hB hr hy, Option.map_some]
  | id o => simp only [PosFact] at hf; exact ⟨some o.raw, rfl, by simp [optOk, hf]⟩
  | param _ => cases hf

/-- Set mode of a pattern: `SetOfTriples` without an eid variable. -/
def setMode (E : Env) (t : TriplePattern) : Bool := E.sem.graphSet == .setOfTriples && t.eid.isNone

/-- The candidates of an outer row: a filter of the visible statements (before adjacent
deduplication) that keeps every statement with a compatible row. -/
theorem ev_candidateRows (E : Env) (t : TriplePattern) (a : Row) (m : Missing) (P Q : Schema) :
    ∃ Cb : List TripleRow, ∃ pred : TripleRow → Bool,
      ev st (candidateRows E (resolveView st t.view) t a) =
        .ok (.ok (if setMode E t && t.graph == .any then dedupAdj Cb else Cb)) ∧
      Cb.Perm ((visibleRows st (resolveView st t.view)).filter pred) ∧
      (∀ r ∈ visibleRows st (resolveView st t.view), pred r = false →
        ∀ x ∈ sRows st E (resolveView st t.view) t r, compat m P Q a x = false) ∧
      (∃ f : Family, f.maxPrefix = 3 ∧ Cb.Pairwise (fun a b => keyLe f a b = true)) := by
  set v := resolveView st t.view
  unfold candidateRows
  cases hb : t.eid.bind (fun ev => a.get (E.idx ev)) with
  | some val =>
    obtain ⟨ev', he, hval⟩ : ∃ ev', t.eid = some ev' ∧ a.get (E.idx ev') = some val := by
      cases h : t.eid with
      | none => rw [h] at hb; cases hb
      | some ev' => rw [h] at hb; exact ⟨ev', rfl, hb⟩
    have hset : (setMode E t && t.graph == .any) = false := by simp [setMode, he]
    simp only [hset, Bool.false_eq_true, ↓reduceIte]
    rw [ev_bind, ev_lookupE]
    simp only
    have hn : ∀ r ∈ visibleRows st v, (lookupId st val == some r.eid) = false →
        ∀ x ∈ sRows st E v t r, compat m P Q a x = false := by
      intro r hr hp x hx
      cases hc : compat m P Q a x
      · rfl
      · have := compat_get hc hval ((sRows_pos hx).2.2.2 ev' he)
        subst this
        rw [lookupId_dv hB (visible_mem hr) (mem_stmtIds_eid r)] at hp
        simp at hp
    cases hl : lookupId st val with
    | none =>
      refine ⟨[], fun _ => false, rfl, by simp, fun r hr _ => ?_, ⟨.liveSpo, rfl, List.Pairwise.nil⟩⟩
      have := hn r hr (by simp [hl])
      exact this
    | some e =>
      simp only
      rw [ev_bind, ev_lookupEid]
      refine ⟨_, fun r => lookupId st val == some r.eid, rfl, ?_, hn, ⟨.liveSpo, rfl, ?_⟩⟩
      · rw [hl]
        unfold visibleRows ModelState.triple
        have : ∀ r : TripleRow, (some e == some r.eid) = (r.eid == e) := by
          intro r; simp [eq_comm]
        simp only [this]
        rw [List.filter_comm, filter_eid_eq hB.wf]
        cases (st.triples.find? (·.eid == e)) with
        | none => exact List.Perm.refl _
        | some r0 => by_cases ha : v.admits r0 = true <;> simp [Option.filter, ha]
      · cases (st.triple e).filter v.admits <;> simp
  | none =>
    simp only
    rw [ev_bind, ev_posId]
    -- a position that can never match empties the candidates
    have hpos : ∀ (tv : TermOrVar) (sel : TripleRow → Int64), (∀ r, sel r ∈ stmtIds r) →
        (∀ r x, x ∈ sRows st E v t r → PosFact E tv (dv st (sel r)) (sel r) x) →
        ∀ r ∈ visibleRows st v, ∀ x ∈ sRows st E v t r, compat m P Q a x = true →
          ∃ o, posIdP st E a tv = some o ∧ optOk o (sel r) = true := by
      intro tv sel hsel hfact r hr x hx hc
      exact posIdP_ok hB hc (visible_mem hr) (hsel r) (hfact r x hx)
    have hs := hpos t.s (·.s) mem_stmtIds_s (fun _ _ hx => (sRows_pos hx).1)
    have hp := hpos t.p (·.p) mem_stmtIds_p (fun _ _ hx => (sRows_pos hx).2.1)
    have ho := hpos t.o (·.o) mem_stmtIds_o (fun _ _ hx => (sRows_pos hx).2.2.1)
    have empty : ∀ (tv : TermOrVar) (sel : TripleRow → Int64), posIdP st E a tv = none →
        (∀ r ∈ visibleRows st v, ∀ x ∈ sRows st E v t r, compat m P Q a x = true →
          ∃ o, posIdP st E a tv = some o ∧ optOk o (sel r) = true) →
        ∀ r ∈ visibleRows st v, (fun _ => false) r = false → ∀ x ∈ sRows st E v t r, compat m P Q a x = false := by
      intro tv sel h0 hall r hr _ x hx
      cases hc : compat m P Q a x
      · rfl
      · obtain ⟨o, ho, -⟩ := hall r hr x hx hc
        rw [h0] at ho; cases ho
    have nil_ok : ev st (pure [] : EvM (List TripleRow)) =
        .ok (.ok (if setMode E t && t.graph == .any then dedupAdj [] else [])) := by split <;> rfl
    cases hS : posIdP st E a t.s with
    | none =>
      exact ⟨[], fun _ => false, nil_ok, by simp, empty t.s _ hS hs, ⟨.liveSpo, rfl, List.Pairwise.nil⟩⟩
    | some os =>
      simp only
      rw [ev_bind, ev_posId]
      cases hP : posIdP st E a t.p with
      | none =>
        exact ⟨[], fun _ => false, nil_ok, by simp, empty t.p _ hP hp, ⟨.liveSpo, rfl, List.Pairwise.nil⟩⟩
      | some op =>
        simp only
        rw [ev_bind, ev_posId]
        cases hO : posIdP st E a t.o with
        | none =>
          exact ⟨[], fun _ => false, nil_ok, by simp, empty t.o _ hO ho, ⟨.liveSpo, rfl, List.Pairwise.nil⟩⟩
        | some oo =>
          simp only
          rcases hI : indexFor os op oo with ⟨ord, pfx⟩
          simp only
          rw [ev_bind, ev_rangeScan st ord v pfx (by have := indexFor_length os op oo; rw [hI] at this; exact this)]
          refine ⟨st.scanList (scanSpec ord v pfx), fun r => optOk os r.s && optOk op r.p && optOk oo r.o, ?_, ?_, ?_, ?_⟩
          · rfl
          · refine (scanList_perm st ord v pfx).trans ?_
            unfold visibleRows
            rw [List.filter_filter]
            apply List.Perm.of_eq
            apply List.filter_congr
            intro r _
            have := prefixOk_indexFor v os op oo r
            rw [hI] at this
            rw [this, Bool.and_comm]
          · intro r hr hpred x hx
            cases hc : compat m P Q a x
            · rfl
            · obtain ⟨o1, e1, k1⟩ := hs r hr x hx hc
              obtain ⟨o2, e2, k2⟩ := hp r hr x hx hc
              obtain ⟨o3, e3, k3⟩ := ho r hr x hx hc
              rw [hS] at e1; rw [hP] at e2; rw [hO] at e3
              cases e1; cases e2; cases e3
              simp only [k1, k2, k3, Bool.and_self] at hpred; cases hpred
          · exact ⟨ord.family v, family_max3 ord v, List.pairwise_mergeSort (keyLe_trans _) (keyLe_total _) _⟩

/-- The evaluator's rows of one statement, as a function. -/
def gOf (st : ModelState) (E : Env) (v : Store.View) (t : TriplePattern) (r : TripleRow) : List Row :=
  match ev st (patRowsOf E v t r) with
  | .ok (.ok L) => L
  | _ => []

theorem gOf_spec (E : Env) (v : Store.View) (t : TriplePattern) {r : TripleRow} (hr : r ∈ st.triples) :
    ev st (patRowsOf E v t r) = .ok (.ok (gOf st E v t r)) ∧ (gOf st E v t r).Perm (sRows st E v t r) := by
  obtain ⟨L, hL, hp⟩ := ev_patRowsOf hB E v t hr
  unfold gOf; rw [hL]; exact ⟨rfl, hp⟩

/-- index-nested-loop step: the rows of a stored pattern under an outer row, restricted to the
rows compatible with it, are those of the reference bag of the pattern. -/
theorem patternRows_step (E : Env) (t : TriplePattern) (a : Row) (m : Missing) (P Q : Schema) :
    ∃ PR, ev st (patternRows E (resolveView st t.view) t a) = .ok (.ok PR) ∧
      (PR.filter (compat m P Q a)).Perm ((tpBag st E t).filter (compat m P Q a)) := by
  set v := resolveView st t.view with hv
  set S := visibleRows st v with hS
  obtain ⟨Cb, pred, hev, hperm, hn, f, hf3, hsorted⟩ := ev_candidateRows hB E t a m P Q
  have hCbS : ∀ r ∈ Cb, r ∈ S := fun r hr => (List.mem_filter.1 (hperm.subset hr)).1
  have hCbT : ∀ r ∈ Cb, r ∈ st.triples := fun r hr => visible_mem (hCbS r hr)
  -- kept rows come from candidates
  have hback : ∀ r ∈ S, ∀ x ∈ sRows st E v t r, compat m P Q a x = true → r ∈ Cb := by
    intro r hr x hx hc
    cases hp : pred r
    · rw [hn r hr hp x hx] at hc; cases hc
    · exact hperm.symm.subset (List.mem_filter.2 ⟨hr, hp⟩)
  unfold patternRows
  rw [ev_bind, hev]
  simp only
  set C := (if setMode E t && t.graph == .any then dedupAdj Cb else Cb) with hC
  have hCT : ∀ r ∈ C, r ∈ st.triples := by
    intro r hr
    rw [hC] at hr
    split at hr
    · exact hCbT r (mem_of_mem_dedupAdj hr)
    · exact hCbT r hr
  rw [ev_bind, ev_mapM st (g := gOf st E v t) C (fun r hr => (gOf_spec hB E v t (hCT r hr)).1)]
  refine ⟨_, rfl, ?_⟩
  simp only [← List.flatMap_def]
  unfold tpBag
  simp only [← hS]
  have hgp : ∀ r ∈ Cb, (gOf st E v t r).Perm (sRows st E v t r) := fun r hr => (gOf_spec hB E v t (hCbT r hr)).2
  -- the kept rows of the candidates are the kept rows of the visible statements
  have hmemCb : ∀ x, compat m P Q a x = true → (x ∈ Cb.flatMap (gOf st E v t) ↔ x ∈ S.flatMap (sRows st E v t)) := by
    intro x hc
    simp only [List.mem_flatMap]
    constructor
    · rintro ⟨r, hr, hx⟩; exact ⟨r, hCbS r hr, (hgp r hr).subset hx⟩
    · rintro ⟨r, hr, hx⟩
      have hrc := hback r hr x hx hc
      exact ⟨r, hrc, (hgp r hrc).symm.subset hx⟩
  by_cases hset : setMode E t = true
  · have hset' : (E.sem.graphSet == .setOfTriples && t.eid.isNone) = true := hset
    rw [if_pos hset']
    by_cases hg : t.graph = .any
    · have hif : (setMode E t && t.graph == .any) = true := by simp [hset, hg]
      have hif2 : (E.sem.graphSet == .setOfTriples && t.eid.isNone && t.graph != .any) = false := by simp [hg]
      rw [hif2]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hC, if_pos hif]
      obtain ⟨hnd, hmemd⟩ := dedupAdj_spec hf3 Cb hsorted
      have he : t.eid = none := by
        simp only [setMode, Bool.and_eq_true, Option.isNone_iff_eq_none] at hset; exact hset.2
      apply set_mode
      · rw [List.nodup_flatMap]
        constructor
        · intro r hr
          refine ((hgp r (mem_of_mem_dedupAdj hr)).nodup_iff).2 ?_
          unfold sRows
          split
          · exact List.nodup_nil
          · rw [hg]; exact List.nodup_singleton _
        · have hpw := hnd
          rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hpw
          refine hpw.imp_of_mem fun {r r'} hr hr' hne => ?_
          intro x hx hx'
          have h1 := mem_of_mem_dedupAdj hr
          have h2 := mem_of_mem_dedupAdj hr'
          exact hne (sRows_inj hB (hCbT r h1) (hCbT r' h2) ((hgp r h1).subset hx) ((hgp r' h2).subset hx'))
      · intro x hc
        rw [← hmemCb x hc]
        simp only [List.mem_flatMap]
        constructor
        · rintro ⟨r, hr, hx⟩; exact ⟨r, mem_of_mem_dedupAdj hr, hx⟩
        · rintro ⟨r, hr, hx⟩
          have : spo r ∈ (dedupAdj Cb).map spo := (hmemd _).2 (List.mem_map_of_mem hr)
          obtain ⟨r', hr', hrr⟩ := List.mem_map.1 this
          refine ⟨r', hr', ?_⟩
          have hx' := (hgp r hr).subset hx
          rw [← sRows_congr he hg hrr] at hx'
          exact (hgp r' (mem_of_mem_dedupAdj hr')).symm.subset hx'
    · have hif : (setMode E t && t.graph == .any) = false := by simp [hg]
      have hif2 : (E.sem.graphSet == .setOfTriples && t.eid.isNone && t.graph != .any) = true := by
        simp [hg, hset']
      rw [hif2, if_pos rfl, hC, if_neg (by simp [hif])]
      apply set_mode (nodup_eraseDups _)
      intro x hc
      rw [List.mem_eraseDups]
      exact hmemCb x hc
  · have hsetf : setMode E t = false := by simpa using hset
    have hset' : (E.sem.graphSet == .setOfTriples && t.eid.isNone) = false := hsetf
    have hif : (setMode E t && t.graph == .any) = false := by simp [hsetf]
    rw [hset']
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [hC, if_neg (by simp [hif])]
    exact bag_mode hperm hn hgp

/-- The evaluator's pattern rows of an outer row, as a function. -/
def prOf (st : ModelState) (E : Env) (t : TriplePattern) (a : Row) : List Row :=
  match ev st (patternRows E (resolveView st t.view) t a) with
  | .ok (.ok L) => L
  | _ => []

/-- One index nested-loop step is the bag join of the outer rows with the pattern's bag. -/
theorem ev_inljStep (E : Env) (P Q : Schema) (t : TriplePattern) (xs : Bag) :
    ∃ R, ev st (inljStep E P Q (resolveView st t.view) t xs) = .ok (.ok R) ∧
      R.Perm (joinB E.sem.missing P Q xs (tpBag st E t)) := by
  unfold inljStep
  have hstep : ∀ a, ev st (patternRows E (resolveView st t.view) t a) = .ok (.ok (prOf st E t a)) ∧
      ((prOf st E t a).filter (compat E.sem.missing P Q a)).Perm
        ((tpBag st E t).filter (compat E.sem.missing P Q a)) := by
    intro a
    obtain ⟨PR, h1, h2⟩ := patternRows_step hB E t a E.sem.missing P Q
    unfold prOf; rw [h1]; exact ⟨rfl, h2⟩
  rw [ev_bind, ev_mapM st (g := fun a => ((prOf st E t a).filter (compat E.sem.missing P Q a)).map (merge a)) xs
    (fun a _ => by rw [ev_bind, (hstep a).1]; rfl)]
  refine ⟨_, rfl, ?_⟩
  rw [← List.flatMap_def, joinB]
  refine flatMap_perm_congr fun a _ => ?_
  rw [filterMap_eq_flatMap]
  refine ((hstep a).2.map (merge a)).trans (List.Perm.of_eq ?_)
  induction tpBag st E t with
  | nil => rfl
  | cons b bs ih =>
    by_cases hc : compat E.sem.missing P Q a b = true <;> simp [List.filter_cons, hc, ih]

/-- The index nested loop over an order of stored patterns, without pushed conjuncts, is the
left fold of bag joins of the patterns' reference bags in that order. -/
theorem ev_inljGo_nil (E : Env) :
    ∀ (order : List (Nat × TriplePattern)) (P : Schema) (rows rows' : Bag) (bound : List Nat),
      rows.Perm rows' →
      ∃ P' R, ev st (inljRun.go E P rows bound [] order) = .ok (.ok (P', R, [])) ∧
        SRel (P', R) ((order.map fun t => (E.schemaOf (.triple t.2), tpBag st E t.2)).foldl
          (joinSB E.sem.missing) (P, rows'))
  | [], P, rows, rows', _, h => ⟨P, rows, rfl, rfl, h⟩
  | (i, t) :: rest, P, rows, rows', bound, h => by
    unfold inljRun.go
    rw [ev_bind, ev_resolveViewE]
    simp only
    obtain ⟨R1, hR1, hp1⟩ := ev_inljStep hB E P (E.schemaOf (.triple t)) t rows
    rw [ev_bind, hR1]
    simp only [List.map_cons, List.foldl_cons]
    exact ev_inljGo_nil E rest _ R1 _ _ (hp1.trans (joinB_perm_left _ h))

/-- nested-loop-join "Join-order independence" (the M3b contract): for every list of stored
triple patterns and every permutation of it, index nested-loop evaluation in that order on the
model store equals the reference natural join of the patterns' bags. -/
theorem inlj_order_independent (E : Env) {ts ts' : List (Nat × TriplePattern)} (hp : ts.Perm ts') :
    ∃ P R, ev st (inljRun E [] [[]] ts' []) = .ok (.ok (P, R, [])) ∧
      SRel (P, R) (joinAll E.sem.missing E.n (ts.map fun t => (E.schemaOf (.triple t.2), tpBag st E t.2))) := by
  obtain ⟨P, R, h1, h2⟩ := ev_inljGo_nil hB E ts' [] [[]] [[]] [] (List.Perm.refl _)
  refine ⟨P, R, h1, h2.trans ?_⟩
  exact (joinAll_perm E.sem.missing E.n (hp.map _)).symm

/-- A stored pattern's reference bag is `tpBag`. -/
theorem denote_triple_eq (E : Env) (pb : PathSem) {t : TriplePattern} (ht : t.p.virtual? = none) {b : Bag}
    (h : denote (E.at st) pb (.triple t) = .ok b) : b = tpBag st E t := by
  simp only [denote] at h
  cases hc : checkOp (.triple t) with
  | error e => rw [hc] at h; cases h
  | ok u =>
    rw [hc] at h
    simp only [bind, Except.bind, triplePat_eq hB E ht, liftL] at h
    cases h; rfl

/-- nested-loop-join "Join-order independence", against the reference semantics: whenever the
reference bag of `Join` over stored patterns exists, index nested-loop evaluation in any order
of the patterns yields it (after the relationship-isomorphism filter `denote` applies). -/
theorem inlj_eq_denote (E : Env) (pb : PathSem) {ts ts' : List (Nat × TriplePattern)} (hp : ts.Perm ts')
    (hs : ∀ t ∈ ts, t.2.p.virtual? = none) {b : Bag}
    (hd : denote (E.at st) pb (.join (ts.map fun t => .triple t.2)) = .ok b) :
    ∃ P R, ev st (inljRun E [] [[]] ts' []) = .ok (.ok (P, R, [])) ∧ (isoFilter E.iso R).Perm b := by
  obtain ⟨P, R, h1, h2⟩ := inlj_order_independent hB E hp
  refine ⟨P, R, h1, ?_⟩
  have hnp : ∀ x ∈ ts.map (fun t => Op.triple t.2), NoPath x := by
    intro x hx; obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx; rfl
  rw [denote_join_eq _ pb _ hnp, denoteList_eq] at hd
  cases hl : (ts.map fun t => Op.triple t.2).mapM (denote (E.at st) pb) with
  | error e => rw [hl] at hd; cases hd
  | ok bs =>
    rw [hl] at hd
    simp only [Except.map, Except.ok.injEq] at hd
    subst hd
    -- every input's bag is its `tpBag`
    have hbs : bs = ts.map fun t => tpBag st E t.2 := by
      have key : ∀ (us : List (Nat × TriplePattern)) (cs : List Bag), (∀ t ∈ us, t.2.p.virtual? = none) →
          (us.map fun t => Op.triple t.2).mapM (denote (E.at st) pb) = .ok cs → cs = us.map fun t => tpBag st E t.2 := by
        intro us
        induction us with
        | nil => intro cs _ h; simp only [List.map_nil, List.mapM_nil] at h; cases h; rfl
        | cons u us ih =>
          intro cs hv h
          simp only [List.map_cons, List.mapM_cons] at h
          cases hu : denote (E.at st) pb (.triple u.2) with
          | error e => rw [hu] at h; cases h
          | ok cu =>
            rw [hu] at h
            cases hus : (us.map fun t => Op.triple t.2).mapM (denote (E.at st) pb) with
            | error e => simp [hus, bind, Except.bind] at h
            | ok cus =>
              simp only [hus, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
              subst h
              rw [denote_triple_eq hB E pb (hv u (List.mem_cons_self ..)) hu,
                ih cus (fun t ht => hv t (List.mem_cons_of_mem _ ht)) hus]
              rfl
      exact key ts bs hs hl
    subst hbs
    have : ((ts.map fun t => Op.triple t.2).map (E.at st).schemaOf).zip (ts.map fun t => tpBag st E t.2) =
        ts.map fun t => (E.schemaOf (.triple t.2), tpBag st E t.2) := by
      clear h2 h1 hl hs hp hnp
      induction ts with
      | nil => rfl
      | cons u us ih => rw [Env.at_schemaOf] at ih; simp only [List.map_cons, List.zip_cons_cons, ih, Env.at_schemaOf]
    rw [this]
    simp only [Env.at_iso, Env.at_sem, Env.at_n]
    exact isoFilter_perm _ h2.2

end

end Tiramemsu.Exec
