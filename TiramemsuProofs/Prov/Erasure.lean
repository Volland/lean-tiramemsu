/-
query-provenance "Provenance on request": erasing the eid lists of the provenance evaluation
yields the reference bag. Leaves first (stored patterns, path patterns), then the operator tree,
mirroring the evaluator theorem (`eval_sim`); same hypotheses: the id bridge and the query
conditions `OpOk` (no stored pattern binds two eid columns of one match group).
-/
import TiramemsuProofs.Prov.Erase
import TiramemsuProofs.Query.EvalDenoteTop

namespace Tiramemsu.Prov

open Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem Tiramemsu.Exec
open Tiramemsu.Path

--# @lat: [[verification#Proven Query Semantics#Provenance Erasure]]

theorem er_filterMap_map {α : Type} (F : α → Option Row) (G : α × Int64 → List Int64) (L : List (α × Int64)) :
    er (L.filterMap fun x => (F x.1).map (·, G x)) = (L.map (·.1)).filterMap F := by
  induction L with
  | nil => rfl
  | cons x xs ih => cases h : F x.1 <;> simp [h, er] <;> simp_all [er]

theorem any_map_fst {α β : Type} (p : α → Bool) (L : List (α × β)) :
    (L.map (·.1)).any p = !(L.filter fun x => p x.1).isEmpty := by
  induction L with
  | nil => rfl
  | cons x xs ih => by_cases h : p x.1 <;> simp [h, ih]

/-- An optional annotated bag against an optional reference bag: both absent, or erasing to a
permutation. -/
def ORel : Option ABag → Option Bag → Prop
  | none, none => True
  | some ab, some b => (er ab).Perm b
  | _, _ => False

theorem others_rel (f : IR.Op → Schema) : ∀ (xs : List IR.Op) (ebs : List (Option ABag)) (dbs : List (Option Bag)),
    List.Forall₂ ORel ebs dbs →
    List.Forall₂ SRel (((xs.zip ebs).filterMap fun p => p.2.map (f p.1, ·)).map fun q => (q.1, er q.2))
      ((xs.zip dbs).filterMap fun p => p.2.map (f p.1, ·))
  | [], _, _, _ => by simp
  | _ :: _, [], [], _ => by simp
  | x :: xs, e :: es, d :: ds, .cons h hs => by
    have ih := others_rel f xs es ds hs
    cases e <;> cases d <;> simp only [ORel] at h
    · simpa using ih
    · simp only [List.zip_cons_cons, List.filterMap_cons, Option.map_some, List.map_cons]
      exact .cons ⟨rfl, h⟩ ih

theorem foldl_rel (m : Missing) : ∀ {xs ys : List SBag}, List.Forall₂ SRel xs ys →
    ∀ {a a' : SBag}, SRel a a' → SRel (xs.foldl (joinSB m) a) (ys.foldl (joinSB m) a')
  | [], [], .nil, _, _, h => h
  | _ :: _, _ :: _, .cons hx hs, _, a', h =>
    foldl_rel m hs ((joinSB_congr m _ h).trans (joinSB_congr_right m a' hx))

theorem joinAll_rel (m : Missing) (n : Nat) {xs ys : List SBag} (h : List.Forall₂ SRel xs ys) :
    SRel (joinAll m n xs) (joinAll m n ys) := foldl_rel m h (SRel.refl _)

theorem flatten_er_perm : ∀ {xss : List ABag} {yss : List Bag}, List.Forall₂ (fun ab b => (er ab).Perm b) xss yss →
    (er xss.flatten).Perm yss.flatten
  | [], [], .nil => List.Perm.refl _
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.flatten_cons, er_append]; exact h.append (flatten_er_perm hs)

theorem filterMap_ite {α β : Type} (c : α → Bool) (f : α → β) (L : List α) :
    (L.filterMap fun b => if c b then some (f b) else none) = (L.filter c).map f := by
  induction L with
  | nil => rfl
  | cons x xs ih => by_cases h : c x <;> simp [h, ih]

theorem ev_mapM_ok {α β : Type} {st : ModelState} (f : α → EvM β) :
    ∀ (xs : List α), (∀ x ∈ xs, ∃ y, ev st (f x) = .ok (.ok y)) → ∃ ys, ev st (xs.mapM f) = .ok (.ok ys)
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x (List.mem_cons_self ..)
    obtain ⟨ys, hys⟩ := ev_mapM_ok f xs (fun z hz => h z (List.mem_cons_of_mem _ hz))
    rw [List.mapM_cons, ev_bind, hy]
    simp only []
    rw [ev_bind, hys]
    exact ⟨_, rfl⟩

theorem ev_mapM_fst {α : Type} {st : ModelState} (f : α → EvM ARow) (key : α → Row) :
    ∀ (xs : List α), (∀ x ∈ xs, ∃ es, ev st (f x) = .ok (.ok (key x, es))) →
      ∃ ab, ev st (xs.mapM f) = .ok (.ok ab) ∧ er ab = xs.map key
  | [], _ => ⟨[], rfl, rfl⟩
  | x :: xs, h => by
    obtain ⟨es, hy⟩ := h x (List.mem_cons_self ..)
    obtain ⟨ab, hab, her⟩ := ev_mapM_fst f key xs (fun z hz => h z (List.mem_cons_of_mem _ hz))
    rw [List.mapM_cons, ev_bind, hy]
    simp only []
    rw [ev_bind, hab]
    exact ⟨_, rfl, by simp [er] at her ⊢; exact her⟩

section
variable {st : ModelState} (hB : IdBridge st)
include hB

/-- The memberships with their eids erase to the memberships of the evaluator. -/
theorem ev_membershipsProv (v : Store.View) (e : Int64) :
    ∃ L, ev st (membershipsProv v e) = .ok (.ok L) ∧ ev st (membershipsE v e) = .ok (.ok (L.map (·.1))) := by
  unfold membershipsProv membershipsE
  rw [ev_bind, ev_bind, ev_lookupE]
  cases hig : lookupId st (.iri Engine.Vocab.sysInGraph) with
  | none => exact ⟨[], rfl, rfl⟩
  | some ig =>
    simp only []
    rw [ev_bind, ev_bind, ev_rangeScan st .spo v [e, ig] (by simp)]
    simp only []
    have hsub : ∀ m ∈ st.scanList (scanSpec .spo v [e, ig]), m ∈ st.triples := fun m hm =>
      (mem_scanList_iff.1 hm).1
    rw [ev_mapM st (g := fun m => (dv st m.o, m.eid)) _ (fun m hm => by
      rw [ev_bind, ev_decodeE st (decodeId_dv hB (hsub m hm) (mem_stmtIds_o m))]; rfl)]
    rw [ev_mapM st (g := fun m => dv st m.o) _ (fun m hm => ev_decodeE st
      (decodeId_dv hB (hsub m hm) (mem_stmtIds_o m)))]
    exact ⟨_, rfl, by simp [List.map_map, Function.comp_def]⟩

/-- The annotated rows of one statement erase to the evaluator's rows of it. -/
theorem ev_patRowsProv (E : Env) (v : Store.View) (t : TriplePattern) {r : TripleRow} (hr : r ∈ st.triples) :
    ∃ A, ev st (patRowsProv E v t r) = .ok (.ok A) ∧ ev st (patRowsOf E v t r) = .ok (.ok (er A)) := by
  have hs := ev_bindE st E t.s (decodeId_dv hB hr (mem_stmtIds_s r))
  have hp := ev_bindE st E t.p (decodeId_dv hB hr (mem_stmtIds_p r))
  have ho := ev_bindE st E t.o (decodeId_dv hB hr (mem_stmtIds_o r))
  have he := ev_decodeE st (decodeId_dv hB hr (mem_stmtIds_eid r))
  obtain ⟨L, hL1, hL2⟩ := ev_membershipsProv hB v r.eid
  unfold patRowsProv patRowsOf
  simp only [ev_bind, hs]
  cases mpos E t.s (dv st r.s) r.s (Row.empty E.n) with
  | none => exact ⟨[], rfl, rfl⟩
  | some row1 =>
    simp only [ev_bind, hp]
    cases mpos E t.p (dv st r.p) r.p row1 with
    | none => exact ⟨[], rfl, rfl⟩
    | some row2 =>
      simp only [ev_bind, ho]
      cases mpos E t.o (dv st r.o) r.o row2 with
      | none => exact ⟨[], rfl, rfl⟩
      | some row3 =>
        simp only []
        cases t.eid with
        | none =>
          simp only [ev_bind, ev_pure]
          cases t.graph with
          | any => exact ⟨_, rfl, rfl⟩
          | set gs =>
            simp only [ev_bind, hL1, hL2, any_map_fst]
            split
            · next hm => exact ⟨[], rfl, by erw [hm]; rfl⟩
            · next hm => exact ⟨_, rfl, by erw [Bool.of_not_eq_true hm]; rfl⟩
          | var gv =>
            simp only [ev_bind, hL1, hL2]
            exact ⟨_, rfl, by rw [← er_filterMap_map]; rfl⟩
        | some ev' =>
          simp only [ev_bind, he, ev_pure]
          cases bindVal E ev' (dv st r.eid) row3 with
          | none => exact ⟨[], rfl, rfl⟩
          | some row4 =>
            simp only []
            cases t.graph with
            | any => exact ⟨_, rfl, rfl⟩
            | set gs =>
              simp only [ev_bind, hL1, hL2, any_map_fst]
              split
              · next hm => exact ⟨[], rfl, by erw [hm]; rfl⟩
              · next hm => exact ⟨_, rfl, by erw [Bool.of_not_eq_true hm]; rfl⟩
            | var gv =>
              simp only [ev_bind, hL1, hL2]
              exact ⟨_, rfl, by rw [← er_filterMap_map]; rfl⟩

/-- The annotated rows of one statement, as a function. -/
def aOf (st : ModelState) (E : Env) (v : Store.View) (t : TriplePattern) (r : TripleRow) : ABag :=
  match ev st (patRowsProv E v t r) with
  | .ok (.ok A) => A
  | _ => []

theorem aOf_spec (E : Env) (v : Store.View) (t : TriplePattern) {r : TripleRow} (hr : r ∈ st.triples) :
    ev st (patRowsProv E v t r) = .ok (.ok (aOf st E v t r)) ∧ er (aOf st E v t r) = gOf st E v t r := by
  obtain ⟨A, h1, h2⟩ := ev_patRowsProv hB E v t hr
  unfold aOf gOf
  rw [h1, h2]
  exact ⟨rfl, rfl⟩

/-- A stored pattern's annotated bag erases to its reference bag. -/
theorem ev_triplePatProv (E : Env) (t : TriplePattern) :
    ∃ ab, ev st (triplePatProv E t) = .ok (.ok ab) ∧ (er ab).Perm (tpBag st E t) := by
  set v := resolveView st t.view with hv
  obtain ⟨Cb, pred, hev, hperm, hn, -⟩ := ev_candidateScan hB E t [] E.sem.missing [] (E.schemaOf (.triple t))
  have hCbT : ∀ r ∈ Cb, r ∈ st.triples := fun r hr => visible_mem (List.mem_filter.1 (hperm.subset hr)).1
  unfold triplePatProv
  rw [ev_bind, ev_resolveViewE]
  simp only []
  rw [ev_bind, hev]
  simp only []
  rw [ev_bind, ev_mapM st (g := aOf st E v t) Cb (fun r hr => (aOf_spec hB E v t (hCbT r hr)).1)]
  simp only []
  -- the erased annotated rows are the evaluator's rows of the candidates
  have her : er (Cb.map (aOf st E v t)).flatten = Cb.flatMap (gOf st E v t) := by
    rw [er_flatten, List.map_map, List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro r hr
    exact (aOf_spec hB E v t (hCbT r hr)).2
  have hbag : (Cb.flatMap (gOf st E v t)).Perm ((visibleRows st v).flatMap (sRows st E v t)) := by
    have := bag_mode (c := compat E.sem.missing [] (E.schemaOf (.triple t)) []) hperm hn
      (fun r hr => (gOf_spec hB E v t (hCbT r hr)).2)
    rwa [List.filter_eq_self.2 (fun x _ => compat_unit_left _ _ x),
      List.filter_eq_self.2 (fun x _ => compat_unit_left _ _ x)] at this
  unfold tpBag
  rw [← hv]
  by_cases hs : (E.sem.graphSet == .setOfTriples && t.eid.isNone) = true
  · simp only [hs, ite_true]
    refine ⟨_, rfl, ?_⟩
    rw [er_map_snd (fun kg => kg.1) (fun kg => unionCites kg.2)]
    have := congrArg (List.map Prod.fst) (groupCites_er (fun r : Row => r) (Cb.map (aOf st E v t)).flatten)
    simp only [List.map_map, Function.comp_def, List.map_id'] at this
    rw [this, her]
    exact eraseDups_perm hbag
  · simp only [hs, Bool.false_eq_true, ite_false]
    exact ⟨_, rfl, her ▸ hbag⟩

theorem ev_hopMemberships (v : Store.View) (gs : List Int64) (hops : List Hop) :
    ∃ ms, ev st (hopMemberships v gs hops) = .ok (.ok ms) := by
  unfold hopMemberships
  obtain ⟨per, hper⟩ := ev_mapM_ok (st := st) (fun h : Hop => do
      let ms ← membershipsProv v h.eid
      let ok ← ms.mapM fun (g, me) => do
        return if gs.contains ((← lookupE g).getD 0) then some me else none
      return ok.filterMap id) hops (fun h _ => by
    obtain ⟨L, hL, -⟩ := ev_membershipsProv hB v h.eid
    rw [ev_bind, hL]
    simp only []
    obtain ⟨oks, hoks⟩ := ev_mapM_ok (st := st) (fun (gm : Value × Int64) => do
        return if gs.contains ((← lookupE gm.1).getD 0) then some gm.2 else none) L (fun gm _ => by
      rw [ev_bind, ev_lookupE]; exact ⟨_, rfl⟩)
    rw [ev_bind, hoks]
    exact ⟨_, rfl⟩)
  rw [ev_bind, hper]
  exact ⟨_, rfl⟩

/-- A path pattern's annotated rows erase to the engine's pattern rows. -/
theorem ev_pathProv (opts : PathOpts) (E : Env) (p : PathPattern) (a : Row) {ws : List WRow}
    (hw : ev st (evalPathW opts E p a) = .ok (.ok ws)) :
    ∃ ab, ev st (pathProv opts E p a) = .ok (.ok ab) ∧ er ab = ws.map (·.1) := by
  unfold pathProv
  rw [ev_bind, hw]
  simp only []
  rw [ev_bind, ev_resolveViewE]
  simp only []
  apply ev_mapM_fst _ (·.1) ws
  intro w _
  obtain ⟨row, hops, graphs⟩ := w
  simp only []
  by_cases hr : (p.mode == .reach) = true
  · simp only [hr, ite_true]; exact ⟨_, rfl⟩
  · simp only [hr, Bool.false_eq_true, ite_false]
    cases graphs with
    | none => exact ⟨_, rfl⟩
    | some gs =>
      simp only []
      obtain ⟨ms, hms⟩ := ev_hopMemberships hB (resolveView st p.view) gs hops
      rw [ev_bind, hms]
      exact ⟨_, rfl⟩

/-- A path pattern's annotated rows erase to the reference rows (the engine run on the model). -/
theorem ev_pathProv_denote (opts : PathOpts) (E : Env) (p : PathPattern) (a : Row) {b : Bag}
    (h : denotePath opts (E.at st) p a = .ok b) :
    ∃ ab, ev st (pathProv opts E p a) = .ok (.ok ab) ∧ (er ab).Perm b := by
  obtain ⟨b', hb', hp⟩ := pathSim_engine opts st E p a b h
  have hW : ∃ ws, ev st (evalPathW opts E p a) = .ok (.ok ws) ∧ ws.map (·.1) = b' := by
    unfold evalPath at hb'
    rw [ev_bind] at hb'
    revert hb'
    cases ev st (evalPathW opts E p a) with
    | error e => intro h; cases h
    | ok r =>
      cases r with
      | error e => intro h; cases h
      | ok ws => intro h; cases h; exact ⟨ws, rfl, rfl⟩
  obtain ⟨ws, hws, rfl⟩ := hW
  obtain ⟨ab, hab, her⟩ := ev_pathProv hB opts E p a hws
  exact ⟨ab, hab, her ▸ hp⟩

/-- One lateral step of the annotated evaluator for one annotated row, as a function. -/
def latAB (st : ModelState) (E : Env) (opts : PathOpts) (P : Schema) (p : PathPattern) (x : ARow) : ABag :=
  match ev st (pathProv opts E p x.1) with
  | .ok (.ok bs) => bs.filterMap fun y =>
      if compat E.sem.missing P (E.schemaOf (.path p)) x.1 y.1 then some (merge x.1 y.1, cite x.2 y.2) else none
  | _ => []

theorem ev_lateralAB (opts : PathOpts) (E : Env) :
    ∀ (ps : List PathPattern) (P : Schema) {rows : ABag} {rows' : Bag} {L : Bag}, (er rows).Perm rows' →
    lateralPaths (E.at st) (denotePath opts) P rows' ps = .ok L →
    ∃ ab, ev st (lateralPathsAB E opts P rows ps) = .ok (.ok ab) ∧ (er ab).Perm L
  | [], P, rows, rows', L, hr, h => by
    simp only [lateralPaths] at h; cases h
    exact ⟨rows, rfl, hr⟩
  | p :: ps, P, rows, rows', L, hr, h => by
    rw [lateralPaths_cons] at h
    cases hm : rows'.mapM (lat1 (E.at st) (denotePath opts) P p) with
    | error e => rw [hm] at h; cases h
    | ok parts' =>
      rw [hm] at h
      simp only [bind, Except.bind] at h
      have hall := mapM_ok_mem hm
      rw [mapM_ok_okv hall] at hm
      cases hm
      have hrow : ∀ x ∈ rows, ev st (do
          let bs ← pathProv opts E p x.1
          return bs.filterMap fun y => if compat E.sem.missing P (E.schemaOf (.path p)) x.1 y.1 then
            some (merge x.1 y.1, cite x.2 y.2) else none) = .ok (.ok (latAB st E opts P p x)) ∧
          (er (latAB st E opts P p x)).Perm (okv (lat1 (E.at st) (denotePath opts) P p x.1)) := by
        intro x hx
        have hx' : x.1 ∈ rows' := hr.subset (List.mem_map.2 ⟨x, hx, rfl⟩)
        obtain ⟨v, hv⟩ := hall x.1 hx'
        have hv' := hv
        unfold lat1 at hv
        cases hpb : denotePath opts (E.at st) p x.1 with
        | error e => rw [hpb] at hv; cases hv
        | ok bs =>
          rw [hpb] at hv
          simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hv
          obtain ⟨ab, hab, hper⟩ := ev_pathProv_denote hB opts E p x.1 hpb
          rw [ev_bind, hab]
          refine ⟨?_, ?_⟩
          · unfold latAB; rw [hab]; rfl
          · unfold latAB; rw [hab, okv_ok hv', ← hv]
            rw [er_filterMap (compat E.sem.missing P (E.schemaOf (.path p)) x.1) (merge x.1) (cite x.2) ab]
            rw [filterMap_ite]
            exact (hper.filter _).map _
      unfold lateralPathsAB
      rw [ev_bind, ev_mapM st (g := latAB st E opts P p) rows (fun x hx => by
        obtain ⟨a, ea⟩ := x; exact (hrow (a, ea) hx).1)]
      simp only []
      refine ev_lateralAB opts E ps _ ?_ h
      rw [er_flatten, List.map_map, ← List.flatMap_def, ← List.flatMap_def]
      refine (flatMap_perm_congr (fun x hx => (hrow x hx).2)).trans ?_
      have : rows.flatMap (fun x => okv (lat1 (E.at st) (denotePath opts) P p x.1)) =
          (er rows).flatMap (fun a => okv (lat1 (E.at st) (denotePath opts) P p a)) := by
        simp [er, List.flatMap_map]
      rw [this]
      exact hr.flatMap_right _

end

section
variable {st : ModelState} (hB : IdBridge st) (opts : PathOpts) {E : Env}
include hB

mutual

/-- query-provenance "Provenance on request" (operator tree): whenever the reference semantics
returns a bag, the provenance evaluator returns annotated rows that erase to a permutation of it. -/
theorem evalProv_erase : ∀ (op : IR.Op), OpOk E.iso E.vars op → ∀ b, denote (E.at st) (denotePath opts) op = .ok b →
    ∃ ab, ev st (evalProv E opts op) = .ok (.ok ab) ∧ (er ab).Perm b
  | .triple t, _, b, hd => by
    rw [denote.eq_1] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    have hd' := liftL_ok hd
    rw [evalProv.eq_1, hc, ev_bind_ok st (ev_liftEx_ok st u)]
    cases hv : t.p.virtual? with
    | some vp =>
      simp only []
      obtain ⟨b', h1, h2⟩ := ev_virtualPat hB E hv (checkOp_virtual hc hv) hd'
      rw [ev_bind, h1]
      exact ⟨_, rfl, by simpa [er, List.map_map, Function.comp_def] using h2⟩
    | none =>
      simp only []
      rw [triplePat_eq hB E hv] at hd'
      cases hd'
      exact ev_triplePatProv hB E t
  | .path p, _, b, hd => by
    rw [denote.eq_2] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    rw [evalProv.eq_2, hc, ev_bind_ok st (ev_liftEx_ok st u)]
    exact ev_pathProv_denote hB opts E p [] (liftL_ok hd)
  | .values vs rows, _, b, hd => by
    rw [denote.eq_3] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    have hd' := liftL_ok hd
    rw [evalProv.eq_3, hc, ev_bind_ok st (ev_liftEx_ok st u)]
    unfold valuesB at hd'
    have hall := mapM_ok_mem hd'
    rw [mapM_ok_okv hall] at hd'
    cases hd'
    have hrows : ev st (rows.mapM (valuesRowE E vs)) =
        .ok (.ok (rows.map fun a => okv (valuesRow (E.at st) vs a))) :=
      ev_mapM st _ (fun cells hcells => by
        obtain ⟨row, hrow⟩ := hall cells hcells
        rw [okv_ok hrow]; exact ev_valuesRowE E vs _ _ hrow)
    rw [ev_bind, hrows]
    exact ⟨_, rfl, by simp [er, List.map_map, Function.comp_def]⟩
  | .join xs, hok, b, hd => by
    obtain ⟨dbs, L, h1, h2, h3⟩ := denote_join_ok hd
    obtain ⟨ebs, he, hrel⟩ := evalProvInputs_erase xs hok dbs h1
    rw [evalProv.eq_4, ev_bind, he]
    simp only []
    obtain ⟨hJ1, hJ2⟩ := joinAllAB_er E.sem.missing E.n
      ((xs.zip ebs).filterMap fun p => p.2.map (E.schemaOf p.1, ·))
    have hR := joinAll_rel E.sem.missing E.n (others_rel E.schemaOf xs ebs dbs hrel)
    have hn : (E.at st).n = E.n := rfl
    simp only [Env.at_sem, Env.at_schemaOf, hn] at h2
    simp only [Env.at_iso] at h3
    have hrows : (er (joinAllAB E.sem.missing
        ((xs.zip ebs).filterMap fun p => p.2.map (E.schemaOf p.1, ·))).2).Perm
        (joinAll E.sem.missing E.n ((xs.zip dbs).filterMap fun p => p.2.map (E.schemaOf p.1, ·))).2 := by
      rw [hJ2]; exact hR.2
    rw [hJ1, hR.1]
    obtain ⟨ab, hab, hper⟩ := ev_lateralAB hB opts E _ _ hrows h2
    rw [ev_bind, hab]
    refine ⟨_, rfl, ?_⟩
    rw [isoFilterAB_er, h3]
    exact isoFilter_perm _ hper
  | .leftJoin l r c, hok, b, hd => by
    obtain ⟨hl, hr, hc⟩ := hok
    rw [denote.eq_5] at hd
    obtain ⟨lb, hlb, hd⟩ := bind_ok hd
    obtain ⟨rb, hrb, hd⟩ := bind_ok hd
    obtain ⟨c', hc', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨la, hla, hlp⟩ := evalProv_erase l hl lb hlb
    obtain ⟨ra, hra, hrp⟩ := evalProv_erase r hr rb hrb
    obtain ⟨c'', hc'', hcc⟩ := resolveOptX_sim hB (pathSim_engine opts st E) c hc c' hc'
    rw [evalProv.eq_5, ev_bind, hla]
    simp only []
    rw [ev_bind, hra]
    simp only []
    rw [ev_bind, hc'']
    refine ⟨_, rfl, ?_⟩
    rw [isoFilterAB_er, leftJoinAB_er]
    exact isoFilter_perm _ (leftJoinB_rel _ _ _ hcc hlp hrp)
  | .union xs, hok, b, hd => by
    rw [denote.eq_6] at hd
    obtain ⟨bs, hbs, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨abs, h1, h2⟩ := evalProvList_erase xs hok bs hbs
    rw [evalProv.eq_6, ev_bind, h1]
    exact ⟨_, rfl, flatten_er_perm h2⟩
  | .filter c x, hok, b, hd => by
    obtain ⟨hc, hx⟩ := hok
    rw [denote.eq_7] at hd
    obtain ⟨c', hc', hd⟩ := bind_ok hd
    obtain ⟨bx, hbx, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨c'', hc'', heq, -⟩ := resolveX_sim hB (pathSim_engine opts st E) c hc c' hc'
    obtain ⟨ab, hab, hxp⟩ := evalProv_erase x hx bx hbx
    rw [evalProv.eq_7, ev_bind, hc'']
    simp only []
    rw [ev_bind, hab]
    refine ⟨_, rfl, ?_⟩
    rw [er_filter (fun r => c''.holds r) ab]
    unfold filterB
    rw [show (fun r => c''.holds r) = c'.holds from heq.holds]
    exact hxp.filter _
  | .extend v e x, hok, b, hd => by
    obtain ⟨he, hx⟩ := hok
    rw [denote.eq_8] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    obtain ⟨e', he', hd⟩ := bind_ok hd
    obtain ⟨bx, hbx, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨e'', he'', heq, -⟩ := resolveX_sim hB (pathSim_engine opts st E) e he e' he'
    obtain ⟨ab, hab, hxp⟩ := evalProv_erase x hx bx hbx
    rw [evalProv.eq_8, hc, ev_bind_ok st (ev_liftEx_ok st u), ev_bind, he'']
    simp only []
    rw [ev_bind, hab]
    refine ⟨_, rfl, ?_⟩
    have := extendB_rel (E.idx v) heq hxp
    refine List.Perm.trans (List.Perm.of_eq ?_) this
    simp only [er, extendB, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro x _
    cases RExpr.eval x.1 e'' <;> rfl
  | .aggregate g aggs x, hok, b, hd => by
    obtain ⟨ha, hx⟩ := hok
    rw [denote.eq_9] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    obtain ⟨as', ha', hd⟩ := bind_ok hd
    obtain ⟨bx, hbx, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨as'', ha'', haeq⟩ := resolveAggsX_sim hB (pathSim_engine opts st E) aggs ha as' ha'
    obtain ⟨ab, hab, hxp⟩ := evalProv_erase x hx bx hbx
    rw [evalProv.eq_9, hc, ev_bind_ok st (ev_liftEx_ok st u), ev_bind, ha'']
    simp only []
    rw [ev_bind, hab]
    refine ⟨_, rfl, ?_⟩
    rw [aggregateAB_er, aggregateB_congr _ _ haeq]
    exact aggregateB_perm _ _ _ hxp
  | .project vs d x, hok, b, hd => by
    rw [denote.eq_10] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    obtain ⟨bx, hbx, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨ab, hab, hxp⟩ := evalProv_erase x hok bx hbx
    rw [evalProv.eq_10, hc, ev_bind_ok st (ev_liftEx_ok st u), ev_bind, hab]
    exact ⟨_, rfl, by rw [projectAB_er]; exact projectB_perm _ _ hxp⟩
  | .orderLimit keys s l x, hok, b, hd => by
    obtain ⟨hk, hx⟩ := hok
    rw [denote.eq_11] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    obtain ⟨ks', hk', hd⟩ := bind_ok hd
    obtain ⟨sk, hs, hd⟩ := bind_ok hd
    obtain ⟨lm, hl, hd⟩ := bind_ok hd
    obtain ⟨bx, hbx, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨ks'', hk'', hkeq⟩ := resolveKeysX_sim hB (pathSim_engine opts st E) keys hk ks' hk'
    obtain ⟨ab, hab, hxp⟩ := evalProv_erase x hx bx hbx
    rw [evalProv.eq_11, hc, ev_bind_ok st (ev_liftEx_ok st u), ev_bind, hk'']
    simp only []
    rw [ev_bind, hs, ev_liftEx_ok]
    simp only []
    rw [ev_bind, hl, ev_liftEx_ok]
    simp only []
    rw [ev_bind, hab]
    refine ⟨_, rfl, List.Perm.of_eq ?_⟩
    rw [orderLimitAB_er, orderLimitB_congr _ hkeq, orderLimitB_perm _ _ _ _ hxp]
    rfl

theorem evalProvList_erase : ∀ (xs : List IR.Op), OpsOk E.iso E.vars xs → ∀ bs,
    denoteList (E.at st) (denotePath opts) xs = .ok bs →
    ∃ abs, ev st (evalProvList E opts xs) = .ok (.ok abs) ∧ List.Forall₂ (fun ab b => (er ab).Perm b) abs bs
  | [], _, bs, hd => by
    simp only [denoteList] at hd; cases hd
    exact ⟨[], rfl, List.Forall₂.nil⟩
  | x :: xs, hok, bs, hd => by
    obtain ⟨hx, hxs⟩ := hok
    simp only [denoteList] at hd
    obtain ⟨b, hb, hd⟩ := bind_ok hd
    obtain ⟨bs0, hbs, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨ab, hab, hp1⟩ := evalProv_erase x hx b hb
    obtain ⟨abs, habs, hp2⟩ := evalProvList_erase xs hxs bs0 hbs
    simp only [evalProvList]
    rw [ev_bind, hab]
    simp only []
    rw [ev_bind, habs]
    exact ⟨_, rfl, List.Forall₂.cons hp1 hp2⟩

theorem evalProvInputs_erase : ∀ (xs : List IR.Op), OpsOk E.iso E.vars xs → ∀ dbs,
    denoteInputs (E.at st) (denotePath opts) xs = .ok dbs →
    ∃ ebs, ev st (evalProvInputs E opts xs) = .ok (.ok ebs) ∧ List.Forall₂ ORel ebs dbs
  | [], _, dbs, hd => by
    simp only [denoteInputs] at hd; cases hd
    exact ⟨[], rfl, List.Forall₂.nil⟩
  | x :: xs, hok, dbs, hd => by
    obtain ⟨hx, hxs⟩ := hok
    by_cases hpath : ∃ p, x = .path p
    · obtain ⟨p, rfl⟩ := hpath
      rw [denoteInputs.eq_2] at hd
      obtain ⟨u, hc, hd⟩ := bind_ok hd
      obtain ⟨ds, hds, hd⟩ := bind_ok hd
      cases hd
      obtain ⟨ebs, he, hrel⟩ := evalProvInputs_erase xs hxs ds hds
      rw [evalProvInputs.eq_2, hc, ev_bind_ok st (ev_liftEx_ok st u)]
      rw [ev_bind, he]
      exact ⟨_, rfl, .cons trivial hrel⟩
    · have hnp : ∀ p, x = .path p → False := fun p h => hpath ⟨p, h⟩
      rw [denoteInputs.eq_3 _ _ _ _ hnp] at hd
      obtain ⟨b, hb, hd⟩ := bind_ok hd
      obtain ⟨ds, hds, hd⟩ := bind_ok hd
      cases hd
      obtain ⟨ab, hab, hp⟩ := evalProv_erase x hx b hb
      obtain ⟨ebs, he, hrel⟩ := evalProvInputs_erase xs hxs ds hds
      rw [evalProvInputs.eq_3 _ _ _ _ hnp, ev_bind, hab]
      simp only []
      rw [ev_bind, he]
      exact ⟨_, rfl, .cons hp hrel⟩

end

end

/-- query-provenance "Provenance on request": for every query and every model state with the id
bridge, whenever the reference semantics returns a bag, the provenance evaluator returns rows
that, without their eid lists, are that bag (up to order). -/
theorem evalQueryProv_erase (opts : PathOpts) {st : ModelState} (hB : IdBridge st) (ps : Params) (q : Query)
    (hok : ∀ p, prepare ps q = .ok p → OpOk p.iso p.vars p.root)
    {b : Bag} (hd : Query.denote opts st ps q = .ok b) :
    ∃ p ab, prepare ps q = .ok p ∧ ev st (evalQueryProv opts ps q) = .ok (.ok (p, ab)) ∧
      (ab.map (·.1)).Perm b := by
  unfold Query.denote denoteWith at hd
  obtain ⟨p, hp, hd⟩ := bind_ok hd
  have hE : (p.env {}).at st = p.env st := rfl
  rw [← hE] at hd
  obtain ⟨ab, h1, h2⟩ := evalProv_erase hB opts p.root (hok p hp) b hd
  refine ⟨p, ab, hp, ?_, h2⟩
  unfold evalQueryProv
  rw [ev_bind, hp, ev_liftEx_ok]
  simp only []
  rw [ev_bind, h1]
  rfl

end Tiramemsu.Prov
