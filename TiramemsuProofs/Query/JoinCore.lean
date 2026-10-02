/-
The evaluator's `Join` on the model store: the hash join of the non-pattern inputs, the index
nested loop over the stored patterns in the greedy order (from rows seeded with pushed constant
equalities, applying each pushed conjunct as soon as its variables are bound) and the lateral
path patterns compute the reference join, filtered by the pushed conjuncts. Statements are in
the soundness direction: whenever the reference semantics returns a bag, the evaluator returns
a permutation of it.
-/
import TiramemsuProofs.Query.Pushdown

namespace Tiramemsu.Exec

open Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem

--# @lat: [[verification#Proven Query Semantics]]

/-! ## Lists in `Except` -/

theorem mapM_ok_mem {α β ε : Type} {f : α → Except ε β} : ∀ {l : List α} {ys : List β},
    l.mapM f = .ok ys → ∀ a ∈ l, ∃ v, f a = .ok v
  | [], _, _, a, ha => by cases ha
  | x :: xs, ys, h, a, ha => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok v =>
      cases hxs : xs.mapM f with
      | error e => simp [hx, hxs, bind, Except.bind] at h
      | ok vs =>
        rcases List.mem_cons.1 ha with rfl | ha
        · exact ⟨v, hx⟩
        · exact mapM_ok_mem hxs a ha

/-- The value of a successful result. -/
def okv {β ε : Type} [Inhabited β] (x : Except ε β) : β := match x with
  | .ok v => v
  | .error _ => default

theorem mapM_ok_okv {α β ε : Type} [Inhabited β] {f : α → Except ε β} {l : List α}
    (h : ∀ a ∈ l, ∃ v, f a = .ok v) : l.mapM f = .ok (l.map fun a => okv (f a)) :=
  mapM_ok_of f _ l fun a ha => by obtain ⟨v, hv⟩ := h a ha; rw [hv]; rfl

theorem okv_ok {β ε : Type} [Inhabited β] {x : Except ε β} {v : β} (h : x = .ok v) : okv x = v := by
  rw [h]; rfl

theorem flatMap_filter_of (rows : Bag) (g : Row → Bag) (f : Row → Bool)
    (hvf : ∀ a ∈ rows, ∀ x ∈ g a, f x = f a) : (rows.filter f).flatMap g = (rows.flatMap g).filter f := by
  induction rows with
  | nil => rfl
  | cons a as ih =>
    have ihr := ih (fun x hx => hvf x (List.mem_cons_of_mem _ hx))
    by_cases hfa : f a = true
    · rw [List.filter_cons_of_pos hfa, List.flatMap_cons, List.flatMap_cons, ihr, List.filter_append]
      congr 1
      exact (List.filter_eq_self.2 fun x hx => (hvf a (List.mem_cons_self ..) x hx).trans hfa).symm
    · have h0 : (g a).filter f = [] :=
        List.filter_eq_nil_iff.2 (fun x hx => by rw [hvf a (List.mem_cons_self ..) x hx]; simpa using hfa)
      rw [List.filter_cons_of_neg hfa, List.flatMap_cons, List.filter_append, h0, List.nil_append, ihr]

/-! ## Lateral path patterns on the reference side -/

section
variable (E : Env) (pb : PathSem)

/-- One lateral step for one row. -/
def lat1 (P : Schema) (p : PathPattern) (a : Row) : Except LErr Bag := do
  return ((← pb E p a).filter (compat E.sem.missing P (E.schemaOf (.path p)) a)).map (merge a)

theorem lateralPaths_cons (P : Schema) (rows : Bag) (p : PathPattern) (ps : List PathPattern) :
    lateralPaths E pb P rows (p :: ps) = (rows.mapM (lat1 E pb P p) >>= fun parts =>
      lateralPaths E pb (Schema.union P (E.schemaOf (.path p))) parts.flatten ps) := rfl

theorem lateral_perm : ∀ (ps : List PathPattern) (P : Schema) {rows rows' : Bag} {L' : Bag},
    rows.Perm rows' → lateralPaths E pb P rows' ps = .ok L' →
    ∃ L, lateralPaths E pb P rows ps = .ok L ∧ L.Perm L'
  | [], P, rows, rows', L', hp, h => by simp only [lateralPaths] at h ⊢; cases h; exact ⟨_, rfl, hp⟩
  | p :: ps, P, rows, rows', L', hp, h => by
    rw [lateralPaths_cons] at h ⊢
    cases hm : rows'.mapM (lat1 E pb P p) with
    | error e => rw [hm] at h; cases h
    | ok parts' =>
      rw [hm] at h
      simp only [bind, Except.bind] at h
      have hall := mapM_ok_mem hm
      have hall' : ∀ a ∈ rows, ∃ v, lat1 E pb P p a = .ok v := fun a ha => hall a (hp.subset ha)
      rw [mapM_ok_okv hall']
      rw [mapM_ok_okv hall] at hm
      cases hm
      simp only [bind, Except.bind]
      exact lateral_perm ps _ ((hp.map _).flatten) h

theorem lateral_sub : ∀ (ps : List PathPattern) (P : Schema) {rows rows' : Bag} {L' : Bag},
    (∀ r ∈ rows, r ∈ rows') → lateralPaths E pb P rows' ps = .ok L' →
    ∃ L, lateralPaths E pb P rows ps = .ok L ∧ ∀ x ∈ L, x ∈ L'
  | [], P, rows, rows', L', hp, h => by simp only [lateralPaths] at h ⊢; cases h; exact ⟨_, rfl, hp⟩
  | p :: ps, P, rows, rows', L', hp, h => by
    rw [lateralPaths_cons] at h ⊢
    cases hm : rows'.mapM (lat1 E pb P p) with
    | error e => rw [hm] at h; cases h
    | ok parts' =>
      rw [hm] at h
      simp only [bind, Except.bind] at h
      have hall := mapM_ok_mem hm
      have hall' : ∀ a ∈ rows, ∃ v, lat1 E pb P p a = .ok v := fun a ha => hall a (hp a ha)
      rw [mapM_ok_okv hall']
      rw [mapM_ok_okv hall] at hm
      cases hm
      simp only [bind, Except.bind]
      refine lateral_sub ps _ (fun x hx => ?_) h
      simp only [List.mem_flatten, List.mem_map] at hx ⊢
      obtain ⟨l, ⟨a, ha, rfl⟩, hx⟩ := hx
      exact ⟨_, ⟨a, hp a ha, rfl⟩, hx⟩

/-- A filter that reads only cells the rows bind commutes with the lateral paths. -/
theorem lateral_filter : ∀ (ps : List PathPattern) (P : Schema) {rows : Bag} {L : Bag} {is : List Nat}
    {f : Row → Bool}, (∀ r ∈ rows, Binds is r) → (∀ r, Binds is r → ∀ q, f (merge r q) = f r) →
    lateralPaths E pb P rows ps = .ok L → lateralPaths E pb P (rows.filter f) ps = .ok (L.filter f)
  | [], P, rows, L, is, f, _, _, h => by simp only [lateralPaths] at h ⊢; cases h; rfl
  | p :: ps, P, rows, L, is, f, hb, hf, h => by
    rw [lateralPaths_cons] at h ⊢
    cases hm : rows.mapM (lat1 E pb P p) with
    | error e => rw [hm] at h; cases h
    | ok parts =>
      rw [hm] at h
      simp only [bind, Except.bind] at h
      have hall := mapM_ok_mem hm
      have hall' : ∀ a ∈ rows.filter f, ∃ v, lat1 E pb P p a = .ok v :=
        fun a ha => hall a (List.mem_filter.1 ha).1
      rw [mapM_ok_okv hall']
      rw [mapM_ok_okv hall] at hm
      cases hm
      simp only [bind, Except.bind]
      have hvf : ∀ a ∈ rows, ∀ x ∈ okv (lat1 E pb P p a), f x = f a := by
        intro a ha x hx
        obtain ⟨v, hv⟩ := hall a ha
        rw [okv_ok hv] at hx
        unfold lat1 at hv
        cases hpb : pb E p a with
        | error e => rw [hpb] at hv; cases hv
        | ok bs =>
          rw [hpb] at hv
          simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hv
          subst hv
          obtain ⟨q, _, rfl⟩ := List.mem_map.1 hx
          exact hf a (hb a ha) q
      have key : ((rows.filter f).map fun a => okv (lat1 E pb P p a)).flatten =
          ((rows.map fun a => okv (lat1 E pb P p a)).flatten).filter f := by
        rw [← List.flatMap_def, ← List.flatMap_def]
        exact flatMap_filter_of _ _ _ hvf
      rw [key]
      refine lateral_filter ps _ (fun r hr => ?_) hf h
      simp only [List.mem_flatten, List.mem_map] at hr
      obtain ⟨l, ⟨a, ha, rfl⟩, hx⟩ := hr
      obtain ⟨v, hv⟩ := hall a ha
      rw [okv_ok hv] at hx
      unfold lat1 at hv
      cases hpb : pb E p a with
      | error e => rw [hpb] at hv; cases hv
      | ok bs =>
        rw [hpb] at hv
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hv
        subst hv
        obtain ⟨q, _, rfl⟩ := List.mem_map.1 hx
        exact binds_merge_left (hb a ha) q

end

/-! ## Lateral path patterns on the evaluator side -/

/-- The evaluator's path semantics agrees with the reference one on the model state, row by row
(soundness direction, as bags). -/
def PathSim (st : ModelState) (E : Env) (pathE : PathE) (pb : PathSem) : Prop :=
  ∀ p a b, pb (E.at st) p a = .ok b → ∃ b', ev st (pathE E p a) = .ok (.ok b') ∧ b'.Perm b

/-- The evaluator's step for one row and one path pattern, as a function. -/
def latE (st : ModelState) (E : Env) (pathE : PathE) (P : Schema) (p : PathPattern) (a : Row) : Bag :=
  match ev st (pathE E p a) with
  | .ok (.ok b) => (b.filter (compat E.sem.missing P (E.schemaOf (.path p)) a)).map (merge a)
  | _ => []

theorem ev_lateral {st : ModelState} {E : Env} {pathE : PathE} {pb : PathSem} (hp : PathSim st E pathE pb) :
    ∀ (ps : List PathPattern) (P : Schema) {rows rows' : Bag} {L : Bag}, rows.Perm rows' →
    lateralPaths (E.at st) pb P rows' ps = .ok L →
    ∃ L', ev st (lateralPathsE E pathE P rows ps) = .ok (.ok L') ∧ L'.Perm L
  | [], P, rows, rows', L, hr, h => by
    simp only [lateralPaths] at h; cases h
    exact ⟨rows, rfl, hr⟩
  | p :: ps, P, rows, rows', L, hr, h => by
    rw [lateralPaths_cons] at h
    cases hm : rows'.mapM (lat1 (E.at st) pb P p) with
    | error e => rw [hm] at h; cases h
    | ok parts' =>
      rw [hm] at h
      simp only [bind, Except.bind] at h
      have hall := mapM_ok_mem hm
      rw [mapM_ok_okv hall] at hm
      cases hm
      -- each row of the evaluator
      have hrow : ∀ a ∈ rows, ev st (do
          return ((← pathE E p a).filter (compat E.sem.missing P (E.schemaOf (.path p)) a)).map (merge a)) =
            .ok (.ok (latE st E pathE P p a)) ∧ (latE st E pathE P p a).Perm (okv (lat1 (E.at st) pb P p a)) := by
        intro a ha
        obtain ⟨v, hv⟩ := hall a (hr.subset ha)
        have hv' := hv
        unfold lat1 at hv
        cases hpb : pb (E.at st) p a with
        | error e => rw [hpb] at hv; cases hv
        | ok bs =>
          rw [hpb] at hv
          simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hv
          obtain ⟨b', hb', hpb'⟩ := hp p a bs hpb
          rw [ev_bind, hb']
          refine ⟨?_, ?_⟩
          · unfold latE; rw [hb']; rfl
          · unfold latE; rw [hb', okv_ok hv', ← hv]
            exact (hpb'.filter _).map _
      unfold lateralPathsE
      rw [ev_bind, ev_mapM st (g := latE st E pathE P p) rows (fun a ha => (hrow a ha).1)]
      simp only
      refine ev_lateral hp ps _ ?_ h
      rw [← List.flatMap_def, ← List.flatMap_def]
      exact (flatMap_perm_congr fun a ha => (hrow a ha).2).trans (hr.flatMap_right _)

/-! ## The hash join -/

theorem hash_idx (key : Row → List Nat) (k : List Nat) : ∀ (ys : Bag) (h : Std.HashMap (List Nat) (Array Row)),
    ((ys.foldl (fun h b => h.insert (key b) ((h.getD (key b) #[]).push b)) h).getD k #[]).toList =
      (h.getD k #[]).toList ++ ys.filter (fun b => key b == k)
  | [], h => by simp
  | y :: ys, h => by
    rw [List.foldl_cons, hash_idx key k ys, Std.HashMap.getD_insert]
    by_cases hk : (key y == k) = true
    · have : key y = k := beq_iff_eq.1 hk
      subst this
      simp [List.filter_cons]
    · simp only [hk, Bool.false_eq_true, ↓reduceIte, List.filter_cons]

theorem flatMap_filter' {α β : Type} (l : List α) (p : α → Bool) (f : α → List β) :
    (l.filter p).flatMap f = l.flatMap (fun x => if p x then f x else []) := by
  induction l with
  | nil => rfl
  | cons x xs ih => by_cases h : p x = true <;> simp [List.filter_cons, h, ih]

/-- The hash join is the bag join. -/
theorem joinHash_eq (m : Missing) (P Q : Schema) (xs ys : Bag) : joinHash m P Q xs ys = joinB m P Q xs ys := by
  unfold joinHash
  simp only []
  split
  · rfl
  · set ks := hashKeys P Q xs ys with hks
    unfold joinB
    apply flatMap_congr
    intro a ha
    rw [hash_idx, Std.HashMap.getD_empty]
    simp only [List.nil_append]
    rw [List.filter_filter, filterMap_eq_flatMap, List.map_eq_flatMap, flatMap_filter']
    apply flatMap_congr
    intro b hb
    by_cases hc : compat m P Q a b = true
    · have hkey : rowKey (ks.map b.get) = rowKey (ks.map a.get) := by
        congr 1
        apply List.map_congr_left
        intro i hi
        rw [hks] at hi
        unfold hashKeys at hi
        simp only [List.mem_filter, Bool.and_eq_true, List.all_eq_true] at hi
        obtain ⟨⟨⟨_, _⟩, hxa⟩, hyb⟩ := hi.2
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hxa a ha)
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hyb b hb)
        rw [hu, hw, compat_get hc hu hw]
      simp [hc, hkey]
    · simp [hc]

theorem joinAllHash_go (m : Missing) : ∀ (xs xs' : List SBag) (a a' : SBag), List.Forall₂ SRel xs xs' → SRel a a' →
    SRel (xs.foldl (fun (P, acc) (Q, ys) => (Schema.union P Q, joinHash m P Q acc ys)) a)
      (xs'.foldl (joinSB m) a')
  | [], [], _, _, _, h => h
  | x :: xs, x' :: xs', a, a', hf, h => by
    rw [List.forall₂_cons] at hf
    simp only [List.foldl_cons]
    apply joinAllHash_go m xs xs' _ _ hf.2
    obtain ⟨hP, hA⟩ := h
    obtain ⟨hQ, hY⟩ := hf.1
    refine ⟨by simp [joinSB, hP, hQ], ?_⟩
    simp only [joinSB, joinHash_eq, hP, hQ]
    exact (joinB_perm_left _ hA).trans (joinB_perm_right _ hY)

theorem joinAllHash_rel (m : Missing) (n : Nat) {xs xs' : List SBag} (hf : List.Forall₂ SRel xs xs') :
    SRel (joinAllHash m xs) (joinAll m n xs') :=
  joinAllHash_go m xs xs' _ _ hf (SRel.refl _)

/-! ## Seeded outer rows, as bags -/

theorem joinB_flatMap (m : Missing) (P Q : Schema) (xs ys : Bag) :
    joinB m P Q xs ys = xs.flatMap fun a => joinB m P Q [a] ys := by
  unfold joinB; simp

theorem seed_bag {m : Missing} {P Q : Schema} {J : Bag} {eqs : List (Nat × Value)} {g : Row → Bool}
    (hP : ∀ e ∈ eqs, bit P e.1 = false) (hJ : ∀ b ∈ J, ∀ e ∈ eqs, (b.get e.1).isSome)
    (hc : ∀ e ∈ eqs, ∀ r, g r = true → r.get e.1 = some e.2) (acc : Bag) :
    (joinB m P Q (acc.map fun a => eqs.foldl seedStep a) J).filter g = (joinB m P Q acc J).filter g ∧
      ∀ x ∈ joinB m P Q (acc.map fun a => eqs.foldl seedStep a) J, x ∈ joinB m P Q acc J := by
  rw [joinB_flatMap, joinB_flatMap m P Q acc]
  refine ⟨?_, ?_⟩
  · rw [List.filter_flatMap, List.filter_flatMap, List.flatMap_map]
    exact flatMap_congr fun a _ => (seed_joinB hP hJ hc a).1
  · intro x hx
    rw [List.flatMap_map] at hx
    obtain ⟨a, ha, hx⟩ := List.mem_flatMap.1 hx
    exact List.mem_flatMap.2 ⟨a, ha, (seed_joinB hP hJ hc a).2 x hx⟩

/-! ## The inputs of a join -/

theorem storedPat_some {x : IR.Op} {t : TriplePattern} (h : storedPat? x = some t) :
    x = .triple t ∧ t.p.virtual? = none := by
  cases x with
  | triple t' =>
    simp only [storedPat?] at h
    split at h
    · next hv => cases h; exact ⟨rfl, by simpa using hv⟩
    · cases h
  | _ => simp [storedPat?] at h

/-- How an input of a join is evaluated on each side: a stored pattern by the nested loop
(the reference bag is `tpBag`), a path pattern laterally, anything else by its operator. -/
def InRel (st : ModelState) (E : Env) (x : IR.Op) (eb db : Option Bag) : Prop :=
  (∃ t, storedPat? x = some t ∧ eb = none ∧ db = some (tpBag st E t)) ∨
  ((∃ p, x = .path p) ∧ eb = none ∧ db = none) ∨
  (storedPat? x = none ∧ (∀ p, x ≠ .path p) ∧ ∃ b' b, eb = some b' ∧ db = some b ∧ b'.Perm b)

section
variable (st : ModelState) (E : Env)

/-- The evaluator's non-pattern inputs. -/
def othE (ins : List (IR.Op × Option Bag × Option Bag)) : List SBag :=
  ins.filterMap fun i => if (Op.pathPat? i.1).isSome then none else i.2.1.map (E.schemaOf i.1, ·)

/-- The reference inputs. -/
def othD (ins : List (IR.Op × Option Bag × Option Bag)) : List SBag :=
  ins.filterMap fun i => i.2.2.map (E.schemaOf i.1, ·)

/-- The reference inputs that are not stored patterns. -/
def othD' (ins : List (IR.Op × Option Bag × Option Bag)) : List SBag :=
  ins.filterMap fun i => if (storedPat? i.1).isNone then i.2.2.map (E.schemaOf i.1, ·) else none

/-- The stored patterns. -/
def patL (ins : List (IR.Op × Option Bag × Option Bag)) : List TriplePattern :=
  ins.filterMap fun i => storedPat? i.1

theorem othD_perm : ∀ (ins : List (IR.Op × Option Bag × Option Bag)), (∀ i ∈ ins, InRel st E i.1 i.2.1 i.2.2) →
    (othD E ins).Perm (othD' E ins ++ (patL ins).map fun t => (E.schemaOf (.triple t), tpBag st E t))
  | [], _ => by simp [othD, othD', patL]
  | i :: is, h => by
    have ih := othD_perm is (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [othD, othD', patL, List.filterMap_cons] at ih ⊢
    rcases h i (List.mem_cons_self ..) with ⟨t, ht, _, hd⟩ | ⟨⟨p, hp⟩, _, hd⟩ | ⟨hn, _, b', b, _, hd, _⟩
    · obtain ⟨hx, _⟩ := storedPat_some ht
      simp only [hd, ht, Option.map_some, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, List.map_cons]
      rw [hx]
      exact (ih.cons _).trans List.perm_middle.symm
    · have : storedPat? i.1 = none := by rw [hp]; rfl
      simp only [hd, this, Option.map_none, Option.isNone_none, ↓reduceIte]
      exact ih
    · simp only [hd, hn, Option.map_some, Option.isNone_none, ↓reduceIte, List.cons_append]
      exact ih.cons _

theorem othE_rel : ∀ (ins : List (IR.Op × Option Bag × Option Bag)), (∀ i ∈ ins, InRel st E i.1 i.2.1 i.2.2) →
    List.Forall₂ SRel (othE E ins) (othD' E ins)
  | [], _ => by simp [othE, othD']
  | i :: is, h => by
    have ih := othE_rel is (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [othE, othD', List.filterMap_cons] at ih ⊢
    rcases h i (List.mem_cons_self ..) with ⟨t, ht, he, hd⟩ | ⟨⟨p, hp⟩, he, hd⟩ | ⟨hn, hnp, b', b, he, hd, hbb⟩
    · obtain ⟨hx, _⟩ := storedPat_some ht
      have h1 : (Op.pathPat? i.1).isSome = false := by rw [hx]; rfl
      simp only [h1, he, ht, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, Option.map_none]
      exact ih
    · have h1 : (Op.pathPat? i.1).isSome = true := by rw [hp]; rfl
      have : storedPat? i.1 = none := by rw [hp]; rfl
      simp only [h1, this, hd, Option.isNone_none, ↓reduceIte, Option.map_none]
      exact ih
    · have h1 : (Op.pathPat? i.1).isSome = false := by
        cases hpp : Op.pathPat? i.1 with
        | none => rfl
        | some p =>
          exfalso; apply hnp p
          revert hpp; cases i.1 <;> simp [Op.pathPat?]
      simp only [h1, hn, hd, he, Bool.false_eq_true, Option.isNone_none, ↓reduceIte, Option.map_some]
      exact List.Forall₂.cons ⟨rfl, hbb⟩ ih

end

theorem zipIdx_pats_snd {f : IR.Op → Option TriplePattern} : ∀ (l : List IR.Op) (n : Nat),
    ((l.zipIdx n).filterMap fun (x, i) => (f x).map (i, ·)).map (·.2) = l.filterMap f
  | [], _ => rfl
  | x :: xs, n => by
    simp only [List.zipIdx_cons, List.filterMap_cons]
    cases f x <;> simp [zipIdx_pats_snd xs (n + 1)]

theorem zipIdx_pats_fst_sub {f : IR.Op → Option TriplePattern} : ∀ (l : List IR.Op) (n : Nat),
    (((l.zipIdx n).filterMap fun (x, i) => (f x).map (i, ·)).map (·.1)).Sublist (List.range' n l.length)
  | [], _ => by simp
  | x :: xs, n => by
    simp only [List.zipIdx_cons, List.filterMap_cons, List.length_cons, List.range'_succ]
    cases f x with
    | none => exact (zipIdx_pats_fst_sub xs (n + 1)).cons _
    | some t => simpa using (zipIdx_pats_fst_sub xs (n + 1)).cons_cons n

theorem pats_nodup (l : List IR.Op) :
    (((l.zipIdx.filterMap fun (x, i) => (storedPat? x).map (i, ·))).map (·.1)).Nodup :=
  (zipIdx_pats_fst_sub l 0).nodup (List.nodup_range' ..)

/-! ## Folds of patterns -/

theorem patFold_schema (st : ModelState) (E : Env) : ∀ (order : List (Nat × TriplePattern)) (P : Schema) (r r' : Bag),
    (patFold st E order (P, r)).1 = (patFold st E order (P, r')).1
  | [], _, _, _ => rfl
  | t :: ts, P, r, r' => patFold_schema st E ts _ _ _

theorem patFold_congr (st : ModelState) (E : Env) (order : List (Nat × TriplePattern)) {a a' : SBag} (h : SRel a a') :
    SRel (patFold st E order a) (patFold st E order a') := foldl_congr _ _ h

theorem patFold_perm (st : ModelState) (E : Env) {o o' : List (Nat × TriplePattern)} (h : o.Perm o') (a : SBag) :
    SRel (patFold st E o a) (patFold st E o' a) := foldl_perm _ (h.map _) a

theorem orderVars_mem_perm {E : Env} {o o' : List (Nat × TriplePattern)} (h : o.Perm o') {i : Nat} :
    i ∈ orderVars E o ↔ i ∈ orderVars E o' := by
  unfold orderVars; exact (h.flatMap_right _).mem_iff

/-- The cell-equality predicate of seeded constants. -/
def eqHold (eqs : List (Nat × Value)) (r : Row) : Bool := eqs.all fun e => r.get e.1 == some e.2

theorem eqHold_merge {eqs : List (Nat × Value)} {r : Row} (hb : ∀ e ∈ eqs, (r.get e.1).isSome) (q : Row) :
    eqHold eqs (merge r q) = eqHold eqs r := by
  unfold eqHold
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  have key : ∀ e ∈ eqs, (merge r q).get e.1 = r.get e.1 := by
    intro e he
    rw [get_merge]
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hb e he)
    rw [hu]; rfl
  exact ⟨fun H e he => key e he ▸ H e he, fun H e he => (key e he).symm ▸ H e he⟩

/-! ## The evaluator's join -/

/-- The seeded constant equalities of a join (as `seedEqs` computes them). -/
def seedList (P : Schema) (patVars : List Nat) (conds : List Pushed) : List (Nat × Value) :=
  conds.filterMap fun c => (prefixEq? c.cond).filter fun (i, _) => patVars.contains i && !(P.getD i false)

theorem seedEqs_eq (P : Schema) (patVars : List Nat) (conds : List Pushed) (rows : Bag) :
    seedEqs P patVars conds rows = rows.map fun a => (seedList P patVars conds).foldl seedStep a := rfl

theorem othE_eq (E : Env) (ins : List (IR.Op × Option Bag × Option Bag)) :
    List.filterMap (fun x => joinCore.match_4 (fun _ => Option SBag) x fun x b =>
        joinCore.match_1 (fun _ => Option SBag) x (fun _ => none) fun _ => Option.map (fun bag => (E.schemaOf x, bag)) b)
      ((ins.map (·.1)).zip (ins.map (·.2.1))) = othE E ins := by
  rw [List.zip_map', List.filterMap_map]
  unfold othE
  apply List.filterMap_congr
  intro i _
  obtain ⟨x, eb, db⟩ := i
  cases x <;> rfl

theorem othD_eq (E : Env) (ins : List (IR.Op × Option Bag × Option Bag)) :
    List.filterMap (fun x : IR.Op × Option Bag => Option.map (fun b => (E.schemaOf x.1, b)) x.2)
      ((ins.map (·.1)).zip (ins.map (·.2.2))) = othD E ins := by
  rw [List.zip_map', List.filterMap_map]; rfl

section
variable {st : ModelState} (hB : IdBridge st)
include hB

/-- The evaluator's `Join` equals the reference join, filtered by the pushed conjuncts (whose
constant equalities have identity value equality), whenever the reference join exists. -/
theorem ev_joinCore {E : Env} {pathE : PathE} {pb : PathSem} (hp : PathSim st E pathE pb)
    (ins : List (IR.Op × Option Bag × Option Bag)) (hrel : ∀ i ∈ ins, InRel st E i.1 i.2.1 i.2.2)
    (conds : List Pushed) (hok : ∀ c ∈ conds, PushedOk c)
    (hid : ∀ c ∈ conds, ∀ i k, prefixEq? c.cond = some (i, k) → IdEq k) {L : Bag}
    (hL : lateralPaths (E.at st) pb (joinAll E.sem.missing E.n (othD E ins)).1
      (joinAll E.sem.missing E.n (othD E ins)).2 ((ins.map (·.1)).filterMap Op.pathPat?) = .ok L) :
    ∃ R, ev st (joinCore E pathE (ins.map (·.1)) (ins.map (·.2.1)) conds) = .ok (.ok R) ∧
      R.Perm (isoFilter E.iso (L.filter (allHold conds))) := by
  set m := E.sem.missing
  set n := E.n
  set patsI := ((ins.map (·.1)).zipIdx.filterMap fun (x, i) => (storedPat? x).map (i, ·)) with hpatsI
  have hpI : patsI.map (fun t => (E.schemaOf (.triple t.2), tpBag st E t.2)) =
      (patL ins).map fun t => (E.schemaOf (.triple t), tpBag st E t) := by
    have h1 : patsI.map (·.2) = patL ins := by
      rw [hpatsI, zipIdx_pats_snd]; simp [patL, List.filterMap_map]
    rw [← h1, List.map_map]; rfl
  have hnd : (patsI.map (·.1)).Nodup := pats_nodup _
  -- the reference join is the pattern fold from the reference non-pattern join
  have hJ1 : SRel (joinAll m n (othD E ins)) (patFold st E patsI (joinAll m n (othD' E ins))) := by
    refine (joinAll_perm m n (othD_perm st E ins hrel)).trans ?_
    unfold joinAll patFold; rw [List.foldl_append, hpI]; exact SRel.refl _
  have hH := joinAllHash_rel m n (othE_rel st E ins hrel)
  -- evaluator side
  unfold joinCore
  simp only []
  rw [othE_eq]
  rcases hHe : joinAllHash m (othE E ins) with ⟨P0, acc⟩
  rw [hHe] at hH
  simp only []
  generalize hb0 : (List.filterMap _ _).flatten ++ _ = b0
  set patVars := patsI.flatMap fun x => x.2.vars.map E.idx with hpv
  set eqs := seedList P0 patVars conds with heqs
  rw [seedEqs_eq]
  set order := greedyOrder b0 patsI E.predCount
  have hord : order.Perm patsI := greedyOrder_perm _ _ _ hnd
  set accS := acc.map fun a => eqs.foldl seedStep a
  obtain ⟨P1, R1, applied, later, hev, hpl, hP1, hR1, happ⟩ :=
    ev_inljGo hB E order P0 accS accS [] conds (List.Perm.refl _) (fun _ _ _ h => by cases h) hok
  -- the pattern join and the folds from the plain and the seeded rows
  set J' := joinAll m n (patsI.map fun t => (E.schemaOf (.triple t.2), tpBag st E t.2))
  have hfrom : ∀ Z, SRel (patFold st E patsI (P0, Z)) (joinSB m (P0, Z) J') := fun Z =>
    foldl_from m n _ (P0, Z)
  set X := (patFold st E patsI (P0, accS)).2
  set Y := (patFold st E patsI (P0, acc)).2
  set Ps := (patFold st E patsI (P0, acc)).1
  have hbindJ : ∀ b ∈ J'.2, Binds (orderVars E patsI) b := fun b hb =>
    by simpa using patFold_binds st E patsI [] [[]] [] (fun _ _ _ h => by cases h) b hb
  have hbindY : ∀ r ∈ Y, Binds (orderVars E patsI) r := fun r hr =>
    by simpa using patFold_binds st E patsI P0 acc [] (fun _ _ _ h => by cases h) r hr
  have hbindX : ∀ r ∈ X, Binds (orderVars E patsI) r := fun r hr =>
    by simpa using patFold_binds st E patsI P0 accS [] (fun _ _ _ h => by cases h) r hr
  -- the seeded equalities
  have heqs_mem : ∀ e ∈ eqs, (∃ c ∈ conds, prefixEq? c.cond = some e) ∧ e.1 ∈ patVars ∧ bit P0 e.1 = false := by
    intro e he
    rw [heqs] at he
    unfold seedList at he
    obtain ⟨c, hc, hce⟩ := List.mem_filterMap.1 he
    cases hpe : prefixEq? c.cond with
    | none => rw [hpe] at hce; cases hce
    | some e' =>
      rw [hpe] at hce
      simp only [Option.filter, Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hce
      split at hce
      · next hh =>
        cases hce
        exact ⟨⟨c, hc, hpe⟩, hh.1, hh.2⟩
      · cases hce
  have hcondEq : ∀ r, allHold conds r = true → eqHold eqs r = true := by
    intro r hr
    unfold eqHold
    rw [List.all_eq_true]
    intro e he
    obtain ⟨⟨c, hc, hpe⟩, _, _⟩ := heqs_mem e he
    have hh : c.cond.holds r = true := by
      unfold allHold at hr; exact List.all_eq_true.1 hr c hc
    rw [prefixEq_holds hpe (hid c hc e.1 e.2 hpe) hh]; simp
  have hseed := seed_bag (m := m) (Q := J'.1) (J := J'.2) (eqs := eqs) (g := eqHold eqs)
    (fun e he => (heqs_mem e he).2.2)
    (fun b hb e he => hbindJ b hb e.1 (heqs_mem e he).2.1)
    (fun e he r hr => by
      unfold eqHold at hr; have := List.all_eq_true.1 hr e he; simpa using this) acc
  have hXJ : X.Perm (joinB m P0 J'.1 accS J'.2) := (hfrom accS).2
  have hYJ : Y.Perm (joinB m P0 J'.1 acc J'.2) := (hfrom acc).2
  have hXYeq : (X.filter (eqHold eqs)).Perm (Y.filter (eqHold eqs)) := by
    refine (hXJ.filter _).trans ?_
    rw [hseed.1]
    exact (hYJ.filter _).symm
  have hXY : ∀ x ∈ X, x ∈ Y := fun x hx => hYJ.symm.subset (hseed.2 x (hXJ.subset hx))
  -- the reference side
  have hD : SRel (joinAll m n (othD E ins)) (Ps, Y) :=
    hJ1.trans (patFold_congr st E patsI hH).symm
  rw [show (joinAll m n (othD E ins)).1 = Ps from hD.1] at hL
  obtain ⟨LY, hLY, hLYp⟩ := lateral_perm (E.at st) pb _ Ps hD.2.symm hL
  obtain ⟨LX, hLX, hLXs⟩ := lateral_sub (E.at st) pb _ Ps hXY hLY
  -- the evaluator side
  have hord' := patFold_perm st E hord (P0, accS)
  have hP1' : P1 = Ps := by
    rw [hP1, hord'.1]; exact patFold_schema st E patsI P0 accS acc
  have hR1' : R1.Perm (X.filter (allHold applied)) := hR1.trans (hord'.2.filter _)
  have hvars : ∀ c ∈ applied, PushedOk c ∧ c.early = true ∧ ∀ i ∈ c.vars, i ∈ orderVars E patsI := by
    intro c hc
    obtain ⟨h1, h2, h3⟩ := happ c hc
    exact ⟨h1, h2, fun i hi => (orderVars_mem_perm hord).1 (by simpa using h3 i hi)⟩
  have hLXa := lateral_filter (E.at st) pb _ Ps hbindX (fun r hr q => allHold_merge hvars hr q) hLX
  obtain ⟨L1, hL1, hL1p⟩ := ev_lateral hp _ Ps hR1' hLXa
  unfold inljRun at *
  rw [ev_bind, hev]
  simp only []
  rw [← hP1'] at hL1
  rw [ev_bind, hL1]
  refine ⟨_, rfl, isoFilter_perm _ ?_⟩
  rw [foldl_filterB]
  -- the filters
  have e1 : (L1.filter (allHold later)).Perm (LX.filter (allHold conds)) := by
    refine (hL1p.filter _).trans (List.Perm.of_eq ?_)
    rw [List.filter_filter]
    congr 1; funext r
    rw [allHold_perm hpl, allHold_append, Bool.and_comm]
  refine e1.trans ?_
  have hbe : ∀ r, Binds (orderVars E patsI) r → ∀ q, eqHold eqs (merge r q) = eqHold eqs r :=
    fun r hr q => eqHold_merge (fun e he => hr e.1 (heqs_mem e he).2.1) q
  have hXe := lateral_filter (E.at st) pb _ Ps hbindX hbe hLX
  have hYe := lateral_filter (E.at st) pb _ Ps hbindY hbe hLY
  obtain ⟨L'', hL'', hL''p⟩ := lateral_perm (E.at st) pb _ Ps hXYeq hYe
  rw [hXe] at hL''
  cases hL''
  have split : ∀ (K : Bag), K.filter (allHold conds) = (K.filter (eqHold eqs)).filter (allHold conds) := by
    intro K
    rw [List.filter_filter]
    congr 1; funext r
    cases h : allHold conds r
    · simp
    · simp [hcondEq r h]
  rw [split LX]
  refine (hL''p.filter _).trans ?_
  rw [← split LY]
  exact hLYp.filter _

end

end Tiramemsu.Exec

