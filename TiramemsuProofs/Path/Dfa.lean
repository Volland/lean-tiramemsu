/-
path-evaluation "Automaton compilation": the compiled automaton accepts exactly the words of
its expression's language, and its run on a word is unique.

The refined alphabet classifies letters so that every symbol of the expression agrees on a
letter and its class; derivatives by classes are then left quotients by letters
(`RE.deriv_lang`), and the breadth-first construction keeps every transition equal to a
derivative of its source state.
-/
import TiramemsuProofs.Path.Lang

namespace Tiramemsu.Path

open Tiramemsu.IR

--# @lat: [[query#Paths#Automaton]]

/-! ## The refined alphabet -/

theorem predOf_eq (d : Dir) (c : Cls) (p : String) : predOf d c = some p ↔ c = .pred p d := by
  cases c <;> simp [predOf] <;> tauto

theorem virtOf_eq (d : Dir) (c : Cls) (k : VKind) : virtOf d c = some k ↔ c = .virt k d := by
  cases c <;> simp [virtOf] <;> tauto

theorem mem_alphabetDir (ss : List Cls) (d : Dir) (c : LClass) :
    c ∈ alphabetDir ss d ↔
      (∃ p, c = .pred p d none ∧ Cls.pred p d ∈ ss ∧ Cls.anyRel d ∉ ss) ∨
      (∃ p b, c = .pred p d (some b) ∧ Cls.pred p d ∈ ss ∧ Cls.anyRel d ∈ ss) ∨
      (c = .other d ∧ Cls.anyRel d ∈ ss) ∨
      (∃ k, c = .virt k d ∧ Cls.virt k d ∈ ss) := by
  unfold alphabetDir
  simp only [List.mem_append, List.mem_flatMap, List.mem_eraseDups, List.mem_filterMap, predOf_eq, virtOf_eq,
    List.mem_map, List.contains_iff_mem]
  by_cases ha : Cls.anyRel d ∈ ss <;> simp [ha] <;> aesop

theorem mem_alphabet (r : RE) (c : LClass) : c ∈ alphabet r ↔ ∃ d, c ∈ alphabetDir r.syms d := by
  unfold alphabet
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨d, _, h⟩; exact ⟨d, h⟩
  · rintro ⟨d, h⟩; exact ⟨d, by cases d <;> simp, h⟩

theorem mem_alphabet_pred_none (r : RE) (p : String) (d : Dir) :
    LClass.pred p d none ∈ alphabet r ↔ Cls.pred p d ∈ r.syms ∧ Cls.anyRel d ∉ r.syms := by
  rw [mem_alphabet]; simp only [mem_alphabetDir]; aesop

theorem mem_alphabet_pred_some (r : RE) (p : String) (d : Dir) (b : Bool) :
    LClass.pred p d (some b) ∈ alphabet r ↔ Cls.pred p d ∈ r.syms ∧ Cls.anyRel d ∈ r.syms := by
  rw [mem_alphabet]; simp only [mem_alphabetDir]; aesop

theorem mem_alphabet_other (r : RE) (d : Dir) : LClass.other d ∈ alphabet r ↔ Cls.anyRel d ∈ r.syms := by
  rw [mem_alphabet]; simp only [mem_alphabetDir]; aesop

theorem mem_alphabet_virt (r : RE) (k : VKind) (d : Dir) :
    LClass.virt k d ∈ alphabet r ↔ Cls.virt k d ∈ r.syms := by
  rw [mem_alphabet]; simp only [mem_alphabetDir]; aesop

theorem classOf_mem {alpha : List LClass} {l : Letter} {c : LClass} (h : classOf alpha l = some c) : c ∈ alpha := by
  cases l <;> simp only [classOf] at h <;> split_ifs at h <;> cases h <;> simp_all [List.contains_iff_mem]

/-- A symbol of the expression agrees on a letter and its class. -/
theorem class_compat (r : RE) {s : Cls} (hs : s ∈ r.syms) {l : Letter} {c : LClass}
    (h : classOf (alphabet r) l = some c) : s.matchesClass c = s.matches l := by
  cases l with
  | stored p rel d =>
    simp only [classOf, List.contains_iff_mem, mem_alphabet_pred_none, mem_alphabet_pred_some] at h
    split_ifs at h with h1 h2 h3 <;> cases h <;> cases s <;> simp_all [Cls.matchesClass, Cls.matches]
    all_goals first
      | aesop
      | (cases rel <;> simp [Cls.matchesClass])
  | virt k d =>
    simp only [classOf, List.contains_iff_mem, mem_alphabet_virt] at h
    split_ifs at h with h1 <;> cases h <;> cases s <;> simp_all [Cls.matchesClass, Cls.matches] <;> done

/-- A letter without a class matches no symbol of the expression. -/
theorem class_none (r : RE) {s : Cls} (hs : s ∈ r.syms) {l : Letter}
    (h : classOf (alphabet r) l = none) : s.matches l = false := by
  cases l with
  | stored p rel d =>
    simp only [classOf, List.contains_iff_mem, mem_alphabet_pred_none, mem_alphabet_pred_some,
      mem_alphabet_other] at h
    split_ifs at h with h1 h2 h3 <;> cases s <;> simp_all [Cls.matches, mem_alphabet_other]
    all_goals aesop
  | virt k d =>
    simp only [classOf, List.contains_iff_mem, mem_alphabet_virt] at h
    split_ifs at h with h1 <;> cases s <;> simp_all [Cls.matches]
    all_goals aesop

/-! ## The construction -/

section Build

variable (A : List LClass) (r0 : RE)

/-- A transition `(class index, target)` of a state `r`: the target is the derivative by that class. -/
def Sound (S : Array RE) (r : RE) (e : Nat × Nat) : Prop :=
  ∃ c, A[e.1]? = some c ∧ S[e.2]? = some (r.deriv c)

/-- The row of a state: sound transitions, one for every class with a non-`empty` derivative. -/
def RowOK (S : Array RE) (row : List (Nat × Nat)) (r : RE) : Prop :=
  (∀ e ∈ row, Sound A S r e) ∧ ∀ ci c, A[ci]? = some c → (r.deriv c).isEmpty = false → ∃ j, (ci, j) ∈ row

/-- The state table: the index points at equal states, and every state's symbols are the expression's. -/
def Good (S : Array RE) (index : Std.HashMap RE Nat) : Prop :=
  (∀ (x : RE) (j : Nat), index.get? x = some j → S[j]? = some x) ∧
    ∀ (j : Nat) (x : RE), S[j]? = some x → ∀ s ∈ x.syms, s ∈ r0.syms

def Ext (S S' : Array RE) : Prop := ∀ (j : Nat) (x : RE), S[j]? = some x → S'[j]? = some x

theorem Ext.refl (S : Array RE) : Ext S S := fun _ _ h => h

theorem Ext.trans {S S' S'' : Array RE} (h1 : Ext S S') (h2 : Ext S' S'') : Ext S S'' :=
  fun j x h => h2 j x (h1 j x h)

theorem Ext.push (S : Array RE) (d : RE) : Ext S (S.push d) := by
  intro j x h
  rw [Array.getElem?_push]
  have : j < S.size := by
    rcases Nat.lt_or_ge j S.size with hj | hj
    · exact hj
    · rw [Array.getElem?_eq_none hj] at h; cases h
  rw [if_neg (by omega)]; exact h

theorem Sound.ext {S S' : Array RE} (h : Ext S S') {r : RE} {e : Nat × Nat} (hs : Sound A S r e) : Sound A S' r e := by
  obtain ⟨c, hc, hd⟩ := hs
  exact ⟨c, hc, h _ _ hd⟩

theorem RowOK.ext {S S' : Array RE} (h : Ext S S') {row : List (Nat × Nat)} {r : RE} (hr : RowOK A S row r) :
    RowOK A S' row r :=
  ⟨fun e he => (hr.1 e he).ext A h, hr.2⟩

theorem addRow_spec (r : RE) (hr : ∀ s ∈ r.syms, s ∈ r0.syms) :
    ∀ (xs : List (LClass × Nat)) (S : Array RE) (index : Std.HashMap RE Nat) (row : List (Nat × Nat)),
      Good r0 S index → (∀ e ∈ row, Sound A S r e) → (∀ x ∈ xs, A[x.2]? = some x.1) →
      ∀ S' index' row', addRow r xs (S, index, row) = (S', index', row') →
        Good r0 S' index' ∧ Ext S S' ∧ (∀ e ∈ row', Sound A S' r e) ∧ (∀ e ∈ row, e ∈ row') ∧
          ∀ x ∈ xs, (r.deriv x.1).isEmpty = false → ∃ j, (x.2, j) ∈ row'
  | [], S, index, row, hg, hrow, _, S', index', row', h => by
    simp only [addRow, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hg, Ext.refl _, hrow, fun _ h => h, by simp⟩
  | (c, ci) :: rest, S, index, row, hg, hrow, hxs, S', index', row', h => by
    have hci : A[ci]? = some c := hxs (c, ci) (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, A[x.2]? = some x.1 := fun x hx => hxs x (List.mem_cons_of_mem _ hx)
    simp only [addRow] at h
    split at h
    · rename_i he
      obtain ⟨g, e, s, m, k⟩ := addRow_spec r hr rest S index row hg hrow hrest S' index' row' h
      refine ⟨g, e, s, m, ?_⟩
      intro x hx hne
      rcases List.mem_cons.1 hx with rfl | hx
      · simp_all
      · exact k x hx hne
    · rename_i he
      split at h
      · rename_i j hj
        have hsj : S[j]? = some (r.deriv c) := hg.1 _ _ hj
        obtain ⟨g, e, s, m, k⟩ := addRow_spec r hr rest S index (row ++ [(ci, j)]) hg
          (by
            intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact hrow x hx
            · simp at hx; subst hx; exact ⟨c, hci, hsj⟩) hrest S' index' row' h
        refine ⟨g, e, s, fun x hx => m x (List.mem_append_left _ hx), ?_⟩
        intro x hx hne
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨j, m _ (by simp)⟩
        · exact k x hx hne
      · rename_i hj
        have hg' : Good r0 (S.push (r.deriv c)) (index.insert (r.deriv c) S.size) := by
          refine ⟨fun x j hx => ?_, fun j x hx => ?_⟩
          · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hx
            split at hx
            · rename_i heq
              cases hx
              rw [Array.getElem?_push, if_pos rfl]
              simp at heq; rw [heq]
            · rw [← Std.HashMap.get?_eq_getElem?] at hx
              exact Ext.push S _ _ _ (hg.1 x j hx)
          · rw [Array.getElem?_push] at hx
            split at hx
            · cases hx
              intro s hs
              exact hr s (RE.syms_deriv c r s hs)
            · exact hg.2 j x hx
        have hS : S[S.size]? = none := Array.getElem?_eq_none (le_refl _)
        obtain ⟨g, e, s, m, k⟩ := addRow_spec r hr rest (S.push (r.deriv c)) (index.insert (r.deriv c) S.size)
          (row ++ [(ci, S.size)]) hg'
          (by
            intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact (hrow x hx).ext A (Ext.push S _)
            · simp at hx; subst hx
              exact ⟨c, hci, by rw [Array.getElem?_push, if_pos rfl]⟩) hrest S' index' row' h
        refine ⟨g, (Ext.push S _).trans e, s, fun x hx => m x (List.mem_append_left _ hx), ?_⟩
        intro x hx hne
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨S.size, m _ (by simp)⟩
        · exact k x hx hne

theorem Ext.size {S S' : Array RE} (h : Ext S S') : S.size ≤ S'.size := by
  rcases Nat.eq_zero_or_pos S.size with h0 | hpos
  · omega
  · have hl : S[S.size - 1]? = some S[S.size - 1] := Array.getElem?_eq_getElem (by omega)
    have := h _ _ hl
    have := (Array.getElem?_eq_some_iff.1 this).1
    omega

theorem buildGo_spec : ∀ (fuel i : Nat) (S : Array RE) (index : Std.HashMap RE Nat) (T : Array (List (Nat × Nat)))
    (d : Dfa), Good r0 S index → T.size = i → i ≤ S.size →
    (∀ (q : Nat) (row : List (Nat × Nat)), T[q]? = some row → ∃ r, S[q]? = some r ∧ RowOK A S row r) →
    buildGo A.toArray fuel i S index T = .ok d →
      d.alpha = A.toArray ∧ Ext S d.states ∧ d.trans.size = d.states.size ∧
      (∀ (q : Nat) (row : List (Nat × Nat)), d.trans[q]? = some row → ∃ r, d.states[q]? = some r ∧ RowOK A d.states row r) ∧
      d.accepting = d.states.map RE.nullable ∧ (∀ (j : Nat) (x : RE), d.states[j]? = some x → ∀ s ∈ x.syms, s ∈ r0.syms)
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [buildGo] at h
  | fuel + 1, i, S, index, T, d, hg, hT, hi, hrows, h => by
    simp only [buildGo] at h
    split at h
    · rename_i hlt
      rcases hres : addRow S[i] A.toArray.toList.zipIdx (S, index, []) with ⟨S', index', row⟩
      rw [hres] at h
      simp only at h
      split at h
      · cases h
      · have hri : ∀ s ∈ S[i].syms, s ∈ r0.syms := hg.2 i S[i] (Array.getElem?_eq_getElem hlt)
        obtain ⟨g, e, snd, _, comp⟩ := addRow_spec A r0 S[i] hri _ S index [] hg (by simp)
          (fun x hx => by simpa using (List.mem_zipIdx_iff_getElem?.1 hx)) S' index' row hres
        suffices hh : i + 1 ≤ S'.size ∧ ∀ (q : Nat) (r : List (Nat × Nat)), (T.push row)[q]? = some r →
            ∃ x, S'[q]? = some x ∧ RowOK A S' r x by
          obtain ⟨a1, a2, a3⟩ := buildGo_spec fuel (i + 1) S' index' (T.push row) d g (by simp [hT]) hh.1 hh.2 h
          exact ⟨a1, e.trans a2, a3⟩
        refine ⟨?_, ?_⟩
        · have := e i S[i] (Array.getElem?_eq_getElem hlt)
          have := (Array.getElem?_eq_some_iff.1 this).1
          omega
        · intro q r hq
          rw [Array.getElem?_push] at hq
          split at hq
          · cases hq
            rename_i hqi
            refine ⟨S[i], ?_, snd, ?_⟩
            · simp only [hqi, hT]; exact e i S[i] (Array.getElem?_eq_getElem hlt)
            · intro ci c hc hne
              exact comp (c, ci) (List.mem_zipIdx_iff_getElem?.2 (by simpa using hc)) hne
          · obtain ⟨x, hx, hrow⟩ := hrows q r hq
            exact ⟨x, e q x hx, hrow.ext A e⟩
    · rename_i hge
      cases h
      refine ⟨rfl, Ext.refl _, by simp; omega, hrows, rfl, hg.2⟩

end Build

/-! ## Runs -/

/-- The transition on a letter: through its class, when it has one. -/
def Dfa.stepL (d : Dfa) (q : Nat) (l : Letter) : Option Nat :=
  match classOf d.alpha.toList l with
  | none => none
  | some c => d.step q (d.alpha.toList.idxOf c)

/-- The run of the automaton on a word from a state (`none`: it dies). -/
def Dfa.runL (d : Dfa) (q : Nat) : List Letter → Option Nat
  | [] => some q
  | l :: w => (d.stepL q l).bind fun q' => d.runL q' w

/-- A run is unique: the automaton is deterministic. -/
theorem runL_unique (d : Dfa) (q : Nat) (w : List Letter) {a b : Nat} (ha : d.runL q w = some a)
    (hb : d.runL q w = some b) : a = b := by
  rw [ha] at hb; exact Option.some.inj hb

theorem RE.isEmpty_iff (r : RE) : r.isEmpty = true ↔ r = .empty := by
  cases r <;> simp [RE.isEmpty]

theorem run_lang (r0 : RE) (d : Dfa) (hα : d.alpha = (alphabet r0).toArray)
    (hsz : d.trans.size = d.states.size)
    (hrows : ∀ (q : Nat) (row : List (Nat × Nat)), d.trans[q]? = some row →
      ∃ r, d.states[q]? = some r ∧ RowOK (alphabet r0) d.states row r)
    (hacc : d.accepting = d.states.map RE.nullable)
    (hsyms : ∀ (j : Nat) (x : RE), d.states[j]? = some x → ∀ s ∈ x.syms, s ∈ r0.syms) :
    ∀ (w : List Letter) (q : Nat) (r : RE), d.states[q]? = some r →
      ((∃ q', d.runL q w = some q' ∧ d.accepts q' = true) ↔ r.Lang w)
  | [], q, r, hq => by
    simp only [Dfa.runL, Option.some.injEq, exists_eq_left', Dfa.accepts, Array.getD_eq_getD_getElem?, hacc,
      Array.getElem?_map, hq, Option.map_some, Option.getD_some]
    exact RE.nullable_iff r
  | l :: w, q, r, hq => by
    have hrs : ∀ s ∈ r.syms, s ∈ r0.syms := hsyms q r hq
    simp only [Dfa.runL, Dfa.stepL, hα, List.toList_toArray]
    cases hc : classOf (alphabet r0) l with
    | none =>
      simp only [Option.bind_none, reduceCtorEq, false_and, exists_false, false_iff]
      intro h
      obtain ⟨s, hs, hm⟩ := RE.lang_letters h l (List.mem_cons_self ..)
      rw [class_none r0 (hrs s hs) hc] at hm
      cases hm
    | some c =>
      simp only
      have hcm : c ∈ alphabet r0 := classOf_mem hc
      have hci : (alphabet r0)[(alphabet r0).idxOf c]? = some c := by
        rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.2 hcm)]
        simp [List.getElem_idxOf]
      have hqlt : q < d.trans.size := by rw [hsz]; exact (Array.getElem?_eq_some_iff.1 hq).1
      obtain ⟨r', hr', hrow⟩ := hrows q _ (Array.getElem?_eq_getElem hqlt)
      rw [hq] at hr'; cases hr'
      have hcompat : ∀ s ∈ r.syms, s.matchesClass c = s.matches l := fun s hs => class_compat r0 (hrs s hs) hc
      rw [← RE.deriv_lang c l r hcompat w]
      simp only [Dfa.step, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hqlt, Option.getD_some]
      cases hf : (d.trans[q]'hqlt).find? (·.1 == (alphabet r0).idxOf c) with
      | none =>
        simp only [Option.map_none, Option.bind_none, reduceCtorEq, false_and, exists_false, false_iff]
        have hne : (r.deriv c).isEmpty = true := by
          by_contra hne
          obtain ⟨j, hj⟩ := hrow.2 _ c hci (by simpa using hne)
          rw [List.find?_eq_none] at hf
          exact hf _ hj (by simp)
        rw [RE.isEmpty_iff] at hne
        rw [hne]
        exact fun h => by cases h
      | some e =>
        simp only [Option.map_some, Option.bind_some]
        have he := List.mem_of_find?_eq_some hf
        have he1 : e.1 = (alphabet r0).idxOf c := by simpa using List.find?_some hf
        obtain ⟨c', hc', hd⟩ := hrow.1 e he
        rw [he1, hci] at hc'; cases hc'
        exact run_lang r0 d hα hsz hrows hacc hsyms w e.2 _ hd

/-- path-evaluation "Automaton compilation": a compiled automaton accepts exactly the words of
its expression's language (and its run on a word is unique, `runL_unique`). -/
theorem buildDfa_lang (r0 : RE) (d : Dfa) (h : buildDfa r0 = .ok d) (w : List Letter) :
    (∃ q, d.runL 0 w = some q ∧ d.accepts q = true) ↔ r0.Lang w := by
  unfold buildDfa at h
  split at h
  · cases h
  · have hg : Good r0 #[r0.norm] ((∅ : Std.HashMap RE Nat).insert r0.norm 0) := by
      refine ⟨fun x j hx => ?_, fun j x hx s hs => ?_⟩
      · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hx
        split at hx
        · rename_i heq
          cases hx
          simp at heq; subst heq; rfl
        · simp at hx
      · have : j = 0 ∧ x = r0.norm := by
          rcases j with _ | j
          · simp at hx; exact ⟨rfl, hx.symm⟩
          · simp at hx
        obtain ⟨rfl, rfl⟩ := this
        exact RE.syms_norm r0 s hs
    obtain ⟨hα, hext, hsz, hrows, hacc, hsyms⟩ :=
      buildGo_spec (alphabet r0) r0 _ 0 _ _ #[] d hg rfl (by simp) (by simp) h
    have h0 : d.states[0]? = some r0.norm := hext 0 _ (by simp)
    rw [run_lang r0 d hα hsz hrows hacc hsyms w 0 _ h0]
    exact RE.norm_equiv r0 w

end Tiramemsu.Path
