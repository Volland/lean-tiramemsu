/-
The never-forget invariant: `WF` on committed states, `Extends` between states, and the
in-transaction invariant `TxInv` that every body operation preserves.
-/
import TiramemsuProofs.Store.ModelOps
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec

--# @lat: [[verification#Proven Store State Machine]]

/-! ## Definitions -/

/-- The last committed transaction number. -/
def lastT (st : ModelState) : Int := ctr st "last_t"
/-- The next statement counter. -/
def nextStmt (st : ModelState) : Int := ctr st "next_stmt"
/-- The instant of the last committed transaction. -/
def lastInstant (st : ModelState) : Int := ctr st "last_instant"

/-- A stored statement: its eid a `STMT` id issued below `N`; a subject-capable subject, an
`IRI` predicate, neither its own eid; a nonempty interval; `1 ≤ t_add ≤ T`; and `t_ret` and
`ret_kind` both absent, or both present with `t_add ≤ t_ret ≤ T` and a kind in 0–3. -/
structure RowOK (T N : Int) (r : TripleRow) : Prop where
  tag : rawTag r.eid = 3
  ctrLo : 0 ≤ eidCtr r.eid
  ctrHi : eidCtr r.eid < N
  subj : 0 ≤ rawTag r.s ∧ rawTag r.s ≤ 4
  pred : rawTag r.p = 0
  noSelfS : r.s ≠ r.eid
  noSelfO : r.o ≠ r.eid
  valid : Valid.nonempty ⟨r.vFrom, r.vTo⟩ = true
  tAddLo : 1 ≤ r.tAdd.toInt
  tAddHi : r.tAdd.toInt ≤ T
  ret : (r.tRet = none ∧ r.retKind = none) ∨
    (∃ x k, r.tRet = some x ∧ r.retKind = some k ∧ r.tAdd.toInt ≤ x.toInt ∧ x.toInt ≤ T ∧
      0 ≤ k.toInt ∧ k.toInt ≤ 3)

theorem RowOK.mono {T T' N N' : Int} {r : TripleRow} (h : RowOK T N r) (hT : T ≤ T') (hN : N ≤ N') :
    RowOK T' N' r := by
  refine ⟨h.tag, h.ctrLo, by have := h.ctrHi; omega, h.subj, h.pred, h.noSelfS, h.noSelfO, h.valid, h.tAddLo,
    by have := h.tAddHi; omega, ?_⟩
  rcases h.ret with h1 | ⟨x, k, h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl h1
  · exact Or.inr ⟨x, k, h1, h2, h3, by omega, h5, h6⟩

/-- A well-formed committed state: unique eids; every statement `RowOK`; transaction numbers
exactly `1 … last_t`; instants strictly increasing and at most `last_instant`. -/
structure WF (st : ModelState) : Prop where
  uniq : st.triples.Pairwise fun a b => a.eid ≠ b.eid
  rows : ∀ r ∈ st.triples, RowOK (lastT st) (nextStmt st) r
  lastTLo : 0 ≤ lastT st
  lastTHi : lastT st ≤ (counterMax : Int)
  nextLo : 0 ≤ nextStmt st
  txs : st.txs.map (·.t.toInt) = List.map (fun i : Nat => (i : Int) + 1) (List.range (lastT st).toNat)
  inst : (st.txs.map (·.instant.toInt)).Pairwise (· < ·)
  lastInst : ∀ r ∈ st.txs, r.instant.toInt ≤ lastInstant st

/-- How a statement may evolve: same content; the retraction unchanged, or newly set after `T`. -/
structure RowExt (T : Int) (r r' : TripleRow) : Prop where
  eid : r'.eid = r.eid
  s : r'.s = r.s
  p : r'.p = r.p
  o : r'.o = r.o
  tAdd : r'.tAdd = r.tAdd
  vFrom : r'.vFrom = r.vFrom
  vTo : r'.vTo = r.vTo
  ret : (r'.tRet = r.tRet ∧ r'.retKind = r.retKind) ∨
    (r.tRet = none ∧ ∃ x, r'.tRet = some x ∧ T < x.toInt)

/-- The id counters a speculation burns and that never go down. -/
def idNames : List String := ["next_term", "next_node", "next_bnode", "next_stmt"]

/-- `b` extends `a`: every statement of `a` is in `b` with its content, retracted only later
than `a`'s last transaction if it was live; new statements have eids issued from `a`'s counter
on and later transaction numbers; terms and transaction rows are prefixes; id counters and the
last transaction number never go down. -/
structure Extends (a b : ModelState) : Prop where
  rows : ∃ pre new, b.triples = pre ++ new ∧ List.Forall₂ (RowExt (lastT a)) a.triples pre ∧
    ∀ r ∈ new, nextStmt a ≤ eidCtr r.eid ∧ lastT a < r.tAdd.toInt
  terms : a.terms <+: b.terms
  txs : a.txs <+: b.txs
  ids : ∀ n ∈ idNames, ctr a n ≤ ctr b n
  lastT : lastT a ≤ lastT b

/-! ## Extends is a preorder -/

theorem RowExt.refl (T : Int) (r : TripleRow) : RowExt T r r :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem RowExt.trans {T T' : Int} (hT : T ≤ T') {a b c : TripleRow} (h1 : RowExt T a b) (h2 : RowExt T' b c) :
    RowExt T a c := by
  refine ⟨h2.eid.trans h1.eid, h2.s.trans h1.s, h2.p.trans h1.p, h2.o.trans h1.o, h2.tAdd.trans h1.tAdd,
    h2.vFrom.trans h1.vFrom, h2.vTo.trans h1.vTo, ?_⟩
  rcases h1.ret with ⟨e1, k1⟩ | ⟨n1, x, hx, hlt⟩ <;> rcases h2.ret with ⟨e2, k2⟩ | ⟨n2, y, hy, hlt'⟩
  · exact Or.inl ⟨e2.trans e1, k2.trans k1⟩
  · exact Or.inr ⟨by rw [← e1]; exact n2, y, hy, by omega⟩
  · exact Or.inr ⟨n1, x, by rw [e2]; exact hx, hlt⟩
  · rw [hx] at n2; cases n2

theorem Extends.refl (a : ModelState) : Extends a a :=
  ⟨⟨a.triples, [], by simp, List.forall₂_same.2 fun r _ => RowExt.refl _ r, by simp⟩,
    List.prefix_refl _, List.prefix_refl _, fun _ _ => le_refl _, le_refl _⟩

theorem forall₂_append_left {R : TripleRow → TripleRow → Prop} :
    ∀ {l : List TripleRow} {m₁ m₂ : List TripleRow}, List.Forall₂ R l (m₁ ++ m₂) →
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂
  | l, [], m₂, h => ⟨[], l, rfl, List.Forall₂.nil, h⟩
  | x :: l, y :: m₁, m₂, List.Forall₂.cons hxy h => by
    obtain ⟨l₁, l₂, rfl, h1, h2⟩ := forall₂_append_left h
    exact ⟨x :: l₁, l₂, rfl, List.Forall₂.cons hxy h1, h2⟩

theorem forall₂_split {R : TripleRow → TripleRow → Prop} :
    ∀ {l₁ l₂ m : List TripleRow}, List.Forall₂ R (l₁ ++ l₂) m →
      ∃ m₁ m₂, m = m₁ ++ m₂ ∧ List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂
  | [], l₂, m, h => ⟨[], m, rfl, List.Forall₂.nil, h⟩
  | x :: l₁, l₂, y :: m, List.Forall₂.cons hxy h => by
    obtain ⟨m₁, m₂, rfl, h1, h2⟩ := forall₂_split h
    exact ⟨y :: m₁, m₂, rfl, List.Forall₂.cons hxy h1, h2⟩

theorem forall₂_trans {R S T : TripleRow → TripleRow → Prop} (hrst : ∀ a b c, R a b → S b c → T a c) :
    ∀ {l m n : List TripleRow}, List.Forall₂ R l m → List.Forall₂ S m n → List.Forall₂ T l n
  | [], [], [], _, _ => List.Forall₂.nil
  | _ :: _, _ :: _, _ :: _, List.Forall₂.cons h1 r1, List.Forall₂.cons h2 r2 =>
    List.Forall₂.cons (hrst _ _ _ h1 h2) (forall₂_trans hrst r1 r2)

theorem forall₂_mem_right {R : TripleRow → TripleRow → Prop} :
    ∀ {l m : List TripleRow}, List.Forall₂ R l m → ∀ r ∈ m, ∃ y ∈ l, R y r
  | [], [], _, r, hr => by cases hr
  | x :: _, y :: _, List.Forall₂.cons hxy rest, r, hr => by
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨x, List.mem_cons_self .., hxy⟩
    · obtain ⟨z, hz, h⟩ := forall₂_mem_right rest r hr
      exact ⟨z, List.mem_cons_of_mem _ hz, h⟩

theorem Extends.trans {a b c : ModelState} (h1 : Extends a b) (h2 : Extends b c) : Extends a c := by
  obtain ⟨pre1, new1, hb, f1, n1⟩ := h1.rows
  obtain ⟨pre2, new2, hc, f2, n2⟩ := h2.rows
  rw [hb] at f2
  obtain ⟨p2a, p2b, hp2, f2a, f2b⟩ := forall₂_split f2
  have hlt : Engine.lastT a ≤ Engine.lastT b := h1.lastT
  refine ⟨⟨p2a, p2b ++ new2, by rw [hc, hp2, List.append_assoc], ?_, ?_⟩, h1.terms.trans h2.terms,
    h1.txs.trans h2.txs, fun n hn => le_trans (h1.ids n hn) (h2.ids n hn), le_trans h1.lastT h2.lastT⟩
  · exact forall₂_trans (R := RowExt (Engine.lastT a)) (S := RowExt (Engine.lastT b))
      (T := RowExt (Engine.lastT a)) (fun x y z hxy hyz => RowExt.trans hlt hxy hyz) f1 f2a
  · intro r hr
    have hsn : nextStmt a ≤ nextStmt b := h1.ids "next_stmt" (by simp [idNames])
    rcases List.mem_append.1 hr with hr | hr
    · obtain ⟨y, hy, hrel⟩ := forall₂_mem_right f2b r hr
      have := n1 y hy
      rw [hrel.eid, hrel.tAdd]; exact this
    · have := n2 r hr
      exact ⟨le_trans hsn this.1, lt_of_le_of_lt hlt this.2⟩

end Tiramemsu.Engine
