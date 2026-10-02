/-
Stable historical results (query-semantics "Machine-checked stability"): extending a store
state by later commits leaves the reference bag of a query whose patterns all use `AsOf(t)`
views, `t` up to the earlier state's last transaction, unchanged.

The reference semantics reads the store only at its leaves (triple patterns, inline values,
path patterns), so the proof has two parts: a generic simulation (`denote_sub`: when every leaf
read on the later state returns what it returned on the earlier one, so does `denote`), and the
store part (`triplePat_sub`, `valuesB_sub`): an `AsOf(t)` pattern sees the same statements on
both states (M2's `Extends`: old statements keep their content and are retracted only after
the earlier state's last transaction; new ones are added later), the same transactions, and a
dictionary that only grew.
-/
import Tiramemsu.Sem.Denote
import TiramemsuProofs.Store.Invariant
import Mathlib.Tactic

namespace Tiramemsu.Sem

open Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Store

--# @lat: [[verification#Proven Query Semantics]]

/-! ## Result refinement -/

/-- `y` returns whatever `x` returns when `x` succeeds. -/
def Sub {ε α : Type} (x y : Except ε α) : Prop := ∀ v, x = .ok v → y = .ok v

theorem Sub.refl {ε α : Type} (x : Except ε α) : Sub x x := fun _ h => h

theorem Sub.of_eq {ε α : Type} {x y : Except ε α} (h : x = y) : Sub x y := fun _ h' => h ▸ h'

theorem Sub.bind {ε α β : Type} {x y : Except ε α} {f g : α → Except ε β} (hx : Sub x y)
    (hf : ∀ a, Sub (f a) (g a)) : Sub (x >>= f) (y >>= g) := by
  intro v h
  cases x with
  | error e => cases h
  | ok a =>
    have hy := hx a rfl
    subst hy
    exact hf a v h

theorem Sub.pure {ε α : Type} (a : α) : Sub (pure a : Except ε α) (pure a) := Sub.refl _

theorem Sub.liftL {α : Type} {x y : Except LErr α} (h : Sub x y) : Sub (liftL x) (liftL y) := by
  intro v hv
  cases x with
  | error e => cases hv
  | ok a =>
    have hy := h a rfl
    subst hy
    exact hv

theorem Sub.map {ε α β : Type} {x y : Except ε α} (f : α → β) (h : Sub x y) : Sub (f <$> x) (f <$> y) := by
  intro v hv
  cases x with
  | error e => cases hv
  | ok a =>
    have hy := h a rfl
    subst hy
    exact hv

theorem Sub.mapM {ε α β : Type} {f g : α → Except ε β} :
    ∀ l : List α, (∀ a ∈ l, Sub (f a) (g a)) → Sub (l.mapM f) (l.mapM g)
  | [], _ => Sub.refl _
  | a :: l, h => by
    simp only [List.mapM_cons]
    exact Sub.bind (h a (List.mem_cons_self ..)) fun _ =>
      Sub.bind (Sub.mapM l fun b hb => h b (List.mem_cons_of_mem _ hb)) fun _ => Sub.refl _

theorem Sub.mapM₂ {ε α γ β : Type} {R : α → γ → Prop} {f : α → Except ε β} {g : γ → Except ε β} :
    ∀ {l : List α} {l' : List γ}, List.Forall₂ R l l' → (∀ a b, R a b → Sub (f a) (g b)) →
      Sub (l.mapM f) (l'.mapM g)
  | [], [], _, _ => Sub.refl _
  | a :: l, b :: l', .cons hab hl, h => by
    simp only [List.mapM_cons]
    exact Sub.bind (h a b hab) fun _ => Sub.bind (Sub.mapM₂ hl h) fun _ => Sub.refl _

/-! ## The leaves a query reads -/

mutual

/-- Every triple pattern of an operator tree (including those of `EXISTS` subqueries) satisfies `f`. -/
def opPats (f : TriplePattern → Bool) : Op → Bool
  | .triple t => f t
  | .path _ => true
  | .values _ _ => true
  | .join xs => opsPats f xs
  | .union xs => opsPats f xs
  | .leftJoin l r c => opPats f l && opPats f r && optPats f c
  | .filter c x => exprPats f c && opPats f x
  | .extend _ e x => exprPats f e && opPats f x
  | .aggregate _ aggs x => aggsPats f aggs && opPats f x
  | .project _ _ x => opPats f x
  | .orderLimit keys _ _ x => keysPats f keys && opPats f x

def opsPats (f : TriplePattern → Bool) : List Op → Bool
  | [] => true
  | x :: xs => opPats f x && opsPats f xs

def exprPats (f : TriplePattern → Bool) : Expr → Bool
  | .cmp _ a b => exprPats f a && exprPats f b
  | .sameTerm a b => exprPats f a && exprPats f b
  | .arith _ a b => exprPats f a && exprPats f b
  | .and xs => exprsPats f xs
  | .or xs => exprsPats f xs
  | .coalesce xs => exprsPats f xs
  | .func _ xs => exprsPats f xs
  | .not a => exprPats f a
  | .neg a => exprPats f a
  | .inList a xs _ => exprPats f a && exprsPats f xs
  | .ite c a b => exprPats f c && exprPats f a && exprPats f b
  | .exists q _ => opPats f q
  | .var _ => true
  | .const _ => true
  | .param _ => true
  | .bound _ => true

def exprsPats (f : TriplePattern → Bool) : List Expr → Bool
  | [] => true
  | x :: xs => exprPats f x && exprsPats f xs

def optPats (f : TriplePattern → Bool) : Option Expr → Bool
  | none => true
  | some e => exprPats f e

def aggsPats (f : TriplePattern → Bool) : List (Var × AggFunc × Option Expr × Bool) → Bool
  | [] => true
  | (_, _, a, _) :: rest => optPats f a && aggsPats f rest

def keysPats (f : TriplePattern → Bool) : List (Expr × Bool) → Bool
  | [] => true
  | (e, _) :: rest => exprPats f e && keysPats f rest

end

/-! ## The generic simulation -/

section Generic

variable (E : Env) (st' : ModelState) (pa pb : PathSem) (f : TriplePattern → Bool)
  (hT : ∀ t, f t = true → Sub (triplePat E t) (triplePat { E with st := st' } t))
  (hV : ∀ vs rows, Sub (valuesB E vs rows) (valuesB { E with st := st' } vs rows))
  (hP : ∀ p row, Sub (pa E p row) (pb { E with st := st' } p row))

include hP in
theorem lateralPaths_sub : ∀ (P : Schema) (rows : Bag) (ps : List PathPattern),
    Sub (lateralPaths E pa P rows ps) (lateralPaths { E with st := st' } pb P rows ps)
  | _, _, [] => Sub.refl _
  | P, rows, p :: ps => by
    simp only [lateralPaths]
    exact Sub.bind (Sub.mapM rows fun a _ => Sub.bind (hP p a) fun _ => Sub.refl _) fun _ =>
      lateralPaths_sub _ _ ps

include hT hV hP

mutual

theorem denote_sub : ∀ op : Op, opPats f op = true →
    Sub (denote E pa op) (denote { E with st := st' } pb op)
  | .triple t, h => by
    simp only [opPats] at h; simp only [denote]
    exact Sub.bind (Sub.refl _) fun _ => Sub.liftL (hT t h)
  | .path p, _ => by
    simp only [denote]
    exact Sub.bind (Sub.refl _) fun _ => Sub.liftL (hP p [])
  | .values vs rows, _ => by
    simp only [denote]
    exact Sub.bind (Sub.refl _) fun _ => Sub.liftL (hV vs rows)
  | .join xs, h => by
    simp only [opPats] at h; simp only [denote]
    exact Sub.bind (denoteInputs_sub xs h) fun _ =>
      Sub.bind (Sub.liftL (lateralPaths_sub E st' pa pb hP _ _ _)) fun _ => Sub.refl _
  | .union xs, h => by
    simp only [opPats] at h; simp only [denote]
    exact Sub.bind (denoteList_sub xs h) fun _ => Sub.refl _
  | .leftJoin l r c, h => by
    simp only [opPats, Bool.and_eq_true] at h; simp only [denote]
    exact Sub.bind (denote_sub l h.1.1) fun _ => Sub.bind (denote_sub r h.1.2) fun _ =>
      Sub.bind (resolveOpt_sub c h.2) fun _ => Sub.refl _
  | .filter c x, h => by
    simp only [opPats, Bool.and_eq_true] at h; simp only [denote]
    exact Sub.bind (resolveE_sub c h.1) fun _ => Sub.bind (denote_sub x h.2) fun _ => Sub.refl _
  | .extend v e x, h => by
    simp only [opPats, Bool.and_eq_true] at h; simp only [denote]
    exact Sub.bind (Sub.refl _) fun _ => Sub.bind (resolveE_sub e h.1) fun _ =>
      Sub.bind (denote_sub x h.2) fun _ => Sub.refl _
  | .aggregate g aggs x, h => by
    simp only [opPats, Bool.and_eq_true] at h; simp only [denote]
    exact Sub.bind (Sub.refl _) fun _ => Sub.bind (resolveAggs_sub aggs h.1) fun _ =>
      Sub.bind (denote_sub x h.2) fun _ => Sub.refl _
  | .project vs d x, h => by
    simp only [opPats] at h; simp only [denote]
    exact Sub.bind (Sub.refl _) fun _ => Sub.bind (denote_sub x h) fun _ => Sub.refl _
  | .orderLimit keys s l x, h => by
    simp only [opPats, Bool.and_eq_true] at h; simp only [denote]
    exact Sub.bind (Sub.refl _) fun _ => Sub.bind (resolveKeys_sub keys h.1) fun _ =>
      Sub.bind (Sub.refl _) fun _ => Sub.bind (Sub.refl _) fun _ => Sub.bind (denote_sub x h.2) fun _ => Sub.refl _

theorem denoteList_sub : ∀ xs : List Op, opsPats f xs = true →
    Sub (denoteList E pa xs) (denoteList { E with st := st' } pb xs)
  | [], _ => Sub.refl _
  | x :: xs, h => by
    simp only [opsPats, Bool.and_eq_true] at h; simp only [denoteList]
    exact Sub.bind (denote_sub x h.1) fun _ => Sub.bind (denoteList_sub xs h.2) fun _ => Sub.refl _

theorem denoteInputs_sub : ∀ xs : List Op, opsPats f xs = true →
    Sub (denoteInputs E pa xs) (denoteInputs { E with st := st' } pb xs)
  | [], _ => Sub.refl _
  | .path p :: xs, h => by
    simp only [opsPats, Bool.and_eq_true] at h; simp only [denoteInputs]
    exact Sub.bind (Sub.refl _) fun _ => Sub.bind (denoteInputs_sub xs h.2) fun _ => Sub.refl _
  | .triple t :: xs, h | .values _ _ :: xs, h | .join _ :: xs, h | .leftJoin _ _ _ :: xs, h
  | .union _ :: xs, h | .filter _ _ :: xs, h | .extend _ _ _ :: xs, h | .aggregate _ _ _ :: xs, h
  | .project _ _ _ :: xs, h | .orderLimit _ _ _ _ :: xs, h => by
    simp only [opsPats, Bool.and_eq_true] at h; simp only [denoteInputs]
    exact Sub.bind (denote_sub _ h.1) fun _ => Sub.bind (denoteInputs_sub xs h.2) fun _ => Sub.refl _

theorem resolveE_sub : ∀ e : Expr, exprPats f e = true →
    Sub (resolveE E pa e) (resolveE { E with st := st' } pb e)
  | .var _, _ | .const _, _ | .param _, _ | .bound _, _ => by simp only [resolveE]; exact Sub.refl _
  | .cmp _ a b, h | .sameTerm a b, h | .arith _ a b, h => by
    simp only [exprPats, Bool.and_eq_true] at h; simp only [resolveE]
    exact Sub.bind (resolveE_sub a h.1) fun _ => Sub.bind (resolveE_sub b h.2) fun _ => Sub.refl _
  | .and xs, h | .or xs, h | .coalesce xs, h => by
    simp only [exprPats] at h; simp only [resolveE]
    exact Sub.bind (resolveEs_sub xs h) fun _ => Sub.refl _
  | .not a, h | .neg a, h => by
    simp only [exprPats] at h; simp only [resolveE]
    exact Sub.bind (resolveE_sub a h) fun _ => Sub.refl _
  | .inList a xs _, h => by
    simp only [exprPats, Bool.and_eq_true] at h; simp only [resolveE]
    exact Sub.bind (resolveE_sub a h.1) fun _ => Sub.bind (resolveEs_sub xs h.2) fun _ => Sub.refl _
  | .ite c a b, h => by
    simp only [exprPats, Bool.and_eq_true] at h; simp only [resolveE]
    exact Sub.bind (resolveE_sub c h.1.1) fun _ => Sub.bind (resolveE_sub a h.1.2) fun _ =>
      Sub.bind (resolveE_sub b h.2) fun _ => Sub.refl _
  | .func fn args, h => by
    simp only [exprPats] at h; simp only [resolveE]
    refine Sub.bind (Sub.refl _) fun _ => ?_
    split
    · exact Sub.refl _
    · exact Sub.bind (resolveEs_sub args h) fun _ => Sub.refl _
  | .exists q _, h => by
    simp only [exprPats] at h; simp only [resolveE]
    exact Sub.bind (denote_sub q h) fun _ => Sub.refl _

theorem resolveEs_sub : ∀ xs : List Expr, exprsPats f xs = true →
    Sub (resolveEs E pa xs) (resolveEs { E with st := st' } pb xs)
  | [], _ => Sub.refl _
  | x :: xs, h => by
    simp only [exprsPats, Bool.and_eq_true] at h; simp only [resolveEs]
    exact Sub.bind (resolveE_sub x h.1) fun _ => Sub.bind (resolveEs_sub xs h.2) fun _ => Sub.refl _

theorem resolveOpt_sub : ∀ c : Option Expr, optPats f c = true →
    Sub (resolveOpt E pa c) (resolveOpt { E with st := st' } pb c)
  | none, _ => Sub.refl _
  | some e, h => by
    simp only [optPats] at h; simp only [resolveOpt]
    exact Sub.bind (resolveE_sub e h) fun _ => Sub.refl _

theorem resolveAggs_sub : ∀ xs : List (Var × AggFunc × Option Expr × Bool), aggsPats f xs = true →
    Sub (resolveAggs E pa xs) (resolveAggs { E with st := st' } pb xs)
  | [], _ => Sub.refl _
  | (v, fn, none, d) :: rest, h => by
    simp only [aggsPats, optPats, Bool.true_and] at h; simp only [resolveAggs]
    exact Sub.bind (Sub.refl _) fun _ => Sub.bind (resolveAggs_sub rest h) fun _ => Sub.refl _
  | (v, fn, some e, d) :: rest, h => by
    simp only [aggsPats, optPats, Bool.and_eq_true] at h; simp only [resolveAggs]
    exact Sub.bind (resolveE_sub e h.1) fun _ => Sub.bind (Sub.refl _) fun _ =>
      Sub.bind (resolveAggs_sub rest h.2) fun _ => Sub.refl _

theorem resolveKeys_sub : ∀ xs : List (Expr × Bool), keysPats f xs = true →
    Sub (resolveKeys E pa xs) (resolveKeys { E with st := st' } pb xs)
  | [], _ => Sub.refl _
  | (e, d) :: rest, h => by
    simp only [keysPats, Bool.and_eq_true] at h; simp only [resolveKeys]
    exact Sub.bind (resolveE_sub e h.1) fun _ => Sub.bind (resolveKeys_sub rest h.2) fun _ => Sub.refl _

end

end Generic

/-! ## The dictionary only grows -/

/-- Every datatype reference of a dictionary row names a row of the dictionary (the writer
interns a literal's datatype IRI before the literal). -/
def TermsClosed (st : ModelState) : Prop :=
  ∀ i r raw, Term.modelRowById st i = some r → r.dt = some raw →
    (⟨raw⟩ : ObjectId).tagBits = Tag.iri.toUInt64 →
      (Term.modelRowById st (ObjectId.upayload ⟨raw⟩).toNat).isSome = true

theorem find?_prefix {α : Type} {p : α → Bool} {l l' : List α} {x : α} (h : l <+: l')
    (hx : l.find? p = some x) : l'.find? p = some x := by
  obtain ⟨m, rfl⟩ := h
  simp [List.find?_append, hx]

theorem rowById_prefix {a b : ModelState} (hp : a.terms <+: b.terms) {i : Nat} {r : Term.Row}
    (h : Term.modelRowById a i = some r) : Term.modelRowById b i = some r := by
  unfold Term.modelRowById ModelState.termById at *
  cases hf : a.terms.find? (·.id == i.toInt64) with
  | none => rw [hf] at h; cases h
  | some x => rw [hf] at h; rw [find?_prefix hp hf]; exact h

theorem decodeId_sub {a b : ModelState} (hp : a.terms <+: b.terms) (hc : TermsClosed a) (x : Int64) :
    Sub (decodeId a x) (decodeId b x) := by
  intro v h
  unfold decodeId at h ⊢
  unfold Term.decode at h ⊢
  simp only [bind, pure, Term.TermReader.rowById] at h ⊢
  cases hdi : decodeInline (⟨x⟩ : ObjectId) with
  | error e => simp [hdi, pure, ReaderT.pure, Except.pure] at h
  | ok o =>
    cases o with
    | some w => simpa [hdi, pure, ReaderT.pure, Except.pure] using h
    | none =>
      cases htg : (⟨x⟩ : ObjectId).tag with
      | error e => simp [hdi, htg, pure, ReaderT.pure, Except.pure] at h
      | ok t =>
        simp only [hdi, htg] at h ⊢
        cases hr : Term.modelRowById a (ObjectId.upayload ⟨x⟩).toNat with
        | none => simp [ReaderT.bind, ReaderT.pure, hr, bind, Except.bind, pure, Except.pure] at h
        | some r =>
          have hr' := rowById_prefix hp hr
          simp only [ReaderT.bind, hr, hr', bind, Except.bind] at h ⊢
          by_cases htag : (r.tag != t) = true
          · simp [htag, ReaderT.pure, pure, Except.pure] at h
          · rw [if_neg htag] at h ⊢
            cases hdt : r.dt with
            | none => simpa [hdt, ReaderT.pure, ReaderT.bind, bind, Except.bind, pure, Except.pure] using h
            | some raw =>
              simp only [hdt] at h ⊢
              by_cases hiri : ((⟨raw⟩ : ObjectId).tagBits == Tag.iri.toUInt64) = true
              · rw [if_pos hiri] at h ⊢
                have hs := hc _ r raw hr hdt (by simpa using hiri)
                obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hs
                have hd' := rowById_prefix hp hd
                simpa [hd, hd', ReaderT.pure, ReaderT.bind, bind, Except.bind, pure, Except.pure] using h
              · rw [if_neg hiri] at h ⊢
                simpa [ReaderT.pure, ReaderT.bind, bind, Except.bind, pure, Except.pure] using h

/-! ## As-of views see the same statements -/

/-- A triple pattern under `AsOf(t)` with `t ≤ T`. -/
def asOfWithin (T : Int) (t : TriplePattern) : Bool :=
  match t.view.tx with
  | .asOf (.tx u) => decide (u.toInt ≤ T)
  | _ => false

theorem admits_ext {T : Int} {u : Int64} {valid : ValidSel} {r r' : TripleRow} (h : Engine.RowExt T r r')
    (hu : u.toInt ≤ T) :
    Store.View.admits { tx := .asOf u, valid } r' = Store.View.admits { tx := .asOf u, valid } r := by
  have hv : valid.admits r' = valid.admits r := by
    cases valid <;> simp [ValidSel.admits, h.vFrom, h.vTo]
  simp only [Store.View.admits, TxSel.admits, hv, h.tAdd]
  rcases h.ret with ⟨e1, _⟩ | ⟨e1, x, e2, hx⟩
  · rw [e1]
  · rw [e1, e2]; simp [show u.toInt < x.toInt by omega]

theorem admits_new {T : Int} {u : Int64} {valid : ValidSel} {r : TripleRow} (hn : T < r.tAdd.toInt)
    (hu : u.toInt ≤ T) : Store.View.admits { tx := .asOf u, valid } r = false := by
  simp only [Store.View.admits, TxSel.admits, Bool.and_eq_false_iff]
  left; left; simp; omega

theorem forall₂_filter {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, R a b → q b = p a) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → List.Forall₂ R (l.filter p) (l'.filter q)
  | [], [], _ => .nil
  | a :: l, b :: l', .cons h hl => by
    simp only [List.filter_cons, hpq a b h]
    split
    · exact .cons h (forall₂_filter hpq hl)
    · exact forall₂_filter hpq hl

theorem forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → g b = f a) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → l'.map g = l.map f
  | [], [], _ => rfl
  | a :: l, b :: l', .cons h hl => by simp [hfg a b h, forall₂_map_eq hfg hl]

theorem visible_ext {a b : ModelState} (hx : Engine.Extends a b) {u : Int64} (hu : u.toInt ≤ Engine.lastT a)
    (valid : ValidSel) :
    List.Forall₂ (Engine.RowExt (Engine.lastT a)) (visibleRows a { tx := .asOf u, valid })
      (visibleRows b { tx := .asOf u, valid }) := by
  obtain ⟨pre, new, hb, hf, hn⟩ := hx.rows
  unfold visibleRows
  rw [hb, List.filter_append]
  have hnil : new.filter (Store.View.admits { tx := .asOf u, valid }) = [] := by
    rw [List.filter_eq_nil_iff]
    intro r hr
    simp [admits_new (hn r hr).2 hu]
  rw [hnil, List.append_nil]
  exact forall₂_filter (fun r r' h => admits_ext h hu) hf

theorem mask_ext {T : Int} {u : Int64} {valid : ValidSel} {r r' : TripleRow} (h : Engine.RowExt T r r') :
    View.mask { tx := .asOf u, valid } r' = View.mask { tx := .asOf u, valid } r := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, _⟩ := h
  simp only [View.mask, e1, e2, e3, e4, e5, e6, e7]

theorem txByT_ext {a b : ModelState} (wa : Engine.WF a) (hp : a.txs <+: b.txs) {k : Int64}
    (h1 : 1 ≤ k.toInt) (h2 : k.toInt ≤ Engine.lastT a) : a.txByT k = b.txByT k := by
  have hmem : k.toInt ∈ a.txs.map (·.t.toInt) := by
    rw [wa.txs, List.mem_map]
    exact ⟨(k.toInt - 1).toNat, List.mem_range.2 (by omega), by omega⟩
  obtain ⟨x, hx, hxk⟩ := List.mem_map.1 hmem
  have hxk' : x.t = k := Int64.toInt_inj.1 hxk
  have hs : (a.txs.find? (·.t == k)).isSome = true := List.find?_isSome.2 ⟨x, hx, by simp [hxk']⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  unfold ModelState.txByT
  rw [hy, find?_prefix hp hy]

/-! ## Leaf reads -/

theorem Sub.foldlM {ε α β : Type} {f g : β → α → Except ε β} (hfg : ∀ acc x, Sub (f acc x) (g acc x)) :
    ∀ (l : List α) (init : β), Sub (l.foldlM f init) (l.foldlM g init)
  | [], _ => Sub.refl _
  | x :: l, init => by
    simp only [List.foldlM_cons]
    exact Sub.bind (hfg init x) fun s => Sub.foldlM hfg l s


section Leaves

variable {a b : ModelState} (hp : a.terms <+: b.terms) (hc : TermsClosed a)

theorem bindOpt_sub {α : Type} {x y : Except LErr (Option α)} {f g : α → Except LErr (Option α)}
    (hx : Sub x y) (hf : ∀ a, Sub (f a) (g a)) : Sub (bindOpt x f) (bindOpt y g) := by
  unfold bindOpt
  exact Sub.bind hx fun o => by cases o <;> simp only [] <;> first | exact hf _ | exact Sub.refl _

include hp hc

theorem matchPos_sub (E : Env) (hE : E.st = a) (t : TermOrVar) (x : Int64) (row : Row) :
    Sub (matchPos E t x row) (matchPos { E with st := b } t x row) := by
  subst hE
  cases t <;> simp only [matchPos]
  · exact Sub.bind (decodeId_sub hp hc x) fun _ => Sub.refl _
  · exact Sub.bind (decodeId_sub hp hc x) fun _ => Sub.refl _
  · exact Sub.refl _
  · exact Sub.refl _

theorem matchVal_sub (E : Env) (hE : E.st = a) (bv : Bool) (t : TermOrVar) (val : Value) (row : Row) :
    Sub (matchVal E bv t val row) (matchVal { E with st := b } bv t val row) := by
  subst hE
  cases t <;> simp only [matchVal]
  · exact Sub.refl _
  · exact Sub.refl _
  · exact Sub.bind (decodeId_sub hp hc _) fun _ => Sub.refl _
  · exact Sub.refl _

theorem membershipsOf_sub (v : Store.View) (e : Int64)
    (h : List.Forall₂ (Engine.RowExt (Engine.lastT a)) (visibleRows a v) (visibleRows b v)) :
    Sub (membershipsOf a v e) (membershipsOf b v e) := by
  unfold membershipsOf
  refine Sub.bind (Sub.mapM₂ (forall₂_filter (fun r r' hr => by simp [hr.s]) h) ?_) fun _ => Sub.refl _
  intro m m' hm
  rw [hm.p, hm.o]
  exact Sub.bind (decodeId_sub hp hc _) fun _ => by
    split
    · exact Sub.bind (decodeId_sub hp hc _) fun _ => Sub.refl _
    · exact Sub.refl _

theorem graphRows_sub (E : Env) (hE : E.st = a) (v : Store.View) (g : GraphSel) (e : Int64) (row : Row)
    (h : List.Forall₂ (Engine.RowExt (Engine.lastT a)) (visibleRows a v) (visibleRows b v)) :
    Sub (graphRows E v g e row) (graphRows { E with st := b } v g e row) := by
  subst hE
  cases g <;> simp only [graphRows]
  · exact Sub.refl _
  · exact Sub.bind (membershipsOf_sub hp hc v e h) fun _ => Sub.refl _
  · exact Sub.bind (membershipsOf_sub hp hc v e h) fun _ => Sub.refl _

theorem storedRows_sub (E : Env) (hE : E.st = a) (v : Store.View) (t : TriplePattern) {r r' : TripleRow}
    (hr : Engine.RowExt (Engine.lastT a) r r')
    (h : List.Forall₂ (Engine.RowExt (Engine.lastT a)) (visibleRows a v) (visibleRows b v)) :
    Sub (storedRows E v t r) (storedRows { E with st := b } v t r') := by
  have hm := matchPos_sub hp hc E hE
  cases hev : t.eid <;> simp only [storedRows, hev, hr.s, hr.p, hr.o, hr.eid]
  · exact Sub.bind (bindOpt_sub (hm _ _ _) fun _ => bindOpt_sub (hm _ _ _) fun _ =>
      bindOpt_sub (hm _ _ _) fun _ => Sub.refl _) fun o => by
        cases o
        · exact Sub.refl _
        · exact graphRows_sub hp hc E hE v _ _ _ h
  · exact Sub.bind (bindOpt_sub (hm _ _ _) fun _ => bindOpt_sub (hm _ _ _) fun _ =>
      bindOpt_sub (hm _ _ _) fun _ => Sub.bind (by subst hE; exact decodeId_sub hp hc _) fun _ => Sub.refl _)
      fun o => by
        cases o
        · exact Sub.refl _
        · exact graphRows_sub hp hc E hE v _ _ _ h

theorem virtualRow_sub (E : Env) (hE : E.st = a) (t : TriplePattern) (vp : VirtualPred) (r : TripleRow)
    (htx : a.txByT r.tAdd = b.txByT r.tAdd) (hret : r.tRet = none) :
    Sub (virtualRow E t vp r) (virtualRow { E with st := b } t vp r) := by
  subst hE
  have hv : Sub (virtualValue E.st vp r) (virtualValue b vp r) := by
    cases vp <;> simp only [virtualValue, htx, hret]
    all_goals first
      | exact Sub.refl _
      | exact Sub.bind (decodeId_sub hp hc _) fun _ => Sub.refl _
  simp only [virtualRow]
  exact Sub.bind hv fun o => by
    cases o
    · exact Sub.refl _
    · exact Sub.bind (decodeId_sub hp hc _) fun _ =>
        bindOpt_sub (matchVal_sub hp hc E rfl _ _ _ _) fun _ => matchVal_sub hp hc E rfl _ _ _ _

theorem cellValue_sub (c : Option TermOrVar) : Sub (cellValue a c) (cellValue b c) := by
  unfold cellValue
  split
  · exact Sub.refl _
  · exact Sub.bind (decodeId_sub hp hc _) fun _ => Sub.refl _
  · exact Sub.refl _

theorem valuesB_sub (E : Env) (hE : E.st = a) (vs : List Var) (rows : List (List (Option TermOrVar))) :
    Sub (valuesB E vs rows) (valuesB { E with st := b } vs rows) := by
  subst hE
  unfold valuesB valuesRow
  exact Sub.mapM rows fun cells _ => Sub.foldlM (fun r (vc : Var × Option TermOrVar) => Sub.bind (cellValue_sub hp hc vc.2) fun o => by
    cases o <;> exact Sub.refl _) _ _

end Leaves

theorem triplePat_sub {a b : ModelState} (wa : Engine.WF a) (hx : Engine.Extends a b) (hc : TermsClosed a)
    (E : Env) (hE : E.st = a) (t : TriplePattern) (ht : asOfWithin (Engine.lastT a) t = true) :
    Sub (triplePat E t) (triplePat { E with st := b } t) := by
  have hp := hx.terms
  unfold asOfWithin at ht
  split at ht
  case h_2 => cases ht
  rename_i u htx
  have hu : u.toInt ≤ Engine.lastT a := by simpa using ht
  have hview : ∀ st, resolveView st t.view = { tx := .asOf u, valid := t.view.valid } := by
    intro st; simp [resolveView, htx]
  have hvis := visible_ext hx hu t.view.valid
  unfold triplePat
  simp only [hview]
  cases hvp : t.p.virtual? with
  | none =>
    simp only [hvp, collectRows]
    rw [hE]
    have hm := Sub.mapM₂ hvis fun r r' hr => storedRows_sub hp hc E hE _ t hr hvis
    first
      | exact Sub.bind hm fun _ => Sub.refl _
      | exact Sub.bind (Sub.bind hm fun _ => Sub.refl _) fun _ => Sub.refl _
  | some vp =>
    simp only [hvp, collectRows]
    rw [hE, forall₂_map_eq (fun r r' hr => mask_ext hr) hvis]
    suffices hm : ∀ r ∈ (visibleRows a { tx := .asOf u, valid := t.view.valid }).map
        (View.mask { tx := .asOf u, valid := t.view.valid }),
        Sub (virtualRow E t vp r) (virtualRow { E with st := b } t vp r) by
      have hm' := Sub.mapM (f := fun r => do return (← virtualRow E t vp r).toList)
        (g := fun r => do return (← virtualRow { E with st := b } t vp r).toList) _
        fun r hr => Sub.bind (hm r hr) fun _ => Sub.refl _
      first
        | exact Sub.bind hm' fun _ => Sub.refl _
        | exact Sub.bind (Sub.bind hm' fun _ => Sub.refl _) fun _ => Sub.refl _
    intro r hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
    have hmem := (List.mem_filter.1 hr0).1
    have hok := wa.rows r0 hmem
    have hta : (View.mask { tx := .asOf u, valid := t.view.valid } r0).tAdd = r0.tAdd := by simp [View.mask]
    refine virtualRow_sub hp hc E hE t vp _ ?_ (by simp [View.mask])
    rw [hta]
    exact txByT_ext wa hx.txs hok.tAddLo hok.tAddHi

/-! ## Stability -/

/-- query-semantics "Stable historical results": when `b` extends `a` (later commits), every
query whose patterns all use `AsOf(t)` views with `t` up to `a`'s last transaction returns on `b`
the bag it returns on `a` (path patterns: whenever the path semantics is itself stable). -/
theorem denote_stable {a b : ModelState} (wa : Engine.WF a) (hx : Engine.Extends a b) (hc : TermsClosed a)
    (E : Env) (hE : E.st = a) (pa pb : PathSem)
    (hP : ∀ p row, Sub (pa E p row) (pb { E with st := b } p row))
    (op : Op) (h : opPats (asOfWithin (Engine.lastT a)) op = true) (bag : Bag)
    (hd : denote E pa op = .ok bag) : denote { E with st := b } pb op = .ok bag :=
  denote_sub E b pa pb _ (fun t ht => triplePat_sub wa hx hc E hE t ht)
    (fun vs rows => valuesB_sub hx.terms hc E hE vs rows) hP op h bag hd

/-- The same for a prepared query, with path patterns rejected (`pathPatStub`). -/
theorem prepared_stable {a b : ModelState} (wa : Engine.WF a) (hx : Engine.Extends a b) (hc : TermsClosed a)
    (p : Prepared) (h : opPats (asOfWithin (Engine.lastT a)) p.root = true) (bag : Bag)
    (hd : denote (p.env a) pathPatStub p.root = .ok bag) : denote (p.env b) pathPatStub p.root = .ok bag :=
  denote_stable wa hx hc (p.env a) rfl pathPatStub pathPatStub (fun _ _ _ hv => by cases hv) p.root h bag hd

end Tiramemsu.Sem
