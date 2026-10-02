/-
Validation soundness (query-ir "Machine-checked validation soundness"): a validated query with
complete parameters never fails with `InvalidQuery` on any store state. The reference
semantics checks each node with the local rule `validate` applies to the whole tree, and its
leaves can only raise `LErr` failures, none of which is `InvalidQuery`.
-/
import Tiramemsu.Sem.Denote
import Mathlib.Tactic

namespace Tiramemsu.Sem

open Tiramemsu.Codec Tiramemsu.IR

--# @lat: [[verification#Proven Query Semantics]]

/-- A result that is not an `InvalidQuery` failure. -/
def NoInv {α : Type} (r : Except QError α) : Prop := ∀ m, r ≠ .error (.invalidQuery m)

theorem NoInv.ok {α : Type} (a : α) : NoInv (.ok a : Except QError α) := fun _ h => by cases h

theorem NoInv.pure {α : Type} (a : α) : NoInv (pure a : Except QError α) := NoInv.ok a

theorem NoInv.bind {α β : Type} {x : Except QError α} {f : α → Except QError β} (hx : NoInv x)
    (hf : ∀ a, NoInv (f a)) : NoInv (x >>= f) := by
  intro m h
  cases x with
  | error e =>
    have h' : (Except.error e : Except QError β) = .error (.invalidQuery m) := h
    cases h'
    exact hx _ rfl
  | ok a => exact hf a m h

theorem NoInv.liftL {α : Type} (x : Except LErr α) : NoInv (Tiramemsu.IR.liftL x) := by
  intro m h
  cases x with
  | ok a => cases h
  | error e => cases e <;> cases h

theorem bind_unit_ok {ε : Type} {x : Except ε Unit} {y : Except ε Unit} (h : (x >>= fun _ => y) = .ok ()) :
    x = .ok () ∧ y = .ok () := by
  cases x with
  | error e => cases h
  | ok u => cases u; exact ⟨rfl, h⟩

theorem bind_unit_eq {ε α : Type} {x : Except ε Unit} {f : Unit → Except ε α} (h : x = .ok ()) :
    (x >>= f) = f () := by subst h; rfl

theorem countOf_noInv (c : Option TermOrVar) : NoInv (countOf c) := by
  unfold countOf; split <;> exact NoInv.ok _

theorem match_opt_noInv {α : Type} (c : Option α) (f : α → Except QError (Option RExpr))
    (hf : ∀ a, NoInv (f a)) : NoInv (match c with | some e => f e | none => .ok none) := by
  cases c <;> simp [hf, NoInv.ok]

mutual

theorem denote_noInv (E : Env) (pb : PathSem) :
    ∀ op : Op, validateOp op = .ok () → NoInv (denote E pb op)
  | .triple t, h => by
    simp only [validateOp] at h; simp only [denote]; rw [bind_unit_eq h]; exact NoInv.liftL _
  | .path p, h => by
    simp only [validateOp] at h; simp only [denote]; rw [bind_unit_eq h]; exact NoInv.liftL _
  | .values vs rows, h => by
    simp only [validateOp] at h; simp only [denote]; rw [bind_unit_eq h]; exact NoInv.liftL _
  | .join xs, h => by
    simp only [validateOp] at h; simp only [denote]
    exact NoInv.bind (denoteInputs_noInv E pb xs h) fun _ => NoInv.bind (NoInv.liftL _) fun _ => NoInv.pure _
  | .union xs, h => by
    simp only [validateOp] at h; simp only [denote]
    exact NoInv.bind (denoteList_noInv E pb xs h) fun _ => NoInv.pure _
  | .leftJoin l r none, h => by
    simp only [validateOp] at h
    obtain ⟨hl, h⟩ := bind_unit_ok h
    obtain ⟨hr, _⟩ := bind_unit_ok h
    simp only [denote, resolveOpt]
    exact NoInv.bind (denote_noInv E pb l hl) fun _ => NoInv.bind (denote_noInv E pb r hr) fun _ =>
      NoInv.bind (NoInv.ok _) fun _ => NoInv.pure _
  | .leftJoin l r (some e), h => by
    simp only [validateOp] at h
    obtain ⟨hl, h⟩ := bind_unit_ok h
    obtain ⟨hr, hc⟩ := bind_unit_ok h
    simp only [denote, resolveOpt]
    exact NoInv.bind (denote_noInv E pb l hl) fun _ => NoInv.bind (denote_noInv E pb r hr) fun _ =>
      NoInv.bind (NoInv.bind (resolveE_noInv E pb e hc) fun _ => NoInv.pure _) fun _ => NoInv.pure _
  | .filter c x, h => by
    simp only [validateOp] at h
    obtain ⟨hc, hx⟩ := bind_unit_ok h
    simp only [denote]
    exact NoInv.bind (resolveE_noInv E pb c hc) fun _ => NoInv.bind (denote_noInv E pb x hx) fun _ => NoInv.pure _
  | .extend v e x, h => by
    simp only [validateOp] at h
    obtain ⟨h0, h⟩ := bind_unit_ok h
    obtain ⟨he, hx⟩ := bind_unit_ok h
    simp only [denote]; rw [bind_unit_eq h0]
    exact NoInv.bind (resolveE_noInv E pb e he) fun _ => NoInv.bind (denote_noInv E pb x hx) fun _ => NoInv.pure _
  | .aggregate g aggs x, h => by
    simp only [validateOp] at h
    obtain ⟨h0, h⟩ := bind_unit_ok h
    obtain ⟨ha, hx⟩ := bind_unit_ok h
    simp only [denote]; rw [bind_unit_eq h0]
    exact NoInv.bind (resolveAggs_noInv E pb aggs ha) fun _ => NoInv.bind (denote_noInv E pb x hx) fun _ => NoInv.pure _
  | .project vs d x, h => by
    simp only [validateOp] at h
    obtain ⟨h0, hx⟩ := bind_unit_ok h
    simp only [denote]; rw [bind_unit_eq h0]
    exact NoInv.bind (denote_noInv E pb x hx) fun _ => NoInv.pure _
  | .orderLimit keys s l x, h => by
    simp only [validateOp] at h
    obtain ⟨h0, h⟩ := bind_unit_ok h
    obtain ⟨hk, hx⟩ := bind_unit_ok h
    simp only [denote]; rw [bind_unit_eq h0]
    exact NoInv.bind (resolveKeys_noInv E pb keys hk) fun _ => NoInv.bind (countOf_noInv s) fun _ =>
      NoInv.bind (countOf_noInv l) fun _ => NoInv.bind (denote_noInv E pb x hx) fun _ => NoInv.pure _

theorem denoteList_noInv (E : Env) (pb : PathSem) :
    ∀ xs : List Op, validateOps xs = .ok () → NoInv (denoteList E pb xs)
  | [], _ => NoInv.ok _
  | x :: xs, h => by
    simp only [validateOps] at h
    obtain ⟨hx, hxs⟩ := bind_unit_ok h
    simp only [denoteList]
    exact NoInv.bind (denote_noInv E pb x hx) fun _ => NoInv.bind (denoteList_noInv E pb xs hxs) fun _ => NoInv.pure _

theorem denoteInputs_noInv (E : Env) (pb : PathSem) :
    ∀ xs : List Op, validateOps xs = .ok () → NoInv (denoteInputs E pb xs)
  | [], _ => NoInv.ok _
  | .path p :: xs, h => by
    simp only [validateOps] at h
    obtain ⟨hx, hxs⟩ := bind_unit_ok h
    simp only [validateOp] at hx
    simp only [denoteInputs]; rw [bind_unit_eq hx]
    exact NoInv.bind (denoteInputs_noInv E pb xs hxs) fun _ => NoInv.pure _
  | .triple t :: xs, h | .values _ _ :: xs, h | .join _ :: xs, h | .leftJoin _ _ _ :: xs, h
  | .union _ :: xs, h | .filter _ _ :: xs, h | .extend _ _ _ :: xs, h | .aggregate _ _ _ :: xs, h
  | .project _ _ _ :: xs, h | .orderLimit _ _ _ _ :: xs, h => by
    simp only [validateOps] at h
    obtain ⟨hx, hxs⟩ := bind_unit_ok h
    simp only [denoteInputs]
    exact NoInv.bind (denote_noInv E pb _ hx) fun _ => NoInv.bind (denoteInputs_noInv E pb xs hxs) fun _ => NoInv.pure _

theorem resolveE_noInv (E : Env) (pb : PathSem) :
    ∀ e : Expr, validateExpr e = .ok () → NoInv (resolveE E pb e)
  | .var _, _ | .const _, _ | .param _, _ | .bound _, _ => by simp only [resolveE]; exact NoInv.ok _
  | .cmp _ a b, h | .sameTerm a b, h | .arith _ a b, h => by
    simp only [validateExpr] at h
    obtain ⟨ha, hb⟩ := bind_unit_ok h
    simp only [resolveE]
    exact NoInv.bind (resolveE_noInv E pb a ha) fun _ => NoInv.bind (resolveE_noInv E pb b hb) fun _ => NoInv.pure _
  | .and xs, h | .or xs, h | .coalesce xs, h => by
    simp only [validateExpr] at h
    simp only [resolveE]
    exact NoInv.bind (resolveEs_noInv E pb xs h) fun _ => NoInv.pure _
  | .not a, h | .neg a, h => by
    simp only [validateExpr] at h
    simp only [resolveE]
    exact NoInv.bind (resolveE_noInv E pb a h) fun _ => NoInv.pure _
  | .inList a xs _, h => by
    simp only [validateExpr] at h
    obtain ⟨ha, hb⟩ := bind_unit_ok h
    simp only [resolveE]
    exact NoInv.bind (resolveE_noInv E pb a ha) fun _ => NoInv.bind (resolveEs_noInv E pb xs hb) fun _ => NoInv.pure _
  | .ite c a b, h => by
    simp only [validateExpr] at h
    obtain ⟨hc, h⟩ := bind_unit_ok h
    obtain ⟨ha, hb⟩ := bind_unit_ok h
    simp only [resolveE]
    exact NoInv.bind (resolveE_noInv E pb c hc) fun _ => NoInv.bind (resolveE_noInv E pb a ha) fun _ =>
      NoInv.bind (resolveE_noInv E pb b hb) fun _ => NoInv.pure _
  | .func f args, h => by
    simp only [validateExpr] at h
    obtain ⟨h0, ha⟩ := bind_unit_ok h
    simp only [resolveE]; rw [bind_unit_eq h0]
    split
    · intro m hm; cases hm
    · exact NoInv.bind (resolveEs_noInv E pb args ha) fun _ => NoInv.pure _
  | .exists q _, h => by
    simp only [validateExpr] at h
    simp only [resolveE]
    exact NoInv.bind (denote_noInv E pb q h) fun _ => NoInv.pure _

theorem resolveEs_noInv (E : Env) (pb : PathSem) :
    ∀ xs : List Expr, validateExprs xs = .ok () → NoInv (resolveEs E pb xs)
  | [], _ => NoInv.ok _
  | x :: xs, h => by
    simp only [validateExprs] at h
    obtain ⟨hx, hxs⟩ := bind_unit_ok h
    simp only [resolveEs]
    exact NoInv.bind (resolveE_noInv E pb x hx) fun _ => NoInv.bind (resolveEs_noInv E pb xs hxs) fun _ => NoInv.pure _

theorem resolveAggs_noInv (E : Env) (pb : PathSem) :
    ∀ xs : List (Var × AggFunc × Option Expr × Bool), validateAggs xs = .ok () → NoInv (resolveAggs E pb xs)
  | [], _ => NoInv.ok _
  | (v, f, none, d) :: rest, h => by
    simp only [validateAggs] at h
    obtain ⟨_, hr⟩ := bind_unit_ok h
    simp only [resolveAggs]
    exact NoInv.bind (NoInv.pure _) fun _ => NoInv.bind (resolveAggs_noInv E pb rest hr) fun _ => NoInv.pure _
  | (v, f, some e, d) :: rest, h => by
    simp only [validateAggs] at h
    obtain ⟨ha, hr⟩ := bind_unit_ok h
    simp only [resolveAggs]
    exact NoInv.bind (resolveE_noInv E pb e ha) fun _ => NoInv.bind (NoInv.pure _) fun _ =>
      NoInv.bind (resolveAggs_noInv E pb rest hr) fun _ => NoInv.pure _

theorem resolveKeys_noInv (E : Env) (pb : PathSem) :
    ∀ xs : List (Expr × Bool), validateKeys xs = .ok () → NoInv (resolveKeys E pb xs)
  | [], _ => NoInv.ok _
  | (e, d) :: rest, h => by
    simp only [validateKeys] at h
    obtain ⟨he, hr⟩ := bind_unit_ok h
    simp only [resolveKeys]
    exact NoInv.bind (resolveE_noInv E pb e he) fun _ => NoInv.bind (resolveKeys_noInv E pb rest hr) fun _ => NoInv.pure _

end

theorem prepare_validates {ps : Params} {q : Query} {p : Prepared} (h : prepare ps q = .ok p) :
    validateOp p.root = .ok () := by
  unfold prepare at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i root _
    split at h
    · cases h
    · rename_i hv
      cases h
      exact hv

/-- query-ir: a validated query with complete parameters never fails with `InvalidQuery`, on
any store state and with any path semantics. -/
theorem validation_sound (pb : PathSem) (st : Store.ModelState)
    {ps : Params} {q : Query} (_hv : validate q = .ok ()) (hc : Complete ps q) :
    ∀ m, denoteWith pb st ps q ≠ .error (.invalidQuery m) := by
  obtain ⟨p, hp⟩ := hc
  unfold denoteWith
  rw [hp]
  exact denote_noInv _ pb p.root (prepare_validates hp)

end Tiramemsu.Sem
