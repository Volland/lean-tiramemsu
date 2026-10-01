/-
Footprints of engine computations: which store operations a body program may perform, read
off its syntax tree. A computation whose operations are all reads leaves the store unchanged;
more generally, a relation every allowed operation respects holds between the stores before
and after the run. The checks and lookups of the pipeline are read-only by this route.
-/
import TiramemsuProofs.Store.OpSpec
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec

--# @lat: [[verification#Proven Store State Machine]]

/-! ## The monad laws of body programs -/

theorem SProg.bind_pure_comp' {α : Type} : ∀ (p : SProg α), SProg.bind p SProg.pure = p
  | .pure _ => rfl
  | .op o k => by simp only [SProg.bind]; congr 1; funext x; exact SProg.bind_pure_comp' (k x)

theorem SProg.bind_assoc' {α β γ : Type} : ∀ (p : SProg α) (f : α → SProg β) (g : β → SProg γ),
    SProg.bind (SProg.bind p f) g = SProg.bind p fun a => SProg.bind (f a) g
  | .pure _, _, _ => rfl
  | .op o k, f, g => by simp only [SProg.bind]; congr 1; funext x; exact SProg.bind_assoc' (k x) f g

instance : LawfulMonad SProg := LawfulMonad.mk'
  (id_map := fun x => SProg.bind_pure_comp' x)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x f g => SProg.bind_assoc' x f g)

/-! ## Body programs whose operations satisfy a predicate -/

/-- Every operation of the program satisfies `S`. -/
inductive OpsIn (S : Op → Prop) : {α : Type} → SProg α → Prop
  | pure {α : Type} (a : α) : OpsIn S (.pure a)
  | op {α : Type} (o : Op) (k : o.Res → SProg α) : S o → (∀ x, OpsIn S (k x)) → OpsIn S (.op o k)

theorem OpsIn.bind {S : Op → Prop} {α β : Type} {p : SProg α} {f : α → SProg β}
    (hp : OpsIn S p) (hf : ∀ a, OpsIn S (f a)) : OpsIn S (p >>= f) := by
  show OpsIn S (SProg.bind p f)
  induction hp with
  | pure a => exact hf a
  | op o k ho _ ih => exact OpsIn.op o _ ho fun x => ih x

theorem OpsIn.mono {S T : Op → Prop} (hST : ∀ o, S o → T o) {α : Type} {p : SProg α} (h : OpsIn S p) :
    OpsIn T p := by
  induction h with
  | pure a => exact OpsIn.pure a
  | op o k ho _ ih => exact OpsIn.op o k (hST o ho) ih

/-- A relation every allowed operation respects holds across the whole run. -/
theorem OpsIn.run {S : Op → Prop} {R : ModelStore → ModelStore → Prop} (hrefl : ∀ s, R s s)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hop : ∀ o, S o → ∀ s x s', (Op.run o : ModelM o.Res) s = .ok (x, s') → R s s') :
    ∀ {α : Type} {p : SProg α}, OpsIn S p → ∀ {s : ModelStore} {a : α} {s' : ModelStore},
      SProg.runModel p s = .ok (a, s') → R s s' := by
  intro α p h
  induction h with
  | pure a => intro s b s' hr; simp only [SProg.runModel] at hr; cases hr; exact hrefl s
  | op o k ho _ ih =>
    intro s b s' hr
    simp only [SProg.runModel] at hr
    cases h1 : (Op.run o : ModelM o.Res) s with
    | error e => rw [h1] at hr; cases hr
    | ok p =>
      rcases p with ⟨x, s1⟩
      rw [h1] at hr
      exact htrans _ _ _ (hop o ho s x s1 h1) (ih x hr)

/-- A read operation. -/
def IsRead (o : Op) : Prop := ∃ r, o = .read r

theorem readOnly_run {α : Type} {p : SProg α} (h : OpsIn IsRead p) {s : ModelStore} {a : α} {s' : ModelStore}
    (hr : SProg.runModel p s = .ok (a, s')) : s' = s :=
  (OpsIn.run (R := fun a b => b = a) (fun _ => rfl) (fun _ _ _ h1 h2 => h2.trans h1)
    (fun o ho s x s' hs => by obtain ⟨r, rfl⟩ := ho; exact (read_same hs).1) h hr)

/-! ## Engine computations -/

/-- Every operation an engine computation may perform, from any context, satisfies `S`. -/
def EOps (S : Op → Prop) {α : Type} (x : EngM α) : Prop := ∀ ctx, OpsIn S ((x.run ctx).run)

section
variable {S : Op → Prop}

theorem EOps.pure {α : Type} (a : α) : EOps S (pure a : EngM α) := fun _ => OpsIn.pure _

theorem EOps.bind {α β : Type} {x : EngM α} {f : α → EngM β} (hx : EOps S x) (hf : ∀ a, EOps S (f a)) :
    EOps S (x >>= f) := by
  intro ctx
  show OpsIn S (SProg.bind ((x.run ctx).run) _)
  refine OpsIn.bind (hx ctx) fun e => ?_
  rcases e with e | ⟨a, c⟩
  · exact OpsIn.pure _
  · exact hf a c

theorem EOps.seq {α β : Type} {x : EngM α} {y : EngM β} (hx : EOps S x) (hy : EOps S y) :
    EOps S (x *> y) := by
  show EOps S (x >>= fun _ => y)
  exact EOps.bind hx fun _ => hy

theorem EOps.map {α β : Type} {x : EngM α} {f : α → β} (hx : EOps S x) : EOps S (f <$> x) := by
  show EOps S (x >>= fun a => Pure.pure (f a))
  exact EOps.bind hx fun _ => EOps.pure _

theorem EOps.throw {α : Type} (e : Error) : EOps S (throw e : EngM α) := fun _ => OpsIn.pure _

theorem EOps.fail {α : Type} (e : Error) : EOps S (EngM.fail e : EngM α) := fun _ => OpsIn.pure _

theorem EOps.get : EOps S (get : EngM TxCtx) := fun _ => OpsIn.pure _

theorem EOps.set (c : TxCtx) : EOps S (set c : EngM PUnit) := fun _ => OpsIn.pure _

theorem EOps.modify (f : TxCtx → TxCtx) : EOps S (modify f : EngM PUnit) := fun _ => OpsIn.pure _

theorem EOps.modifyGet {α : Type} (f : TxCtx → α × TxCtx) : EOps S (modifyGet f : EngM α) :=
  fun _ => OpsIn.pure _

theorem EOps.report (f : TxReport → TxReport) : EOps S (EngM.report f) := fun _ => OpsIn.pure _

theorem EOps.op (o : Op) (h : S o) : EOps S (EngM.op o) := fun _ =>
  OpsIn.op o _ h fun _ => OpsIn.pure _

theorem EOps.rd (r : ROp) (h : S (.read r)) : EOps S (EngM.rd r) := EOps.op _ h

theorem toS_ops {α : Type} (hS : ∀ r, S (.read r)) : ∀ (p : RProg α), OpsIn S p.toS
  | .pure a => OpsIn.pure a
  | .read r k => OpsIn.op _ _ (hS r) fun x => toS_ops hS (k x)

theorem EOps.reads {α : Type} (hS : ∀ r, S (.read r)) (p : RProg α) : EOps S (EngM.reads p) := by
  intro ctx
  show OpsIn S (SProg.bind (SProg.bind p.toS fun a => SProg.pure (Except.ok a)) _)
  refine OpsIn.bind (OpsIn.bind (toS_ops hS p) fun _ => OpsIn.pure _) fun e => ?_
  rcases e with e | a <;> exact OpsIn.pure _

theorem EOps.ofExcept {α : Type} (e : Except Error α) : EOps S (EngM.ofExcept e) := by
  cases e <;> exact fun _ => OpsIn.pure _

theorem EOps.codec {α : Type} (pos : Position) (e : Except CodecError α) : EOps S (EngM.codec pos e) := by
  cases e <;> exact fun _ => OpsIn.pure _

theorem EOps.ite {α : Type} {c : Prop} [Decidable c] {x y : EngM α} (hx : EOps S x) (hy : EOps S y) :
    EOps S (if c then x else y) := by
  split <;> assumption

theorem EOps.forIn_list {α β : Type} (xs : List α) (b : β) {f : α → β → EngM (ForInStep β)}
    (hf : ∀ a b, EOps S (f a b)) : EOps S (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact EOps.pure _
  | cons x xs ih =>
    rw [List.forIn_cons]
    refine EOps.bind (hf x b) fun r => ?_
    cases r with
    | done b => exact EOps.pure _
    | yield b => exact ih b

theorem EOps.forIn_arr {α β : Type} (xs : Array α) (b : β) {f : α → β → EngM (ForInStep β)}
    (hf : ∀ a b, EOps S (f a b)) : EOps S (forIn xs b f) := by
  rw [← Array.forIn_toList]; exact EOps.forIn_list _ _ hf

theorem EOps.mapM {α β : Type} (xs : List α) {f : α → EngM β} (hf : ∀ a, EOps S (f a)) :
    EOps S (xs.mapM f) := by
  induction xs with
  | nil => exact EOps.pure _
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact EOps.bind (hf x) fun _ => EOps.bind ih fun _ => EOps.pure _

end

/-- A read-only engine computation. -/
abbrev ERO {α : Type} (x : EngM α) : Prop := EOps IsRead x

theorem isRead_read (r : ROp) : IsRead (.read r) := ⟨r, rfl⟩

/-- Runs an engine computation on the model. -/
def erun {α : Type} (x : EngM α) (ctx : TxCtx) (s : ModelStore) :
    Except StoreError (Except Error (α × TxCtx) × ModelStore) :=
  SProg.runModel ((x.run ctx).run) s

theorem ERO.store {α : Type} {x : EngM α} (h : ERO x) {ctx : TxCtx} {s s' : ModelStore}
    {r : Except Error (α × TxCtx)} (hr : erun x ctx s = .ok (r, s')) : s' = s :=
  readOnly_run (h ctx) hr

end Tiramemsu.Engine
