/-
Row effects of engine steps. A light operation (read, intern, id allocation, `pred_multi`
upkeep, volatile write) changes no statement row; a non-inserting operation may in addition
only retract live statements at the current transaction. Lifted to engine computations
through their footprints, these say that the checks of the pipeline change no row and that the
cascade, retraction and uniqueness/cardinality steps only retract.
-/
import TiramemsuProofs.Store.Temporal
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec Tiramemsu.View EngM

--# @lat: [[verification#Proven Store State Machine]]

/-! ## Operation classes -/

/-- An operation that writes no statement row. -/
def Op.light : Op → Bool
  | .insert _ => false
  | .retract .. => false
  | _ => true

/-- An operation that inserts no statement row. -/
def Op.noIns : Op → Bool
  | .insert _ => false
  | _ => true

theorem noIns_of_light {o : Op} (h : o.light = true) : o.noIns = true := by
  cases o <;> simp_all [Op.light, Op.noIns]

/-- A computation whose operations are light. -/
abbrev LightE {α : Type} (x : EngM α) : Prop := EOps (fun o => o.light = true) x
/-- A computation whose operations insert nothing. -/
abbrev NoInsE {α : Type} (x : EngM α) : Prop := EOps (fun o => o.noIns = true) x

theorem EOps.mono' {S T : Op → Prop} (h : ∀ o, S o → T o) {α : Type} {x : EngM α} (hx : EOps S x) : EOps T x :=
  fun ctx => OpsIn.mono h (hx ctx)

theorem LightE.noIns {α : Type} {x : EngM α} (h : LightE x) : NoInsE x := EOps.mono' (fun _ => noIns_of_light) h

theorem ERO.light {α : Type} {x : EngM α} (h : ERO x) : LightE x :=
  EOps.mono' (fun o ho => by obtain ⟨r, rfl⟩ := ho; rfl) h

theorem ERO.noIns {α : Type} {x : EngM α} (h : ERO x) : NoInsE x := h.light.noIns

/-! ## Row effects of single operations -/

/-- Same statement rows and committed state. -/
def SameRows (s s' : ModelStore) : Prop :=
  s'.current.triples = s.current.triples ∧ s'.committed = s.committed

theorem setCounter_triples {st c : ModelState} {n : String} {v : Int64} (h : st.setCounter n v = .ok c) :
    c.triples = st.triples := by
  unfold ModelState.setCounter at h; cases h; rfl

theorem insertTerm_triples {st c : ModelState} {r : TermRow} (h : st.insertTerm r = .ok c) :
    c.triples = st.triples := by
  unfold ModelState.insertTerm at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

theorem light_same (o : Op) (ho : o.light = true) {s s' : ModelStore} {x : o.Res}
    (h : (Op.run o : ModelM o.Res) s = .ok (x, s')) : SameRows s s' := by
  cases o with
  | read r => obtain ⟨rfl, _⟩ := read_same h; exact ⟨rfl, rfl⟩
  | alloc c =>
    rcases alloc_spec h with rfl | ⟨_, n, cur, _, _, _, hc, rfl, _⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨setCounter_triples hc, rfl⟩
  | insert r => cases ho
  | retract e k => cases ho
  | intern k num =>
    rcases intern_spec h with rfl | ⟨_, _, _, c1, c2, _, _, h1, h2, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨(setCounter_triples h2).trans (insertTerm_triples h1), rfl⟩
  | volPut r =>
    obtain ⟨w, rfl⟩ := volPut_only h; exact ⟨rfl, rfl⟩
  | volDel a k =>
    obtain ⟨w, rfl⟩ := volDel_only h; exact ⟨rfl, rfl⟩
  | markMulti p =>
    rcases markMulti_spec h with rfl | ⟨_, c1, c2, v, h1, h2, rfl⟩
    · exact ⟨rfl, rfl⟩
    · unfold ModelState.addPredMulti at h1; cases h1
      exact ⟨by rw [setCounter_triples h2], rfl⟩

/-- The transaction number a row written now gets. -/
def tOf (s : ModelStore) : Int64 := (s.committed.counter "last_t").getD 0 + 1

/-- A row unchanged, or a live row retracted at `t`. -/
def RetStep (t : Int64) (r r' : TripleRow) : Prop :=
  r' = r ∨ (r.tRet = none ∧ ∃ k, r' = { r with tRet := some t, retKind := some k })

/-- Same committed state; every row unchanged or a live row retracted at the current
transaction; no row added or removed. -/
def RetOnly (s s' : ModelStore) : Prop :=
  s'.committed = s.committed ∧ List.Forall₂ (RetStep (tOf s)) s.current.triples s'.current.triples

def Uniq (s : ModelStore) : Prop := s.current.triples.Pairwise fun a b => a.eid ≠ b.eid

/-- The relation a non-inserting run keeps (on unique-eid states). -/
def NoInsRel (s s' : ModelStore) : Prop := Uniq s → RetOnly s s' ∧ Uniq s'

theorem RetStep.trans {t : Int64} {a b c : TripleRow} (h1 : RetStep t a b) (h2 : RetStep t b c) : RetStep t a c := by
  rcases h1 with rfl | ⟨ha, k, rfl⟩
  · exact h2
  · rcases h2 with rfl | ⟨hb, _, _⟩
    · exact Or.inr ⟨ha, k, rfl⟩
    · cases hb

theorem forall₂_retStep_eid {t : Int64} : ∀ {l m : List TripleRow}, List.Forall₂ (RetStep t) l m →
    l.map (·.eid) = m.map (·.eid)
  | [], [], _ => rfl
  | a :: l, b :: m, List.Forall₂.cons h r => by
    simp only [List.map_cons, forall₂_retStep_eid r]
    rcases h with rfl | ⟨_, k, rfl⟩ <;> rfl

theorem uniq_of_eids {l m : List TripleRow} (h : l.map (·.eid) = m.map (·.eid))
    (hu : l.Pairwise fun a b => a.eid ≠ b.eid) : m.Pairwise fun a b => a.eid ≠ b.eid := by
  have : (l.map (·.eid)).Pairwise (· ≠ ·) := List.pairwise_map.2 hu
  rw [h] at this
  exact List.pairwise_map.1 this

theorem NoInsRel.refl (s : ModelStore) : NoInsRel s s :=
  fun hu => ⟨⟨rfl, List.forall₂_same.2 fun _ _ => Or.inl rfl⟩, hu⟩

theorem NoInsRel.trans {a b c : ModelStore} (h1 : NoInsRel a b) (h2 : NoInsRel b c) : NoInsRel a c := by
  intro hu
  obtain ⟨⟨c1, f1⟩, hb⟩ := h1 hu
  obtain ⟨⟨c2, f2⟩, hc⟩ := h2 hb
  have ht : tOf b = tOf a := by unfold tOf; rw [c1]
  rw [ht] at f2
  exact ⟨⟨c2.trans c1, forall₂_trans (R := RetStep (tOf a)) (S := RetStep (tOf a)) (T := RetStep (tOf a))
    (fun _ _ _ h h' => RetStep.trans h h') f1 f2⟩, hc⟩

theorem noIns_rel (o : Op) (ho : o.noIns = true) {s s' : ModelStore} {x : o.Res}
    (h : (Op.run o : ModelM o.Res) s = .ok (x, s')) : NoInsRel s s' := by
  by_cases hl : o.light = true
  · obtain ⟨h1, h2⟩ := light_same o hl h
    intro hu
    refine ⟨⟨h2, ?_⟩, by unfold Uniq; rw [h1]; exact hu⟩
    rw [h1]; exact List.forall₂_same.2 fun _ _ => Or.inl rfl
  · cases o with
    | insert r => cases ho
    | retract e k =>
      have h' : (retractRun e k : ModelM Bool) s = .ok (x, s') := h
      obtain ⟨lastT, hlt, -, -, hcase⟩ := retract_spec' h'
      rcases hcase with ⟨-, rfl, -⟩ | ⟨-, -, r, ht, hl', rfl⟩
      · exact NoInsRel.refl _
      · intro hu
        have htOf : tOf s = lastT + 1 := by unfold tOf; rw [hlt]; rfl
        obtain ⟨hr, he⟩ := triple_some ht
        have hf : List.Forall₂ (RetStep (tOf s)) s.current.triples
            (s.current.triples.map (Store.retractRow e (lastT + 1) k.code)) := by
          rw [List.forall₂_map_right_iff]
          refine List.forall₂_same.2 fun y hy => ?_
          unfold Store.retractRow
          by_cases hye : y.eid = e
          · have hy' : y = r := by
              have := triple_of_mem hu hy
              rw [hye, ht] at this; exact (Option.some.inj this).symm
            subst hy'
            simp only [hye, beq_self_eq_true, if_true]
            exact Or.inr ⟨hl', k.code, by rw [htOf, hye]⟩
          · have : (y.eid == e) = false := by simpa using hye
            simp only [this]; exact Or.inl rfl
        exact ⟨⟨rfl, hf⟩, uniq_of_eids (forall₂_retStep_eid hf) hu⟩
    | _ => simp [Op.light] at hl

/-! ## Row effects of engine computations -/

theorem LightE.rows {α : Type} {x : EngM α} (hx : LightE x) {ctx : TxCtx} {s s' : ModelStore}
    {r : Except Error (α × TxCtx)} (h : erun x ctx s = .ok (r, s')) : SameRows s s' :=
  OpsIn.run (R := SameRows) (fun _ => ⟨rfl, rfl⟩)
    (fun _ _ _ h1 h2 => ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩)
    (fun o ho _ _ _ hr => light_same o ho hr) (hx ctx) h

theorem NoInsE.rows {α : Type} {x : EngM α} (hx : NoInsE x) {ctx : TxCtx} {s s' : ModelStore}
    {r : Except Error (α × TxCtx)} (h : erun x ctx s = .ok (r, s')) : NoInsRel s s' :=
  OpsIn.run (R := NoInsRel) NoInsRel.refl (fun _ _ _ h1 h2 => h1.trans h2)
    (fun o ho _ _ _ hr => noIns_rel o ho hr) (hx ctx) h

/-! ## Footprints of the engine steps -/

macro "fp_step" : tactic => `(tactic| first
  | apply EOps.bind
  | exact EOps.pure _ | apply EOps.pure | apply EOps.throw | apply EOps.fail | apply EOps.get
  | apply EOps.set | apply EOps.modify | apply EOps.modifyGet | apply EOps.report
  | apply EOps.ofExcept | apply EOps.codec
  | exact EOps.reads (fun _ => rfl) _
  | exact EOps.op _ rfl
  | apply EOps.forIn_list
  | apply EOps.forIn_arr
  | apply EOps.mapM
  | split
  | dsimp only
  | (refine fun _ => ?_)
  | assumption)

theorem light_sysLookup (i : String) : LightE (sysLookup i) := (ero_sysLookup i).light
theorem light_liveOfS (p : ObjectId) : LightE (liveOfS p) := (ero_liveOfS p).light
theorem light_liveOfSP (s p : ObjectId) : LightE (liveOfSP s p) := (ero_liveOfSP s p).light
theorem light_liveOfP (p : ObjectId) : LightE (liveOfP p) := (ero_liveOfP p).light
theorem light_iriOf (x : ObjectId) : LightE (iriOf x) := (ero_iriOf x).light
theorem light_tagOf (x : ObjectId) (pos : Position) : LightE (tagOf x pos) := (ero_tagOf x pos).light
theorem light_originOk (x : ObjectId) : LightE (originOk x) := (ero_originOk x).light
theorem light_live (x : ObjectId) : LightE (live x) := (ero_live x).light
theorem light_isMembership (x : ObjectId) : LightE (isMembership x) := (ero_isMembership x).light
theorem light_subjectTypeRows (x : ObjectId) : LightE (subjectTypeRows x) := (ero_subjectTypeRows x).light
theorem light_tagsOf (x : List ObjectId) : LightE (tagsOf x) := (ero_tagsOf x).light
theorem light_subjectTypeViolations (x : ObjectId) (t : List Tag) : LightE (subjectTypeViolations x t) :=
  (ero_subjectTypeViolations x t).light
theorem light_validateFlagRetraction (e : ObjectId) : LightE (validateFlagRetraction e) :=
  (ero_validateFlagRetraction e).light

theorem light_internKey (k : TermKey) (num : Option UInt64) (pos : Position) : LightE (EngM.internKey k num pos) := by
  unfold EngM.internKey; repeat fp_step
theorem light_internValue (v : Value) (pos : Position) : LightE (internValue v pos) := by
  unfold internValue; repeat (first | with_reducible apply light_internKey | fp_step)
theorem light_sys (i : String) : LightE (sys i) := by
  unfold sys; repeat (first | with_reducible apply light_internKey | fp_step)
theorem light_checkKnown (x : ObjectId) (pos : Position) : LightE (checkKnown x pos) := by
  unfold checkKnown; repeat (first | with_reducible apply light_tagOf | fp_step)
theorem light_checkPositions (s p o : ObjectId) : LightE (checkPositions s p o) := by
  unfold checkPositions
  repeat (first | with_reducible apply light_tagOf | with_reducible apply light_originOk | with_reducible apply light_checkKnown | fp_step)
theorem light_idIn (x : ObjectId) : LightE (idIn x) := by
  unfold idIn; repeat (first | with_reducible apply light_tagOf | with_reducible apply light_originOk | fp_step)
theorem light_schema (p : ObjectId) : LightE (schema p) := by
  unfold schema; repeat (first | with_reducible apply light_sysLookup | with_reducible apply light_liveOfS | fp_step)
theorem light_matchesValueType (vt o : ObjectId) : LightE (matchesValueType vt o) := by
  unfold matchesValueType; repeat (first | with_reducible apply light_iriOf | with_reducible apply light_tagOf | fp_step)
theorem light_checkValueType (p o : ObjectId) : LightE (checkValueType p o) := by
  unfold checkValueType
  repeat (first | with_reducible apply light_schema | with_reducible apply light_matchesValueType | with_reducible apply light_tagOf | fp_step)
theorem light_checkSubjectType (p s : ObjectId) : LightE (checkSubjectType p s) := by
  unfold checkSubjectType
  repeat (first | with_reducible apply light_schema | with_reducible apply light_tagOf | with_reducible apply light_tagsOf | fp_step)
theorem light_validateFlag (f : Flag) (fp s o : ObjectId) : LightE (validateFlag f fp s o) := by
  unfold validateFlag
  repeat (first | with_reducible apply light_tagOf | with_reducible apply light_iriOf | with_reducible apply light_sys | fp_step)
theorem light_validateSchemaChange (f : Flag) (x o : ObjectId) (r : Option ObjectId) :
    LightE (validateSchemaChange f x o r) := by
  unfold validateSchemaChange
  repeat (first | with_reducible apply light_iriOf | with_reducible apply light_liveOfP | with_reducible apply light_matchesValueType | with_reducible apply light_subjectTypeRows | with_reducible apply light_subjectTypeViolations | with_reducible apply light_tagsOf | fp_step)
theorem light_findOverlapping (s p o : ObjectId) (v : Valid) : LightE (findOverlapping s p o v) := by
  unfold findOverlapping; repeat fp_step
theorem light_allocEid : LightE allocEid := by unfold allocEid; repeat fp_step
theorem light_overlappingOthers (s p o : ObjectId) (v : Valid) : LightE (overlappingOthers s p o v) := by
  unfold overlappingOthers; repeat (first | with_reducible apply light_liveOfSP | fp_step)
theorem light_cascadeSet (root : ObjectId) : LightE (cascadeSet root) := by
  unfold cascadeSet; repeat fp_step
theorem noIns_retractRow (e : ObjectId) (k : RetKind) : NoInsE (EngM.retractRow e k) := by
  unfold EngM.retractRow; repeat (first | with_reducible apply (light_isMembership _).noIns | fp_step)
theorem noIns_retractRoot (e : ObjectId) (k : RetKind) : NoInsE (retractRoot e k) := by
  unfold retractRoot
  repeat (first | with_reducible apply (light_originOk _).noIns | with_reducible apply (light_live _).noIns | with_reducible apply (light_validateFlagRetraction _).noIns | with_reducible apply (light_cascadeSet _).noIns | with_reducible apply noIns_retractRow | fp_step)
theorem noIns_uniqueAndCardinality (s p o : ObjectId) (v : Valid) (f : Bool) :
    NoInsE (uniqueAndCardinality s p o v f) := by
  unfold uniqueAndCardinality
  repeat (first | with_reducible apply (light_schema _).noIns | with_reducible apply (light_overlappingOthers _ _ _ _).noIns | with_reducible apply noIns_retractRoot | fp_step)

end Tiramemsu.Engine
