/-
Evidence carriers for the B7 hypothesis-necessity catalog of the Orientation Boundary.

Relation: the row's own acceptance predicate for the free duplicating rule.
Property: necessity of one premise or one defining feature, stated by a concrete datum.
-/
import Mathlib.Logic.Function.Basic

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.HypothesisNecessity

universe u v

/-- The four necessity classes of a method row. -/
inductive RowNecessityKind where
  | deletedBarrierPremise
  | lawFreeBarrierControl
  | deletedEscapeFeature
  | noApplicableHypothesis
  deriving DecidableEq, Repr

/-! ## Barrier rows with a removable premise -/

/-- A datum that keeps every law except the deleted clause, violates the deleted clause, and is
accepted by the method. -/
structure DeletedPremiseCountermodel {D : Sort u} (Other Deleted Accepts : D → Prop) where
  datum : D
  other : Other datum
  deletedFails : ¬ Deleted datum
  accepts : Accepts datum

/-- A deleted-premise countermodel refutes the barrier stated with that premise removed. -/
theorem DeletedPremiseCountermodel.refutes_deleted_barrier {D : Sort u}
    {Other Deleted Accepts : D → Prop} (C : DeletedPremiseCountermodel Other Deleted Accepts) :
    ¬ ∀ M : D, Other M → ¬ Accepts M :=
  fun h => h C.datum C.other C.accepts

/-- Necessity of one law clause of a barrier row: the laws split exactly into the retained part
and the deleted clause, the barrier holds under the full laws, and a countermodel refutes it
under the retained part alone. -/
def BarrierPremiseNecessity {D : Sort u} (Laws Other Deleted Accepts : D → Prop) : Prop :=
  (∀ M : D, Laws M ↔ Other M ∧ Deleted M) ∧
    (∀ M : D, Laws M → ¬ Accepts M) ∧
    Nonempty (DeletedPremiseCountermodel Other Deleted Accepts)

theorem BarrierPremiseNecessity.retained_barrier_false {D : Sort u}
    {Laws Other Deleted Accepts : D → Prop}
    (h : BarrierPremiseNecessity Laws Other Deleted Accepts) :
    ¬ ∀ M : D, Other M → ¬ Accepts M := by
  obtain ⟨-, -, ⟨C⟩⟩ := h
  exact C.refutes_deleted_barrier

/-! ## Barrier rows without a removable premise -/

/-- A barrier whose laws hold for every datum, together with a nonduplicating control that the
same method accepts. The control is a proposition about the method's own acceptance of a rule
without a duplicated variable. -/
def LawFreeBarrierNecessity {D : Sort u} (Laws Accepts : D → Prop) (Control : Prop) : Prop :=
  (∀ M : D, Laws M) ∧ (∀ M : D, ¬ Accepts M) ∧ Control

/-- A barrier that holds for every datum, including data that violate the laws, with satisfiable
laws and a nonduplicating control accepted by the same method. Deleting any set of law clauses
leaves the barrier true, so no single clause is a removable premise. -/
def UniversalBarrierNecessity {D : Sort u} (Laws Accepts : D → Prop) (Control : Prop) : Prop :=
  (∃ M : D, Laws M) ∧ (∀ M : D, ¬ Accepts M) ∧ Control

/-- A universal barrier refutes every deleted-premise countermodel, for every split of the laws. -/
theorem UniversalBarrierNecessity.no_deleted_premise_countermodel {D : Sort u}
    {Laws Accepts : D → Prop} {Control : Prop}
    (h : UniversalBarrierNecessity Laws Accepts Control) (Other Deleted : D → Prop) :
    ¬ Nonempty (DeletedPremiseCountermodel Other Deleted Accepts) := by
  rintro ⟨C⟩
  exact h.2.1 C.datum C.accepts

/-- A barrier whose laws split into two parts, each of which forces the barrier alone, together
with satisfiable laws and a nonduplicating control accepted by the same method. Every single
clause lies in one part, so deleting it leaves the other part and the barrier. -/
def CoveredBarrierNecessity {D : Sort u} (Laws PartA PartB Accepts : D → Prop) (Control : Prop) :
    Prop :=
  (∀ M : D, Laws M ↔ PartA M ∧ PartB M) ∧ (∃ M : D, Laws M) ∧
    (∀ M : D, PartA M → ¬ Accepts M) ∧ (∀ M : D, PartB M → ¬ Accepts M) ∧ Control

/-- Under a covered barrier, deleting a clause from either part leaves a barrier. -/
theorem CoveredBarrierNecessity.barrier_of_partA {D : Sort u} {Laws PartA PartB Accepts : D → Prop}
    {Control : Prop} (h : CoveredBarrierNecessity Laws PartA PartB Accepts Control) (M : D)
    (hA : PartA M) : ¬ Accepts M :=
  h.2.2.1 M hA

theorem CoveredBarrierNecessity.barrier_of_partB {D : Sort u} {Laws PartA PartB Accepts : D → Prop}
    {Control : Prop} (h : CoveredBarrierNecessity Laws PartA PartB Accepts Control) (M : D)
    (hB : PartB M) : ¬ Accepts M :=
  h.2.2.2.1 M hB

/-! ## Escape rows with a defining feature -/

/-- A single named feature of the data, read by `get` and replaced by `set`. The lens laws state
that `set` changes that feature and nothing else. -/
structure FeatureLens (D : Sort u) (V : Sort v) where
  get : D → V
  set : D → V → D
  get_set : ∀ M v, get (set M v) = v
  set_get : ∀ M, set M (get M) = M
  set_set : ∀ M v w, set (set M v) w = set M w

/-- An accepted lawful datum and a replacement value of one feature such that the changed datum
still satisfies every law and the method rejects it. -/
structure FeatureChangeControl {D : Sort u} {V : Sort v} (Laws Accepts : D → Prop)
    (L : FeatureLens D V) where
  base : D
  baseLaws : Laws base
  baseAccepts : Accepts base
  value : V
  valueDiffers : value ≠ L.get base
  changedLaws : Laws (L.set base value)
  changedRejects : ¬ Accepts (L.set base value)

/-- Only the named feature separates the accepted datum from the rejected one. -/
theorem FeatureChangeControl.restore {D : Sort u} {V : Sort v} {Laws Accepts : D → Prop}
    {L : FeatureLens D V} (C : FeatureChangeControl Laws Accepts L) :
    L.set (L.set C.base C.value) (L.get C.base) = C.base := by
  rw [L.set_set, L.set_get]

/-- Necessity of a defining feature of an escape row. -/
def EscapeFeatureNecessity {D : Sort u} {V : Sort v} (Laws Accepts : D → Prop)
    (L : FeatureLens D V) : Prop :=
  Nonempty (FeatureChangeControl Laws Accepts L)

/-! ## Rows with no applicable hypothesis -/

/-- Closed reasons for a row without a removable premise or feature. -/
inductive NoHypothesisReason where
  /-- The laws determine acceptance: all lawful data agree on the verdict. -/
  | lawsDetermineVerdict
  deriving DecidableEq, Repr

/-- Meaning of each reason. -/
def NoHypothesisReason.Holds {D : Sort u} (Laws Accepts : D → Prop) :
    NoHypothesisReason → Prop
  | .lawsDetermineVerdict =>
      (∃ M : D, Laws M) ∧ ∀ M M' : D, Laws M → Laws M' → (Accepts M ↔ Accepts M')

/-- No applicable hypothesis: the stated reason holds, so no lawful datum changes the verdict. -/
def NoApplicableHypothesis {D : Sort u} (Laws Accepts : D → Prop)
    (reason : NoHypothesisReason) : Prop :=
  reason.Holds Laws Accepts

/-- Under `lawsDetermineVerdict`, no lawful datum separates acceptance from rejection, so no
feature-change control exists for any lens. -/
theorem NoApplicableHypothesis.no_feature_control {D : Sort u} {V : Sort v}
    {Laws Accepts : D → Prop}
    (h : NoApplicableHypothesis Laws Accepts .lawsDetermineVerdict) (L : FeatureLens D V) :
    ¬ EscapeFeatureNecessity Laws Accepts L := by
  rintro ⟨C⟩
  exact C.changedRejects ((h.2 C.base _ C.baseLaws C.changedLaws).mp C.baseAccepts)

/-! ## Controls on the carriers -/

/-- Point update of a function at one argument is a feature lens. -/
def pointLens {α : Type u} {β : Type v} [DecidableEq α] (a : α) : FeatureLens (α → β) β where
  get f := f a
  set f v := Function.update f a v
  get_set f v := by simp
  set_get f := by simp
  set_set f v w := by simp

end OperatorKO7.Methods.OrientationClosure.HypothesisNecessity
