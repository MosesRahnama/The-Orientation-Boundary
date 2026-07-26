import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.RepairSemantics

/-!
# Typed witness-language adequacy

The least witness grade is derived from a carrier of concrete witnesses.  A
semantic model receives a certificate only when its stored graded adequacy is
extensionally equal to the carrier-derived adequacy and its scope records the
same language kind and least grade.

## Audit slots

Relation: inherited from the certified semantic model.
Closure: upward closure in the natural-number language grade.
Trust: kernel-only; rank extraction uses the existing `Nat.find` surface.
Scope: typed finite or infinite witness carriers with a natural-number grade.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u v w z

/-- A witness language with concrete witness terms and their least required
grade. -/
structure WitnessLanguageModel where
  Witness : Type z
  kind : WitnessLanguageKind
  grade : Witness → Nat
  adequateWitness : Witness → Prop
  inhabited : ∃ witness, adequateWitness witness

namespace WitnessLanguageModel

/-- Grade `n` is adequate when it can express one adequate witness whose own
grade is at most `n`. -/
def adequateAt (model : WitnessLanguageModel) (n : Nat) : Prop :=
  ∃ witness, model.adequateWitness witness ∧ model.grade witness ≤ n

/-- The concrete language induces an upward-closed graded adequacy object. -/
def toGradedAdequacy (model : WitnessLanguageModel) : GradedAdequacy where
  adequate := model.adequateAt
  upward := by
    intro i j hij hi
    rcases hi with ⟨w, hw, hgrade⟩
    exact ⟨w, hw, hgrade.trans hij⟩
  inhabited := by
    rcases model.inhabited with ⟨w, hw⟩
    exact ⟨model.grade w, w, hw, le_rfl⟩

end WitnessLanguageModel

/-- The stored semantic witness profile is the image of a typed witness
language, and the scope records its kind and least adequate grade. -/
structure WitnessLanguageAdequacy
    {A : ARS.{u}} [Fintype A.Carrier]
    {Defect : Type v} {Action : Type w}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (data : SemanticConstructionData A Defect Action) where
  model : WitnessLanguageModel
  language_kind_eq : data.scope.witnessLanguage = model.kind
  adequate_iff : ∀ n,
    data.witnessAdequacy.adequate n ↔ model.adequateAt n
  scope_grade_eq :
    data.scope.witnessGrade = witnessRank data.witnessAdequacy

namespace WitnessLanguageAdequacy

variable {A : ARS.{u}} [Fintype A.Carrier]
variable {Defect : Type v} {Action : Type w}
variable [DecidableEq Defect] [Fintype Action] [DecidableEq Action]

/-- The scope grade is adequate in the concrete witness language. -/
theorem scope_grade_adequate
    {data : SemanticConstructionData A Defect Action}
    (certificate : WitnessLanguageAdequacy data) :
    certificate.model.adequateAt data.scope.witnessGrade := by
  rw [certificate.scope_grade_eq]
  exact (certificate.adequate_iff _).mp
    (witnessRank_adequate data.witnessAdequacy)

/-- Every lower grade is inadequate in the concrete witness language. -/
theorem below_scope_grade_inadequate
    {data : SemanticConstructionData A Defect Action}
    (certificate : WitnessLanguageAdequacy data) {n : Nat}
    (hn : n < data.scope.witnessGrade) :
    ¬ certificate.model.adequateAt n := by
  rw [certificate.scope_grade_eq] at hn
  intro h
  exact not_adequate_below_witnessRank data.witnessAdequacy hn
    ((certificate.adequate_iff n).mpr h)

#check @scope_grade_adequate
#check @below_scope_grade_inadequate
#print axioms scope_grade_adequate
#print axioms below_scope_grade_inadequate

end WitnessLanguageAdequacy
end OperatorKO7.Meta.LicensedBoundaryCalculus
