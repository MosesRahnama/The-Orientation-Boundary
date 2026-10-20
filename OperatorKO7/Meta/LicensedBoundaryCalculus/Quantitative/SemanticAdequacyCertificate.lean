import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.AlternativeCarrier

/-!
# Certified semantic construction data

`SemanticConstructionData` is a computation record: it can compute a profile
from supplied finite fields.  `SemanticAdequacyCertificate` is the separate
proof object showing that those fields denote the actual scoped relation,
actual local defects, concrete repairs, a typed witness language, and the
actual reachable terminal alternatives.

## Audit slots

Relation: exact equality, pointwise, with a partial morphism's admitted edges.
Closure: local normalization, actual peak resolution, and terminal reachability.
Trust: kernel-only; no external citations or physical interpretation.
Scope: one finite semantic scope and one partial licensed-reduction morphism.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u v d a

/-- A proof that every manuscript-facing coordinate of a finite semantic
profile is backed by the relation and concrete carriers named by the scope. -/
structure SemanticAdequacyCertificate
    {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (F : PartialLicensedReductionMorphism A B)
    (data : SemanticConstructionData A Defect Action) where
  relationExact : ∀ x y, data.scope.relation x y ↔ F.admitted x y
  normalizing : NormalizingAt data.scope.relation data.scope.source
  defects : DefectAdequacy data
  repairs : RepairSemantics data defects
  witnesses : WitnessLanguageAdequacy data
  alternatives : AlternativeCarrier data

namespace SemanticAdequacyCertificate

variable {A : ARS.{u}} {B : ARS.{v}}
variable [Fintype A.Carrier] [Fintype B.Carrier]
variable {Defect : Type d} {Action : Type a}
variable [DecidableEq Defect] [Fintype Action] [DecidableEq Action]

/-- Certified semantic data has exactly the terminal multiplicity carried by
its concrete alternative type. -/
theorem terminalMultiplicity_eq_alternative_card
    {F : PartialLicensedReductionMorphism A B}
    {data : SemanticConstructionData A Defect Action}
    (certificate : SemanticAdequacyCertificate F data) :
    (semanticProfile data).terminalMultiplicity =
      Fintype.card certificate.alternatives.Alternative := by
  change data.scope.terminalMultiplicity =
    Fintype.card certificate.alternatives.Alternative
  rw [← certificate.alternatives.fixed_count_eq_terminalMultiplicity]
  exact certificate.alternatives.fixed_count_eq

/-- The profile's defect coordinate counts an irredundant complete vocabulary
of actual source-local non-joinable peaks. -/
theorem criticalPairDefect_eq_certified_defect_card
    {F : PartialLicensedReductionMorphism A B}
    {data : SemanticConstructionData A Defect Action}
    (_certificate : SemanticAdequacyCertificate F data) :
    (semanticProfile data).criticalPairDefect = data.defects.card :=
  rfl

/-- Every defect counted by a certified profile denotes an actual local peak. -/
theorem counted_defect_is_actual
    {F : PartialLicensedReductionMorphism A B}
    {data : SemanticConstructionData A Defect Action}
    (certificate : SemanticAdequacyCertificate F data)
    {d : Defect} (hd : d ∈ data.defects) :
    ∃ actual : ActualLocalDefect data.scope,
      certificate.defects.endpoints d = (actual.left, actual.right) :=
  certificate.defects.sound d hd

/-- The guarded Hartley coordinate is defined for every certified profile. -/
theorem terminalHartley_defined
    {F : PartialLicensedReductionMorphism A B}
    {data : SemanticConstructionData A Defect Action}
    (certificate : SemanticAdequacyCertificate F data) :
    ∃ h : Real, (semanticProfile data).terminalHartley = some h :=
  semanticProfile_terminalHartley_defined data certificate.normalizing

#check @terminalMultiplicity_eq_alternative_card
#check @criticalPairDefect_eq_certified_defect_card
#check @counted_defect_is_actual
#check @terminalHartley_defined
#print axioms terminalMultiplicity_eq_alternative_card
#print axioms criticalPairDefect_eq_certified_defect_card
#print axioms counted_defect_is_actual
#print axioms terminalHartley_defined

end SemanticAdequacyCertificate
end OperatorKO7.Meta.LicensedBoundaryCalculus
