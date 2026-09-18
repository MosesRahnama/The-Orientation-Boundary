import OperatorKO7.Meta.NonlinearTransparentProjection

namespace OperatorKO7.NonlinearDominanceCriteria

open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.NonlinearDominanceWitnesses
open OperatorKO7.NonlinearResidualTaxonomy
open OperatorKO7.NonlinearTransparentProjection

/-- A transparent boundary paired with a `TransparentDominanceWitnessClass` assumption. -/
structure TransparentPolynomialDominanceCriterion where
  boundary : TransparentPolynomialProjectionBoundary
  witnessClass : TransparentDominanceWitnessClass boundary.measure

/-- Any dominance criterion upgrades the transparent boundary to full projection data. -/
def TransparentPolynomialDominanceCriterion.toProjectionData
    (criterion : TransparentPolynomialDominanceCriterion) : TransparentPolynomialProjectionData :=
  { measure := criterion.boundary.measure
    transparentAtBase := criterion.boundary.transparentAtBase
    unbounded := criterion.boundary.unbounded
    dominance :=
      transparent_dominance_witness_class_eventually_dominated_at_base
        criterion.boundary.measure criterion.witnessClass }

/-- Forgetting the added dominance proof recovers the original boundary. -/
theorem transparentPolynomialDominanceCriterion_toProjectionData_boundary_exact
    (criterion : TransparentPolynomialDominanceCriterion) :
    criterion.toProjectionData.toBoundary = criterion.boundary := by
  cases criterion
  rfl

/-- The imported status function labels this row `requiresExistingTheoremProjection`. -/
theorem transparentPolynomialDominanceCriterion_requires_projection_status
    (_criterion : TransparentPolynomialDominanceCriterion) :
    nonlinearResidualStatus .boundedDegreeDirectTransparentPolynomial =
      .requiresExistingTheoremProjection := by
  rfl

/-- The witness-class assumption supplies the imported dominance-data predicate. -/
theorem transparentPolynomialDominanceCriterion_yields_boundaryDominanceData
    (criterion : TransparentPolynomialDominanceCriterion) :
    TransparentPolynomialProjectionBoundaryHasDominanceData criterion.boundary := by
  exact
    transparentPolynomialProjectionBoundary_hasDominanceData_of_witnessClass
      criterion.boundary criterion.witnessClass

/-- A transparent boundary is blocked when supplied with a `TransparentDominanceWitnessClass`
hypothesis. -/
theorem transparent_polynomial_dominance_unconditional_for_class
    (boundary : TransparentPolynomialProjectionBoundary)
    (hwitness : TransparentDominanceWitnessClass boundary.measure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System boundary.measure.eval (· < ·) := by
  exact transparentPolynomialProjectionBoundary_with_witnessClass_is_blocked boundary hwitness

/-- Pointwise restatement of the preceding conditional theorem for all transparent boundaries. -/
theorem transparent_polynomial_dominance_universal_unconditional :
    ∀ boundary : TransparentPolynomialProjectionBoundary,
      TransparentDominanceWitnessClass boundary.measure →
        ¬ StepDuplicatingSchema.GlobalOrients ko7System boundary.measure.eval (· < ·) := by
  intro boundary hwitness
  exact transparent_polynomial_dominance_unconditional_for_class boundary hwitness

/-- The criterion's stored witness-class hypothesis yields failure of global orientation. -/
theorem transparentPolynomialDominanceCriterion_closes_transparent_row
    (criterion : TransparentPolynomialDominanceCriterion) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System criterion.boundary.measure.eval (· < ·) := by
  exact
    transparent_polynomial_dominance_unconditional_for_class
      criterion.boundary criterion.witnessClass

/-- Conditional catalog over supplied `TransparentPolynomialDominanceCriterion` values. -/
abbrev TransparentPolynomialDominanceCriteriaCatalog : Prop :=
  ∀ criterion : TransparentPolynomialDominanceCriterion,
    nonlinearResidualStatus .boundedDegreeDirectTransparentPolynomial =
        .requiresExistingTheoremProjection
      ∧ TransparentPolynomialProjectionBoundaryHasDominanceData criterion.boundary
      ∧ TransparentDominanceWitnessClass criterion.boundary.measure
      ∧ ¬ StepDuplicatingSchema.GlobalOrients ko7System criterion.boundary.measure.eval (· < ·)

/-- Collect the status equality, dominance-data proposition, stored witness class, and blocking result. -/
theorem transparent_polynomial_dominance_criteria_catalog :
    TransparentPolynomialDominanceCriteriaCatalog := by
  intro criterion
  exact ⟨transparentPolynomialDominanceCriterion_requires_projection_status criterion,
    transparentPolynomialDominanceCriterion_yields_boundaryDominanceData criterion,
    criterion.witnessClass,
    transparentPolynomialDominanceCriterion_closes_transparent_row criterion⟩

/-- Alias for `TransparentPolynomialDominanceCriteriaCatalog`. -/
abbrev TransparentPolynomialConditionalClosureCatalog : Prop :=
  TransparentPolynomialDominanceCriteriaCatalog

/-- The alias is inhabited by `transparent_polynomial_dominance_criteria_catalog`. -/
theorem transparent_polynomial_conditional_closure_catalog :
    TransparentPolynomialConditionalClosureCatalog :=
  transparent_polynomial_dominance_criteria_catalog

end OperatorKO7.NonlinearDominanceCriteria
