import OperatorKO7.Meta.NonlinearTransparentProjection

namespace OperatorKO7.NonlinearDominanceCriteria

open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.NonlinearDominanceWitnesses
open OperatorKO7.NonlinearResidualTaxonomy
open OperatorKO7.NonlinearTransparentProjection

/-- Exact theorem-visible criterion for closing a transparent bounded-polynomial row:
it is precisely the old boundary payload together with a concrete dominance witness class. -/
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

/-- The upgraded projection data forgets back to the original boundary exactly. -/
theorem transparentPolynomialDominanceCriterion_toProjectionData_boundary_exact
    (criterion : TransparentPolynomialDominanceCriterion) :
    criterion.toProjectionData.toBoundary = criterion.boundary := by
  cases criterion
  rfl

/-- The transparent row keeps its top-level projection-required status until the criterion is attached. -/
theorem transparentPolynomialDominanceCriterion_requires_projection_status
    (_criterion : TransparentPolynomialDominanceCriterion) :
    nonlinearResidualStatus .boundedDegreeDirectTransparentPolynomial =
      .requiresExistingTheoremProjection := by
  rfl

/-- Any dominance criterion witnesses that the boundary now carries the missing dominance data. -/
theorem transparentPolynomialDominanceCriterion_yields_boundaryDominanceData
    (criterion : TransparentPolynomialDominanceCriterion) :
    TransparentPolynomialProjectionBoundaryHasDominanceData criterion.boundary := by
  exact
    transparentPolynomialProjectionBoundary_hasDominanceData_of_witnessClass
      criterion.boundary criterion.witnessClass

/-- T.5: every transparent-row boundary in the concrete witness class closes unconditionally. -/
theorem transparent_polynomial_dominance_unconditional_for_class
    (boundary : TransparentPolynomialProjectionBoundary)
    (hwitness : TransparentDominanceWitnessClass boundary.measure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System boundary.measure.eval (· < ·) := by
  exact transparentPolynomialProjectionBoundary_with_witnessClass_is_blocked boundary hwitness

/-- T.6: universal unconditional closure for the transparent row over the concrete witness class. -/
theorem transparent_polynomial_dominance_universal_unconditional :
    ∀ boundary : TransparentPolynomialProjectionBoundary,
      TransparentDominanceWitnessClass boundary.measure →
        ¬ StepDuplicatingSchema.GlobalOrients ko7System boundary.measure.eval (· < ·) := by
  intro boundary hwitness
  exact transparent_polynomial_dominance_unconditional_for_class boundary hwitness

/-- Any dominance criterion closes the transparent row through the existing bounded polynomial barrier. -/
theorem transparentPolynomialDominanceCriterion_closes_transparent_row
    (criterion : TransparentPolynomialDominanceCriterion) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System criterion.boundary.measure.eval (· < ·) := by
  exact
    transparent_polynomial_dominance_unconditional_for_class
      criterion.boundary criterion.witnessClass

/-- Paper-facing catalog for the exact transparent-row dominance criteria. -/
abbrev TransparentPolynomialDominanceCriteriaCatalog : Prop :=
  ∀ criterion : TransparentPolynomialDominanceCriterion,
    nonlinearResidualStatus .boundedDegreeDirectTransparentPolynomial =
        .requiresExistingTheoremProjection
      ∧ TransparentPolynomialProjectionBoundaryHasDominanceData criterion.boundary
      ∧ TransparentDominanceWitnessClass criterion.boundary.measure
      ∧ ¬ StepDuplicatingSchema.GlobalOrients ko7System criterion.boundary.measure.eval (· < ·)

/-- Every theorem-visible dominance criterion closes the transparent row conditionally and nothing stronger. -/
theorem transparent_polynomial_dominance_criteria_catalog :
    TransparentPolynomialDominanceCriteriaCatalog := by
  intro criterion
  exact ⟨transparentPolynomialDominanceCriterion_requires_projection_status criterion,
    transparentPolynomialDominanceCriterion_yields_boundaryDominanceData criterion,
    criterion.witnessClass,
    transparentPolynomialDominanceCriterion_closes_transparent_row criterion⟩

/-- Backward-compatible alias for the exact conditional closure catalog used by the boundary layer. -/
abbrev TransparentPolynomialConditionalClosureCatalog : Prop :=
  TransparentPolynomialDominanceCriteriaCatalog

/-- Backward-compatible theorem alias for the exact conditional closure catalog. -/
theorem transparent_polynomial_conditional_closure_catalog :
    TransparentPolynomialConditionalClosureCatalog :=
  transparent_polynomial_dominance_criteria_catalog

end OperatorKO7.NonlinearDominanceCriteria
