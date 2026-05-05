import OperatorKO7.Meta.NonlinearResidualTaxonomy
import OperatorKO7.Meta.NonlinearDominanceWitnesses
import OperatorKO7.Meta.PolynomialBarrierGeneral
import OperatorKO7.Meta.EscapeTrichotomy_Schema

namespace OperatorKO7.NonlinearTransparentProjection

open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.NonlinearDominanceWitnesses
open OperatorKO7.NonlinearResidualTaxonomy

/-- Boundary payload currently available for the transparent bounded-degree polynomial row. -/
structure TransparentPolynomialProjectionBoundary where
  measure : StepDuplicatingSchema.BoundedPolynomialMeasure ko7Schema
  transparentAtBase : StepDuplicatingSchema.TransparentAtBase ko7Schema measure.eval
  unbounded : StepDuplicatingSchema.HasUnboundedRangePoly measure

/-- Stronger projection data that actually closes the transparent row through the existing bounded polynomial barrier. -/
structure TransparentPolynomialProjectionData extends TransparentPolynomialProjectionBoundary where
  dominance : StepDuplicatingSchema.EventuallyDominatedAtBase measure

/-- Forget the extra dominance witness and retain only the transparent boundary payload. -/
def TransparentPolynomialProjectionData.toBoundary
    (data : TransparentPolynomialProjectionData) : TransparentPolynomialProjectionBoundary :=
  { measure := data.measure
    transparentAtBase := data.transparentAtBase
    unbounded := data.unbounded }

/-- Boundary-level proposition saying the missing dominance witness has been supplied. -/
def TransparentPolynomialProjectionBoundaryHasDominanceData
    (boundary : TransparentPolynomialProjectionBoundary) : Prop :=
  ∃ data : TransparentPolynomialProjectionData, data.toBoundary = boundary

/-- Any projection data immediately certifies that the underlying boundary carries dominance data. -/
theorem transparentPolynomialProjectionBoundary_hasDominanceData_of_data
    (data : TransparentPolynomialProjectionData) :
    TransparentPolynomialProjectionBoundaryHasDominanceData data.toBoundary := by
  exact ⟨data, rfl⟩

/-- The transparent row remains classified as projection-required at the current E3 stage. -/
theorem transparentPolynomialProjectionBoundary_requires_projectionData
    (_boundary : TransparentPolynomialProjectionBoundary) :
    nonlinearResidualStatus .boundedDegreeDirectTransparentPolynomial =
      .requiresExistingTheoremProjection := by
  rfl

/-- Once the missing dominance witness is supplied, the existing bounded polynomial barrier blocks the row. -/
theorem transparentPolynomialProjectionData_to_boundedPolynomialBarrier
    (data : TransparentPolynomialProjectionData) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System data.measure.eval (· < ·) := by
  exact
    PolynomialBarrierGeneral.no_global_step_orientation_polynomial_of_unbounded
      data.measure data.unbounded data.dominance

/-- Any concrete strengthening of a boundary witness by the missing dominance data is already blocked. -/
theorem transparentPolynomialProjectionBoundary_with_data_is_blocked
    (boundary : TransparentPolynomialProjectionBoundary)
    (data : TransparentPolynomialProjectionData)
    (hboundary : data.toBoundary = boundary) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System boundary.measure.eval (· < ·) := by
  cases hboundary
  simpa using transparentPolynomialProjectionData_to_boundedPolynomialBarrier data

/-- Any boundary carrying the missing dominance data is already blocked by the existing bounded polynomial barrier. -/
theorem transparentPolynomialProjectionBoundary_with_dominanceData_is_blocked
    (boundary : TransparentPolynomialProjectionBoundary)
    (hdata : TransparentPolynomialProjectionBoundaryHasDominanceData boundary) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System boundary.measure.eval (· < ·) := by
  rcases hdata with ⟨data, hboundary⟩
  exact transparentPolynomialProjectionBoundary_with_data_is_blocked boundary data hboundary

/-- Any concrete witness-class member already upgrades the boundary to full dominance data. -/
theorem transparentPolynomialProjectionBoundary_hasDominanceData_of_witnessClass
    (boundary : TransparentPolynomialProjectionBoundary)
    (hwitness : TransparentDominanceWitnessClass boundary.measure) :
    TransparentPolynomialProjectionBoundaryHasDominanceData boundary := by
  refine ⟨{
    measure := boundary.measure
    transparentAtBase := boundary.transparentAtBase
    unbounded := boundary.unbounded
    dominance :=
      transparent_dominance_witness_class_eventually_dominated_at_base boundary.measure hwitness
  }, rfl⟩

/-- Any boundary in the concrete witness class is already blocked by the existing bounded
polynomial barrier. -/
theorem transparentPolynomialProjectionBoundary_with_witnessClass_is_blocked
    (boundary : TransparentPolynomialProjectionBoundary)
    (hwitness : TransparentDominanceWitnessClass boundary.measure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System boundary.measure.eval (· < ·) := by
  exact
    transparentPolynomialProjectionBoundary_with_dominanceData_is_blocked boundary
      (transparentPolynomialProjectionBoundary_hasDominanceData_of_witnessClass boundary hwitness)

/-- Exact paper-facing catalog for the transparent projection boundary. -/
abbrev TransparentPolynomialProjectionBoundaryCatalog : Prop :=
  ∀ boundary : TransparentPolynomialProjectionBoundary,
    nonlinearResidualStatus .boundedDegreeDirectTransparentPolynomial =
        .requiresExistingTheoremProjection
      ∧ StepDuplicatingSchema.TransparentAtBase ko7Schema boundary.measure.eval
      ∧ StepDuplicatingSchema.HasUnboundedRangePoly boundary.measure
      ∧ ∀ data : TransparentPolynomialProjectionData,
          data.toBoundary = boundary →
            ¬ StepDuplicatingSchema.GlobalOrients ko7System boundary.measure.eval (· < ·)

/-- The transparent row is exact boundary-only until the missing dominance witness is packaged. -/
theorem transparent_polynomial_projection_boundary_catalog :
    TransparentPolynomialProjectionBoundaryCatalog := by
  intro boundary
  refine ⟨transparentPolynomialProjectionBoundary_requires_projectionData boundary,
    boundary.transparentAtBase, boundary.unbounded, ?_⟩
  intro data hboundary
  exact transparentPolynomialProjectionBoundary_with_data_is_blocked boundary data hboundary

end OperatorKO7.NonlinearTransparentProjection
