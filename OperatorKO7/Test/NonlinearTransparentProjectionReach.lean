import OperatorKO7.Meta.NonlinearTransparentProjection
import OperatorKO7.Meta.NonlinearDominanceCriteria

namespace NonlinearTransparentProjectionReach

open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.NonlinearDominanceCriteria
open OperatorKO7.NonlinearDominanceWitnesses
open OperatorKO7.NonlinearResidualTaxonomy
open OperatorKO7.NonlinearTransparentProjection

#check TransparentPolynomialProjectionBoundary
#check TransparentPolynomialProjectionData
#check TransparentPolynomialProjectionData.toBoundary
#check TransparentPolynomialProjectionBoundaryHasDominanceData
#check transparentPolynomialProjectionBoundary_hasDominanceData_of_data
#check transparentPolynomialProjectionBoundary_requires_projectionData
#check transparentPolynomialProjectionData_to_boundedPolynomialBarrier
#check transparentPolynomialProjectionBoundary_with_data_is_blocked
#check transparentPolynomialProjectionBoundary_with_dominanceData_is_blocked
#check transparentPolynomialProjectionBoundary_hasDominanceData_of_witnessClass
#check transparentPolynomialProjectionBoundary_with_witnessClass_is_blocked
#check TransparentPolynomialProjectionBoundaryCatalog
#check transparent_polynomial_projection_boundary_catalog
#check TrivialMonomialDominanceWitness
#check WrapDominantFrozenAffineWitness
#check SuccessorIdentityDominanceWitness
#check trivial_monomial_eventually_dominated_at_base
#check wrap_dominant_eventually_dominated_at_base
#check successor_identity_eventually_dominated_at_base
#check TransparentDominanceWitnessClass
#check transparent_dominance_witness_class_eventually_dominated_at_base
#check transparent_polynomial_dominance_unconditional_for_class
#check transparent_polynomial_dominance_universal_unconditional
#check NonlinearResidualStatus
#check nonlinearResidualStatus
#check nonlinearResidualStatuses
#check nonlinearResidualStatuses_length
#check StepDuplicatingSchema.TransparentAtBase
#check StepDuplicatingSchema.HasUnboundedRangePoly
#check StepDuplicatingSchema.EventuallyDominatedAtBase

example (boundary : TransparentPolynomialProjectionBoundary) :
    nonlinearResidualStatus .boundedDegreeDirectTransparentPolynomial =
      .requiresExistingTheoremProjection := by
  exact transparentPolynomialProjectionBoundary_requires_projectionData boundary

example : nonlinearResidualStatuses.length = 5 := by
  exact nonlinearResidualStatuses_length

example : NonlinearResidualStatus.closedByConcreteDominanceWitnessClass ∈ nonlinearResidualStatuses := by
  simp [nonlinearResidualStatuses]

example (boundary : TransparentPolynomialProjectionBoundary) :
    StepDuplicatingSchema.TransparentAtBase ko7Schema boundary.measure.eval :=
  boundary.transparentAtBase

example (boundary : TransparentPolynomialProjectionBoundary) :
    StepDuplicatingSchema.HasUnboundedRangePoly boundary.measure :=
  boundary.unbounded

example (data : TransparentPolynomialProjectionData) :
    TransparentPolynomialProjectionBoundary :=
  data.toBoundary

example (data : TransparentPolynomialProjectionData) :
    TransparentPolynomialProjectionBoundaryHasDominanceData data.toBoundary := by
  exact transparentPolynomialProjectionBoundary_hasDominanceData_of_data data

example (data : TransparentPolynomialProjectionData) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System data.measure.eval (· < ·) := by
  exact transparentPolynomialProjectionData_to_boundedPolynomialBarrier data

example (boundary : TransparentPolynomialProjectionBoundary)
    (hdata : TransparentPolynomialProjectionBoundaryHasDominanceData boundary) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System boundary.measure.eval (· < ·) := by
  exact transparentPolynomialProjectionBoundary_with_dominanceData_is_blocked boundary hdata

example (boundary : TransparentPolynomialProjectionBoundary)
    (hwitness : TransparentDominanceWitnessClass boundary.measure) :
    TransparentPolynomialProjectionBoundaryHasDominanceData boundary := by
  exact transparentPolynomialProjectionBoundary_hasDominanceData_of_witnessClass boundary hwitness

example (boundary : TransparentPolynomialProjectionBoundary)
    (hwitness : TransparentDominanceWitnessClass boundary.measure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System boundary.measure.eval (· < ·) := by
  exact transparentPolynomialProjectionBoundary_with_witnessClass_is_blocked boundary hwitness

example (boundary : TransparentPolynomialProjectionBoundary)
    (hwitness : TransparentDominanceWitnessClass boundary.measure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System boundary.measure.eval (· < ·) := by
  exact transparent_polynomial_dominance_unconditional_for_class boundary hwitness

example (boundary : TransparentPolynomialProjectionBoundary)
    (hwitness : TransparentDominanceWitnessClass boundary.measure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System boundary.measure.eval (· < ·) := by
  exact transparent_polynomial_dominance_universal_unconditional boundary hwitness

example : TransparentPolynomialProjectionBoundaryCatalog :=
  transparent_polynomial_projection_boundary_catalog

end NonlinearTransparentProjectionReach
