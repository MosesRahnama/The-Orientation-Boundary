import OperatorKO7.Meta.NonlinearResidualTaxonomy
import OperatorKO7.Meta.NonlinearDominanceCriteria
import OperatorKO7.Meta.NonlinearMethodLawCarrier
import OperatorKO7.Meta.NonlinearUnconstrainedSplit
import OperatorKO7.Meta.NonlinearTransparentProjection
import OperatorKO7.Meta.PolynomialBarrierGeneral
import OperatorKO7.Meta.QuadraticCrossTermBarrier
import OperatorKO7.Meta.MultilinearBarrier
import OperatorKO7.Meta.WPO_PolynomialBarrier
import OperatorKO7.Meta.MaxBarrier

namespace OperatorKO7.NonlinearDirectBoundary

open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.NonlinearDominanceCriteria
open OperatorKO7.NonlinearDominanceWitnesses
open _root_.OperatorKO7.NonlinearMethodLawCarrier
open OperatorKO7.NonlinearResidualTaxonomy
open OperatorKO7.NonlinearTransparentProjection
open OperatorKO7.NonlinearUnconstrainedSplit

/-- Theorem-backed support payload for each nonlinear residual family in the E3 split. -/
def NonlinearDirectBoundarySupported : NonlinearResidualFamily → Prop
  | .boundedDegreeDirectTransparentPolynomial =>
      nonlinearResidualStatus .boundedDegreeDirectTransparentPolynomial =
          .requiresExistingTheoremProjection
        ∧ NonlinearResidualStatus.closedByConcreteDominanceWitnessClass ∈ nonlinearResidualStatuses
        ∧ TransparentPolynomialProjectionBoundaryCatalog
        ∧ TransparentPolynomialConditionalClosureCatalog
        ∧ ∀ boundary : TransparentPolynomialProjectionBoundary,
            TransparentDominanceWitnessClass boundary.measure →
              ¬ StepDuplicatingSchema.GlobalOrients ko7System boundary.measure.eval (· < ·)
  | .boundedCrossTermQuadratic =>
      ∀ (M : StepDuplicatingSchema.CrossTermQuadraticMeasure CompositionalImpossibility.ko7Schema)
        (_hunbounded : StepDuplicatingSchema.HasUnboundedRangeX M)
        (_hbounded : StepDuplicatingSchema.CrossTermBoundedAtBase M),
        ¬ StepDuplicatingSchema.GlobalOrients CompositionalImpossibility.ko7System M.eval (· < ·)
  | .boundedMultilinear =>
      ∀ (M : StepDuplicatingSchema.BoundedMultilinearMeasure CompositionalImpossibility.ko7Schema)
        (_hunbounded : StepDuplicatingSchema.HasUnboundedRangeML M)
        (_hdom : StepDuplicatingSchema.MultilinearDominatedAtBase M),
        ¬ StepDuplicatingSchema.GlobalOrients CompositionalImpossibility.ko7System M.eval (· < ·)
  | .wpoPolynomialBranch =>
      ∀ (W : StepDuplicatingSchema.WPOPolynomialDirectOrder CompositionalImpossibility.ko7Schema)
        (_hunbounded : StepDuplicatingSchema.HasUnboundedRangePoly W.measure)
        (_hdom : StepDuplicatingSchema.EventuallyDominatedAtBase W.measure),
        ¬ StepDuplicatingSchema.GlobalOrients CompositionalImpossibility.ko7System (fun t => t) (fun x y => W.gt y x)
  | .maxPlusDirectFragment =>
      ∀ (M : StepDuplicatingSchema.MaxMeasure CompositionalImpossibility.ko7Schema)
        (_hunbounded : StepDuplicatingSchema.HasUnboundedRangeMax M),
        ¬ StepDuplicatingSchema.GlobalOrients CompositionalImpossibility.ko7System M.eval (· < ·)
  | .globalCrossCoupledWitness =>
      nonlinearResidualStatus .globalCrossCoupledWitness = .licensedEscape .W1
        ∧ poly_w1_success.route = .W1
        ∧ poly_w1_success.importClass = .globalPolynomial
        ∧ PermittedW1Import .globalPolynomial
  | .unconstrainedNonlinearDirect =>
      nonlinearResidualStatus .unconstrainedNonlinearDirect = .openResidualClass
        ∧ NonlinearUnconstrainedSplitCatalog
        ∧ ∀ (R : NonlinearRelation),
            unsupported_arbitrary_relation_boundary R

/-- The transparent-specific polynomial row now carries the concrete witness-class closure theorem
while preserving the legacy projection-required status equation for downstream compatibility. -/
theorem boundedDegreeDirectTransparentPolynomial_closed_by_concrete_dominance_witness_class :
    NonlinearDirectBoundarySupported .boundedDegreeDirectTransparentPolynomial := by
  exact ⟨rfl,
    by simp [nonlinearResidualStatuses],
    transparent_polynomial_projection_boundary_catalog,
    transparent_polynomial_conditional_closure_catalog,
    transparent_polynomial_dominance_universal_unconditional⟩

/-- Backward-compatible theorem name for downstream files that still refer to the old boundary label. -/
theorem boundedDegreeDirectTransparentPolynomial_requires_projection :
    NonlinearDirectBoundarySupported .boundedDegreeDirectTransparentPolynomial :=
  boundedDegreeDirectTransparentPolynomial_closed_by_concrete_dominance_witness_class

/-- The bounded cross-term quadratic fragment is blocked by an existing KO7 barrier theorem. -/
theorem boundedCrossTermQuadratic_blocked :
    NonlinearDirectBoundarySupported .boundedCrossTermQuadratic := by
  exact
    (show ∀ (M : StepDuplicatingSchema.CrossTermQuadraticMeasure CompositionalImpossibility.ko7Schema)
      (_hunbounded : StepDuplicatingSchema.HasUnboundedRangeX M)
      (_hbounded : StepDuplicatingSchema.CrossTermBoundedAtBase M),
      ¬ StepDuplicatingSchema.GlobalOrients CompositionalImpossibility.ko7System M.eval (· < ·) from
        QuadraticCrossTermBarrier.no_global_step_orientation_cross_quadratic_of_unbounded)

/-- The bounded multilinear fragment is blocked by an existing KO7 barrier theorem. -/
theorem boundedMultilinear_blocked :
    NonlinearDirectBoundarySupported .boundedMultilinear := by
  exact
    (show ∀ (M : StepDuplicatingSchema.BoundedMultilinearMeasure CompositionalImpossibility.ko7Schema)
      (_hunbounded : StepDuplicatingSchema.HasUnboundedRangeML M)
      (_hdom : StepDuplicatingSchema.MultilinearDominatedAtBase M),
      ¬ StepDuplicatingSchema.GlobalOrients CompositionalImpossibility.ko7System M.eval (· < ·) from
        MultilinearBarrier.no_global_step_orientation_multilinear_of_unbounded)

/-- The direct WPO polynomial branch is blocked by the existing KO7 corollary. -/
theorem wpoPolynomialBranch_blocked :
    NonlinearDirectBoundarySupported .wpoPolynomialBranch := by
  exact
    (show ∀ (W : StepDuplicatingSchema.WPOPolynomialDirectOrder CompositionalImpossibility.ko7Schema)
      (_hunbounded : StepDuplicatingSchema.HasUnboundedRangePoly W.measure)
      (_hdom : StepDuplicatingSchema.EventuallyDominatedAtBase W.measure),
      ¬ StepDuplicatingSchema.GlobalOrients CompositionalImpossibility.ko7System (fun t => t)
        (fun x y => W.gt y x) from
        WPOPolynomialBarrier.no_global_step_orientation_wpoPolynomialDirect_of_unbounded)

/-- The max-plus direct fragment is blocked by the existing KO7 max barrier. -/
theorem maxPlusDirectFragment_blocked :
    NonlinearDirectBoundarySupported .maxPlusDirectFragment := by
  exact
    (show ∀ (M : StepDuplicatingSchema.MaxMeasure CompositionalImpossibility.ko7Schema)
      (_hunbounded : StepDuplicatingSchema.HasUnboundedRangeMax M),
      ¬ StepDuplicatingSchema.GlobalOrients CompositionalImpossibility.ko7System M.eval (· < ·) from
        MaxBarrier.no_global_step_orientation_max_of_unbounded)

/-- The global cross-coupled nonlinear witness is licensed as a W1 escape, not as a W0 barrier theorem. -/
theorem globalCrossCoupledWitness_licensed_escape :
    NonlinearDirectBoundarySupported .globalCrossCoupledWitness := by
  exact
    (show nonlinearResidualStatus .globalCrossCoupledWitness = .licensedEscape .W1
      ∧ poly_w1_success.route = .W1
      ∧ poly_w1_success.importClass = .globalPolynomial
      ∧ PermittedW1Import .globalPolynomial from
        ⟨rfl, rfl, rfl, poly_w1_success_requires_global_polynomial_import⟩)

/-- The unrestricted nonlinear direct class remains open after splitting off the theorem-backed fragments. -/
theorem unconstrainedNonlinearDirect_remains_open :
    NonlinearDirectBoundarySupported .unconstrainedNonlinearDirect := by
  exact ⟨rfl,
    nonlinear_unconstrained_split_catalog,
    unsupported_arbitrary_relation_no_first_order_method_or_licensed_escape⟩

/-- Every nonlinear residual family carries the exact theorem-backed support recorded by the E3 split. -/
theorem nonlinear_direct_boundary_supported (family : NonlinearResidualFamily) :
    NonlinearDirectBoundarySupported family := by
  cases family with
  | boundedDegreeDirectTransparentPolynomial =>
      exact boundedDegreeDirectTransparentPolynomial_requires_projection
  | boundedCrossTermQuadratic =>
      exact boundedCrossTermQuadratic_blocked
  | boundedMultilinear =>
      exact boundedMultilinear_blocked
  | wpoPolynomialBranch =>
      exact wpoPolynomialBranch_blocked
  | maxPlusDirectFragment =>
      exact maxPlusDirectFragment_blocked
  | globalCrossCoupledWitness =>
      exact globalCrossCoupledWitness_licensed_escape
  | unconstrainedNonlinearDirect =>
      exact unconstrainedNonlinearDirect_remains_open

/-- Paper-facing proposition for the nonlinear residual boundary projection catalog. -/
abbrev NonlinearDirectBoundaryProjectionCatalog : Prop :=
  ∀ family : NonlinearResidualFamily,
    family ∈ nonlinearResidualFamilies ∧
      NonlinearDirectBoundarySupported family ∧
      nonlinearResidualStatus family ∈ nonlinearResidualStatuses

/-- The nonlinear residual split has exact boundary support for every listed family. -/
theorem nonlinear_direct_boundary_projection_catalog : NonlinearDirectBoundaryProjectionCatalog := by
  intro family
  exact ⟨(nonlinearResidualFamilies_complete_exact family).2 <| by
      cases family <;> simp,
    nonlinear_direct_boundary_supported family,
    nonlinearResidualFamily_has_listed_status family⟩

/-- Certificate packaging the nonlinear status catalog and the theorem-backed boundary projections. -/
structure NonlinearDirectBoundaryCertificate where
  statusCatalog : NonlinearResidualStatusCatalog
  projectionCatalog : NonlinearDirectBoundaryProjectionCatalog

/-- The E3 nonlinear split certificate records the finite status list and its theorem-backed boundary projections. -/
theorem nonlinear_direct_boundary_certificate : NonlinearDirectBoundaryCertificate := by
  exact {
    statusCatalog := nonlinear_residual_status_catalog
    projectionCatalog := nonlinear_direct_boundary_projection_catalog
  }

/-- The nonlinear boundary certificate projects the finite status catalog. -/
theorem nonlinear_direct_boundary_certificate_projects_status_catalog :
    NonlinearResidualStatusCatalog :=
  nonlinear_direct_boundary_certificate.statusCatalog

/-- The nonlinear boundary certificate projects the theorem-backed boundary catalog. -/
theorem nonlinear_direct_boundary_certificate_projects_projection_catalog :
    NonlinearDirectBoundaryProjectionCatalog :=
  nonlinear_direct_boundary_certificate.projectionCatalog

end OperatorKO7.NonlinearDirectBoundary
