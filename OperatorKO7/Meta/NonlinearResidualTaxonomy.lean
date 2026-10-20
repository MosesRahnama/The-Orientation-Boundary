import OperatorKO7.Meta.ConstructionMethodClassification

namespace OperatorKO7.NonlinearResidualTaxonomy

open OperatorKO7.ConstructionMethodClassification

/-- Finite nonlinear subfamilies used to split the unrestricted nonlinear direct residue. -/
inductive NonlinearResidualFamily where
  | boundedDegreeDirectTransparentPolynomial
  | boundedCrossTermQuadratic
  | boundedMultilinear
  | wpoPolynomialBranch
  | maxPlusDirectFragment
  | globalCrossCoupledWitness
  | unconstrainedNonlinearDirect
deriving DecidableEq, Repr

/-- Finite status vocabulary assigned by the nonlinear residual table. -/
inductive NonlinearResidualStatus where
  | blockedByExistingTheorem
  | licensedEscape (route : ConstructionRoute)
  | certifiedSuccess
  | requiresExistingTheoremProjection
  | closedByConcreteDominanceWitnessClass
  | exactLawCarrierBoundary
deriving DecidableEq, Repr

/-- Finite list of nonlinear residual family tags. -/
def nonlinearResidualFamilies : List NonlinearResidualFamily :=
  [.boundedDegreeDirectTransparentPolynomial,
    .boundedCrossTermQuadratic,
    .boundedMultilinear,
    .wpoPolynomialBranch,
    .maxPlusDirectFragment,
    .globalCrossCoupledWitness,
    .unconstrainedNonlinearDirect]

/-- Finite list of status tags used by the assignment table. -/
def nonlinearResidualStatuses : List NonlinearResidualStatus :=
  [.requiresExistingTheoremProjection,
    .closedByConcreteDominanceWitnessClass,
    .blockedByExistingTheorem,
    .licensedEscape .W1,
    .exactLawCarrierBoundary]

/-- Status classification for each nonlinear residual subfamily. -/
def nonlinearResidualStatus : NonlinearResidualFamily → NonlinearResidualStatus
  | .boundedDegreeDirectTransparentPolynomial => .requiresExistingTheoremProjection
  | .boundedCrossTermQuadratic => .blockedByExistingTheorem
  | .boundedMultilinear => .blockedByExistingTheorem
  | .wpoPolynomialBranch => .blockedByExistingTheorem
  | .maxPlusDirectFragment => .blockedByExistingTheorem
  | .globalCrossCoupledWitness => .licensedEscape .W1
  | .unconstrainedNonlinearDirect => .exactLawCarrierBoundary

/-- Status-table equation for every nonlinear residual family. -/
theorem nonlinearResidualStatus_exact (family : NonlinearResidualFamily) :
    nonlinearResidualStatus family =
      match family with
      | .boundedDegreeDirectTransparentPolynomial => .requiresExistingTheoremProjection
      | .boundedCrossTermQuadratic => .blockedByExistingTheorem
      | .boundedMultilinear => .blockedByExistingTheorem
      | .wpoPolynomialBranch => .blockedByExistingTheorem
      | .maxPlusDirectFragment => .blockedByExistingTheorem
      | .globalCrossCoupledWitness => .licensedEscape .W1
      | .unconstrainedNonlinearDirect => .exactLawCarrierBoundary := by
  cases family <;> rfl

/-- The finite nonlinear residual family list is duplicate-free. -/
theorem nonlinearResidualFamilies_nodup : nonlinearResidualFamilies.Nodup := by
  decide

/-- The finite nonlinear residual family list has length seven. -/
theorem nonlinearResidualFamilies_length : nonlinearResidualFamilies.length = 7 := by
  rfl

/-- Membership characterization for the nonlinear residual family list. -/
theorem nonlinearResidualFamilies_complete_exact (family : NonlinearResidualFamily) :
    family ∈ nonlinearResidualFamilies ↔
      family = .boundedDegreeDirectTransparentPolynomial
        ∨ family = .boundedCrossTermQuadratic
        ∨ family = .boundedMultilinear
        ∨ family = .wpoPolynomialBranch
        ∨ family = .maxPlusDirectFragment
        ∨ family = .globalCrossCoupledWitness
        ∨ family = .unconstrainedNonlinearDirect := by
  cases family <;> simp [nonlinearResidualFamilies]

/-- The finite nonlinear residual status list is duplicate-free. -/
theorem nonlinearResidualStatuses_nodup : nonlinearResidualStatuses.Nodup := by
  decide

/-- The finite nonlinear residual status list has length five. -/
theorem nonlinearResidualStatuses_length : nonlinearResidualStatuses.length = 5 := by
  rfl

/-- Membership characterization for the nonlinear residual status list. -/
theorem nonlinearResidualStatuses_complete_exact (status : NonlinearResidualStatus) :
    status ∈ nonlinearResidualStatuses ↔
      status = .requiresExistingTheoremProjection
    ∨ status = .closedByConcreteDominanceWitnessClass
        ∨ status = .blockedByExistingTheorem
        ∨ status = .licensedEscape .W1
        ∨ status = .exactLawCarrierBoundary := by
  cases status with
  | blockedByExistingTheorem =>
      simp [nonlinearResidualStatuses]
  | licensedEscape route =>
      cases route <;> simp [nonlinearResidualStatuses]
  | certifiedSuccess =>
      simp [nonlinearResidualStatuses]
  | requiresExistingTheoremProjection =>
      simp [nonlinearResidualStatuses]
  | closedByConcreteDominanceWitnessClass =>
    simp [nonlinearResidualStatuses]
  | exactLawCarrierBoundary =>
      simp [nonlinearResidualStatuses]

/-- Every nonlinear residual family receives a tag from the finite status list. -/
theorem nonlinearResidualFamily_has_listed_status (family : NonlinearResidualFamily) :
    nonlinearResidualStatus family ∈ nonlinearResidualStatuses := by
  cases family <;> simp [nonlinearResidualStatus, nonlinearResidualStatuses]

/-- Proposition exposing the closed family-to-status assignment table. The
status constructors carry metadata rather than backing theorem witnesses. -/
abbrev NonlinearResidualStatusCatalog : Prop :=
  ∀ family : NonlinearResidualFamily,
    family ∈ nonlinearResidualFamilies ∧
      nonlinearResidualStatus family ∈ nonlinearResidualStatuses

/-- Realization of the finite assigned-status catalog by case analysis. -/
theorem nonlinear_residual_status_catalog : NonlinearResidualStatusCatalog := by
  intro family
  exact ⟨(nonlinearResidualFamilies_complete_exact family).2 <| by
    cases family <;> simp,
    nonlinearResidualFamily_has_listed_status family⟩

end OperatorKO7.NonlinearResidualTaxonomy
