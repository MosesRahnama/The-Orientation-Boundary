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

/-- Current closure statuses for the nonlinear residual split. -/
inductive NonlinearResidualStatus where
  | blockedByExistingTheorem
  | licensedEscape (route : ConstructionRoute)
  | certifiedSuccess
  | requiresExistingTheoremProjection
  | closedByConcreteDominanceWitnessClass
  | openResidualClass
deriving DecidableEq, Repr

/-- The finite nonlinear residual family list formalized in this sprint. -/
def nonlinearResidualFamilies : List NonlinearResidualFamily :=
  [.boundedDegreeDirectTransparentPolynomial,
    .boundedCrossTermQuadratic,
    .boundedMultilinear,
    .wpoPolynomialBranch,
    .maxPlusDirectFragment,
    .globalCrossCoupledWitness,
    .unconstrainedNonlinearDirect]

/-- The finite nonlinear residual status list realized by the current split. -/
def nonlinearResidualStatuses : List NonlinearResidualStatus :=
  [.requiresExistingTheoremProjection,
    .closedByConcreteDominanceWitnessClass,
    .blockedByExistingTheorem,
    .licensedEscape .W1,
    .openResidualClass]

/-- Status classification for each nonlinear residual subfamily. -/
def nonlinearResidualStatus : NonlinearResidualFamily → NonlinearResidualStatus
  | .boundedDegreeDirectTransparentPolynomial => .requiresExistingTheoremProjection
  | .boundedCrossTermQuadratic => .blockedByExistingTheorem
  | .boundedMultilinear => .blockedByExistingTheorem
  | .wpoPolynomialBranch => .blockedByExistingTheorem
  | .maxPlusDirectFragment => .blockedByExistingTheorem
  | .globalCrossCoupledWitness => .licensedEscape .W1
  | .unconstrainedNonlinearDirect => .openResidualClass

/-- Exact status equation for every nonlinear residual family. -/
theorem nonlinearResidualStatus_exact (family : NonlinearResidualFamily) :
    nonlinearResidualStatus family =
      match family with
      | .boundedDegreeDirectTransparentPolynomial => .requiresExistingTheoremProjection
      | .boundedCrossTermQuadratic => .blockedByExistingTheorem
      | .boundedMultilinear => .blockedByExistingTheorem
      | .wpoPolynomialBranch => .blockedByExistingTheorem
      | .maxPlusDirectFragment => .blockedByExistingTheorem
      | .globalCrossCoupledWitness => .licensedEscape .W1
      | .unconstrainedNonlinearDirect => .openResidualClass := by
  cases family <;> rfl

/-- The finite nonlinear residual family list has no duplicates. -/
theorem nonlinearResidualFamilies_nodup : nonlinearResidualFamilies.Nodup := by
  decide

/-- The finite nonlinear residual family list has exact size seven. -/
theorem nonlinearResidualFamilies_length : nonlinearResidualFamilies.length = 7 := by
  rfl

/-- Exact membership characterization for the nonlinear residual family list. -/
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

/-- The finite nonlinear residual status list has no duplicates. -/
theorem nonlinearResidualStatuses_nodup : nonlinearResidualStatuses.Nodup := by
  decide

/-- The finite nonlinear residual status list has exact size five. -/
theorem nonlinearResidualStatuses_length : nonlinearResidualStatuses.length = 5 := by
  rfl

/-- Exact membership characterization for the nonlinear residual status list. -/
theorem nonlinearResidualStatuses_complete_exact (status : NonlinearResidualStatus) :
    status ∈ nonlinearResidualStatuses ↔
      status = .requiresExistingTheoremProjection
    ∨ status = .closedByConcreteDominanceWitnessClass
        ∨ status = .blockedByExistingTheorem
        ∨ status = .licensedEscape .W1
        ∨ status = .openResidualClass := by
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
  | openResidualClass =>
      simp [nonlinearResidualStatuses]

/-- Every nonlinear residual family lands in the current finite status list. -/
theorem nonlinearResidualFamily_has_listed_status (family : NonlinearResidualFamily) :
    nonlinearResidualStatus family ∈ nonlinearResidualStatuses := by
  cases family <;> simp [nonlinearResidualStatus, nonlinearResidualStatuses]

/-- Paper-facing proposition for the finite nonlinear residual status catalog. -/
abbrev NonlinearResidualStatusCatalog : Prop :=
  ∀ family : NonlinearResidualFamily,
    family ∈ nonlinearResidualFamilies ∧
      nonlinearResidualStatus family ∈ nonlinearResidualStatuses

/-- The nonlinear residual split has an exact finite status catalog. -/
theorem nonlinear_residual_status_catalog : NonlinearResidualStatusCatalog := by
  intro family
  exact ⟨(nonlinearResidualFamilies_complete_exact family).2 <| by
    cases family <;> simp,
    nonlinearResidualFamily_has_listed_status family⟩

end OperatorKO7.NonlinearResidualTaxonomy
