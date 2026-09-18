import OperatorKO7.Meta.ToolSearchFragmentCoverage
import OperatorKO7.Meta.MatrixResidualTaxonomy
import OperatorKO7.Meta.MatrixToolSearchMapping

/-!
# Tool Search Fragment Coverage Status

This module adds a paper-facing status/certificate layer above the M4 coverage
ledger without strengthening any underlying barrier theorem.

Residual exclusions here are status labels only. They are not new impossibility
theorems.
-/

namespace OperatorKO7.ToolSearchFragmentCoverageStatus

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.ToolSearchFragmentCoverage
open OperatorKO7.MatrixResidualTaxonomy
open OperatorKO7.MatrixToolSearchMapping

/-- Paper-facing status label for a tool-search fragment family. -/
inductive CoverageStatus
  | covered
  | residualExclusion
  deriving DecidableEq, Repr

/-- Residual fragment families intentionally left outside the current theorem-backed ledger. -/
inductive ResidualFragmentFamily
  | unrestrictedNonlinearDirect
  /-- Legacy compatibility aggregate. The exact matrix split is carried separately by
  `MatrixResidualStatusCatalog`. -/
  | unrestrictedMatrixClasses
  deriving DecidableEq, Repr

/-- Exact paper-facing catalog for the refined residual matrix split. -/
abbrev MatrixResidualStatusCatalog : Prop :=
  matrixResidualClosureStatus .componentwiseWeakStrict = .reducedToExistingTheorem ∧
  matrixResidualClosureStatus .paretoProduct = .reducedToExistingTheorem ∧
  matrixResidualClosureStatus .lexPriority = .reducedToExistingTheorem ∧
  matrixResidualClosureStatus .permutationLexPriority = .reducedToExistingTheorem ∧
  matrixResidualClosureStatus .scalarizableWeight = .reducedToExistingTheorem ∧
  matrixResidualClosureStatus .arcticFull = .licensedEscape ∧
  matrixResidualClosureStatus .tropicalFull = .licensedEscape ∧
  matrixResidualClosureStatus .importDependentMatrix = .licensedEscape ∧
  matrixResidualClosureStatus .unconstrainedRelation = .notYetMethodClass

/-- Certificate packaging the three theorem-backed M4 coverage bundles. -/
structure ToolSearchCoverageCertificate (Sys : StepDuplicatingSystem) where
  direct : DirectScalarFragmentCoverageCatalog Sys
  extended : ExtendedDirectFragmentCoverageCatalog Sys
  matrix : MatrixProjectionFragmentCoverageCatalog Sys
  matrixResidual : MatrixResidualStatusCatalog

/-- Covered families receive the paper-facing `covered` status label. -/
def coveredFragmentFamilyStatus (_ : ToolSearchFragmentFamily) : CoverageStatus :=
  .covered

/-- Residual exclusions receive the paper-facing `residualExclusion` status label. -/
def residualFragmentFamilyStatus (_ : ResidualFragmentFamily) : CoverageStatus :=
  .residualExclusion

/-- The refined matrix residual catalog carries the exact status split rather than the old
opaque aggregate row. -/
theorem matrix_residual_status_catalog : MatrixResidualStatusCatalog := by
  exact matrixResidualClosureStatus_catalog

/-- The legacy aggregate matrix residual row refines to the exact matrix residual catalog. -/
theorem unrestricted_matrix_residual_refines_exact_catalog :
    residualFragmentFamilyStatus ResidualFragmentFamily.unrestrictedMatrixClasses =
      CoverageStatus.residualExclusion ∧ MatrixResidualStatusCatalog := by
  exact ⟨rfl, matrix_residual_status_catalog⟩

/-- The paper-facing certificate is exactly the current combined M4 coverage ledger. -/
theorem tool_search_coverage_certificate
    {Sys : StepDuplicatingSystem} : ToolSearchCoverageCertificate Sys := by
  rcases tool_search_fragment_coverage_catalog (Sys := Sys) with ⟨hDirect, hRest⟩
  rcases hRest with ⟨hExtended, hMatrix⟩
  exact {
    direct := hDirect
    extended := hExtended
    matrix := hMatrix
    matrixResidual := matrix_residual_status_catalog
  }

/-- The certificate projects the direct scalar coverage bundle. -/
theorem tool_search_coverage_certificate_projects_direct
    {Sys : StepDuplicatingSystem} : DirectScalarFragmentCoverageCatalog Sys :=
  (tool_search_coverage_certificate (Sys := Sys)).direct

/-- The certificate projects the extended-direct coverage bundle. -/
theorem tool_search_coverage_certificate_projects_extended
    {Sys : StepDuplicatingSystem} : ExtendedDirectFragmentCoverageCatalog Sys :=
  (tool_search_coverage_certificate (Sys := Sys)).extended

/-- The certificate projects the matrix-projection coverage bundle. -/
theorem tool_search_coverage_certificate_projects_matrix
    {Sys : StepDuplicatingSystem} : MatrixProjectionFragmentCoverageCatalog Sys :=
  (tool_search_coverage_certificate (Sys := Sys)).matrix

/-- The certificate projects the exact residual matrix status catalog. -/
theorem tool_search_coverage_certificate_projects_matrixResidual
    {Sys : StepDuplicatingSystem} : MatrixResidualStatusCatalog :=
  (tool_search_coverage_certificate (Sys := Sys)).matrixResidual

/-- Every theorem-backed covered family is labeled `covered` in the status catalog. -/
theorem covered_fragment_family_status_catalog :
    ∀ family : ToolSearchFragmentFamily,
      coveredFragmentFamilyStatus family = CoverageStatus.covered := by
  intro family
  cases family <;> rfl

/-- Every residual family is labeled `residualExclusion` in the status catalog. -/
theorem residual_fragment_family_status_catalog :
    ∀ family : ResidualFragmentFamily,
      residualFragmentFamilyStatus family = CoverageStatus.residualExclusion := by
  intro family
  cases family <;> rfl

end OperatorKO7.ToolSearchFragmentCoverageStatus
