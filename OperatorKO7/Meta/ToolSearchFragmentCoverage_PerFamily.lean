import OperatorKO7.Meta.ToolSearchFragmentCoverage_Status

/-!
# Tool Search Fragment Coverage Per Family

This module refines the grouped M4 status/certificate layer into a per-family
coverage audit without adding new barrier theorems.

Residual exclusions remain status labels only.
-/

namespace OperatorKO7.ToolSearchFragmentCoveragePerFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.ToolSearchFragmentCoverage
open OperatorKO7.ToolSearchFragmentCoverageStatus

/-- Paper-facing grouping of the theorem-backed tool-search fragment families. -/
inductive ToolSearchFragmentGroup
  | directScalar
  | extendedDirect
  | matrixProjection
  deriving DecidableEq, Repr

/-- Group assignment for each theorem-backed tool-search fragment family. -/
def toolSearchFragmentGroup : ToolSearchFragmentFamily -> ToolSearchFragmentGroup
  | .directAdditive => .directScalar
  | .directAffine => .directScalar
  | .directQuadratic => .directScalar
  | .directMultilinear => .directScalar
  | .directPolynomial => .directScalar
  | .extendedCrossQuadratic => .extendedDirect
  | .extendedMaxPlus => .extendedDirect
  | .extendedWPOPolynomial => .extendedDirect
  | .matrixFixedRow => .matrixProjection
  | .matrixRowSum => .matrixProjection
  | .matrixArcticFixedRow => .matrixProjection
  | .matrixArcticRowSum => .matrixProjection
  | .matrixTropicalFixedRow => .matrixProjection
  | .matrixTropicalRowSum => .matrixProjection

/-- A covered family is audited by projecting to its grouped certificate bundle. -/
def familyCoveredByCertificate (Sys : StepDuplicatingSystem)
    (family : ToolSearchFragmentFamily) : Prop :=
  match toolSearchFragmentGroup family with
  | .directScalar => DirectScalarFragmentCoverageCatalog Sys
  | .extendedDirect => ExtendedDirectFragmentCoverageCatalog Sys
  | .matrixProjection => MatrixProjectionFragmentCoverageCatalog Sys

/-- Every theorem-backed family has a fixed group in the per-family catalog. -/
theorem tool_search_fragment_group_catalog :
    ∀ family : ToolSearchFragmentFamily,
      match family with
      | .directAdditive
      | .directAffine
      | .directQuadratic
      | .directMultilinear
      | .directPolynomial =>
          toolSearchFragmentGroup family = ToolSearchFragmentGroup.directScalar
      | .extendedCrossQuadratic
      | .extendedMaxPlus
      | .extendedWPOPolynomial =>
          toolSearchFragmentGroup family = ToolSearchFragmentGroup.extendedDirect
      | .matrixFixedRow
      | .matrixRowSum
      | .matrixArcticFixedRow
      | .matrixArcticRowSum
      | .matrixTropicalFixedRow
      | .matrixTropicalRowSum =>
          toolSearchFragmentGroup family = ToolSearchFragmentGroup.matrixProjection := by
  intro family
  cases family <;> rfl

/-- Direct-scalar families project to the direct certificate bundle. -/
theorem direct_scalar_families_project_to_direct_certificate
    {Sys : StepDuplicatingSystem} {family : ToolSearchFragmentFamily}
    (hgroup : toolSearchFragmentGroup family = ToolSearchFragmentGroup.directScalar) :
    familyCoveredByCertificate Sys family =
      DirectScalarFragmentCoverageCatalog Sys := by
  simp [familyCoveredByCertificate, hgroup]

/-- Extended-direct families project to the extended-direct certificate bundle. -/
theorem extended_direct_families_project_to_extended_certificate
    {Sys : StepDuplicatingSystem} {family : ToolSearchFragmentFamily}
    (hgroup : toolSearchFragmentGroup family = ToolSearchFragmentGroup.extendedDirect) :
    familyCoveredByCertificate Sys family =
      ExtendedDirectFragmentCoverageCatalog Sys := by
  simp [familyCoveredByCertificate, hgroup]

/-- Matrix-projection families project to the matrix certificate bundle. -/
theorem matrix_projection_families_project_to_matrix_certificate
    {Sys : StepDuplicatingSystem} {family : ToolSearchFragmentFamily}
    (hgroup : toolSearchFragmentGroup family = ToolSearchFragmentGroup.matrixProjection) :
    familyCoveredByCertificate Sys family =
      MatrixProjectionFragmentCoverageCatalog Sys := by
  simp [familyCoveredByCertificate, hgroup]

/-- Every theorem-backed family is covered by the appropriate certificate projection. -/
theorem tool_search_family_covered_by_certificate
    {Sys : StepDuplicatingSystem} :
    ∀ family : ToolSearchFragmentFamily, familyCoveredByCertificate Sys family := by
  intro family
  cases family
  all_goals
    simp [familyCoveredByCertificate, toolSearchFragmentGroup]
  all_goals
    first
    | exact tool_search_coverage_certificate_projects_direct (Sys := Sys)
    | exact tool_search_coverage_certificate_projects_extended (Sys := Sys)
    | exact tool_search_coverage_certificate_projects_matrix (Sys := Sys)

/-- Every theorem-backed family is both status-covered and backed by a certificate projection. -/
theorem tool_search_family_status_and_certificate
    {Sys : StepDuplicatingSystem} :
    ∀ family : ToolSearchFragmentFamily,
      coveredFragmentFamilyStatus family = CoverageStatus.covered ∧
      familyCoveredByCertificate Sys family := by
  intro family
  exact ⟨covered_fragment_family_status_catalog family,
    tool_search_family_covered_by_certificate (Sys := Sys) family⟩

end OperatorKO7.ToolSearchFragmentCoveragePerFamily
