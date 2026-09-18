import OperatorKO7.Meta.ToolSearchFragmentCoverage_PerFamily

/-!
# Tool-search family lists

This module lists every constructor of the declared
`ToolSearchFragmentFamily` and `ResidualFragmentFamily` types. Membership
completeness is therefore relative to those closed enums. Covered and residual
statuses, together with certificate projections, are imported from the
per-family catalog; these results do not quantify over external tool-search
spaces.

Residual entries are status labels.
-/

namespace OperatorKO7.ToolSearchFragmentCoverageListAudit

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.ToolSearchFragmentCoverage
open OperatorKO7.ToolSearchFragmentCoverageStatus
open OperatorKO7.ToolSearchFragmentCoveragePerFamily

/-- List containing every constructor of `ToolSearchFragmentFamily`. -/
def theoremBackedToolSearchFamilies : List ToolSearchFragmentFamily :=
  [ .directAdditive
  , .directAffine
  , .directQuadratic
  , .directMultilinear
  , .directPolynomial
  , .extendedCrossQuadratic
  , .extendedMaxPlus
  , .extendedWPOPolynomial
  , .matrixFixedRow
  , .matrixRowSum
  , .matrixArcticFixedRow
  , .matrixArcticRowSum
  , .matrixTropicalFixedRow
  , .matrixTropicalRowSum
  ]

/-- List containing every constructor of `ResidualFragmentFamily`. -/
def residualToolSearchFamilies : List ResidualFragmentFamily :=
  [ .unrestrictedNonlinearDirect
  , .unrestrictedMatrixClasses
  ]

/-- Every constructor of `ToolSearchFragmentFamily` occurs in the declared list. -/
theorem theoremBackedToolSearchFamilies_complete :
    ∀ family : ToolSearchFragmentFamily, family ∈ theoremBackedToolSearchFamilies := by
  intro family
  cases family <;> simp [theoremBackedToolSearchFamilies]

/-- Each listed theorem-backed family receives the imported `covered` status label. -/
theorem theoremBackedToolSearchFamilies_status_covered :
    ∀ family : ToolSearchFragmentFamily,
      family ∈ theoremBackedToolSearchFamilies ->
      coveredFragmentFamilyStatus family = CoverageStatus.covered := by
  intro family _
  exact covered_fragment_family_status_catalog family

/-- Each listed theorem-backed family receives the imported certificate projection. -/
theorem theoremBackedToolSearchFamilies_have_certificate
    {Sys : StepDuplicatingSystem} :
    ∀ family : ToolSearchFragmentFamily,
      family ∈ theoremBackedToolSearchFamilies ->
      familyCoveredByCertificate Sys family := by
  intro family _
  exact tool_search_family_covered_by_certificate (Sys := Sys) family

/-- Every constructor of `ResidualFragmentFamily` occurs in the declared list. -/
theorem residualToolSearchFamilies_complete :
    ∀ family : ResidualFragmentFamily, family ∈ residualToolSearchFamilies := by
  intro family
  cases family <;> simp [residualToolSearchFamilies]

/-- Each listed residual family receives the imported `residualExclusion` status label. -/
theorem residualToolSearchFamilies_status_residual :
    ∀ family : ResidualFragmentFamily,
      family ∈ residualToolSearchFamilies ->
      residualFragmentFamilyStatus family = CoverageStatus.residualExclusion := by
  intro family _
  exact residual_fragment_family_status_catalog family

/-- Combines closed-enum membership with the imported status and certificate projections. -/
theorem tool_search_fragment_audit_catalog
    {Sys : StepDuplicatingSystem} :
    (∀ family : ToolSearchFragmentFamily,
      family ∈ theoremBackedToolSearchFamilies ∧
      coveredFragmentFamilyStatus family = CoverageStatus.covered ∧
      familyCoveredByCertificate Sys family) ∧
    (∀ family : ResidualFragmentFamily,
      family ∈ residualToolSearchFamilies ∧
      residualFragmentFamilyStatus family = CoverageStatus.residualExclusion) := by
  constructor
  · intro family
    exact ⟨theoremBackedToolSearchFamilies_complete family,
      theoremBackedToolSearchFamilies_status_covered family
        (theoremBackedToolSearchFamilies_complete family),
      theoremBackedToolSearchFamilies_have_certificate (Sys := Sys) family
        (theoremBackedToolSearchFamilies_complete family)⟩
  · intro family
    exact ⟨residualToolSearchFamilies_complete family,
      residualToolSearchFamilies_status_residual family
        (residualToolSearchFamilies_complete family)⟩

end OperatorKO7.ToolSearchFragmentCoverageListAudit
