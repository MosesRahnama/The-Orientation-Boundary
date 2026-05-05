import OperatorKO7.Meta.ToolSearchFragmentCoverage_PerFamily

/-!
# Tool Search Fragment Coverage List Audit

This module records the finite family lists behind the current M4 tool-search
coverage audit.

Residual exclusions remain status labels only.
-/

namespace OperatorKO7.ToolSearchFragmentCoverageListAudit

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.ToolSearchFragmentCoverage
open OperatorKO7.ToolSearchFragmentCoverageStatus
open OperatorKO7.ToolSearchFragmentCoveragePerFamily

/-- Finite list of the theorem-backed tool-search families currently audited in M4. -/
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

/-- Finite list of the residual fragment families intentionally left outside the theorem-backed audit. -/
def residualToolSearchFamilies : List ResidualFragmentFamily :=
  [ .unrestrictedNonlinearDirect
  , .unrestrictedMatrixClasses
  ]

/-- The theorem-backed family list is complete for the current M4 audit surface. -/
theorem theoremBackedToolSearchFamilies_complete :
    ∀ family : ToolSearchFragmentFamily, family ∈ theoremBackedToolSearchFamilies := by
  intro family
  cases family <;> simp [theoremBackedToolSearchFamilies]

/-- Every theorem-backed family in the finite audit list carries the `covered` status label. -/
theorem theoremBackedToolSearchFamilies_status_covered :
    ∀ family : ToolSearchFragmentFamily,
      family ∈ theoremBackedToolSearchFamilies ->
      coveredFragmentFamilyStatus family = CoverageStatus.covered := by
  intro family _
  exact covered_fragment_family_status_catalog family

/-- Every theorem-backed family in the finite audit list is backed by a certificate projection. -/
theorem theoremBackedToolSearchFamilies_have_certificate
    {Sys : StepDuplicatingSystem} :
    ∀ family : ToolSearchFragmentFamily,
      family ∈ theoremBackedToolSearchFamilies ->
      familyCoveredByCertificate Sys family := by
  intro family _
  exact tool_search_family_covered_by_certificate (Sys := Sys) family

/-- The residual family list is complete for the current M4 residual labels. -/
theorem residualToolSearchFamilies_complete :
    ∀ family : ResidualFragmentFamily, family ∈ residualToolSearchFamilies := by
  intro family
  cases family <;> simp [residualToolSearchFamilies]

/-- Every residual family in the finite audit list carries the `residualExclusion` status label. -/
theorem residualToolSearchFamilies_status_residual :
    ∀ family : ResidualFragmentFamily,
      family ∈ residualToolSearchFamilies ->
      residualFragmentFamilyStatus family = CoverageStatus.residualExclusion := by
  intro family _
  exact residual_fragment_family_status_catalog family

/-- Combined finite audit catalog for theorem-backed families and residual status labels. -/
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
