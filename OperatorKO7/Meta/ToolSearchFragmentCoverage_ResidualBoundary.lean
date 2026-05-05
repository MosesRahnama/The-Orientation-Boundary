import OperatorKO7.Meta.ToolSearchFragmentCoverage_Exactness

/-!
# Tool Search Fragment Coverage Residual Boundary

This module packages the honest boundary of the M4 tool-search coverage stack:
the theorem-backed families carry covered status and certificates, while the
two residual families carry residual-exclusion status labels only.
-/

namespace OperatorKO7.ToolSearchFragmentCoverageResidualBoundary

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.ToolSearchFragmentCoverage
open OperatorKO7.ToolSearchFragmentCoverageStatus
open OperatorKO7.ToolSearchFragmentCoveragePerFamily
open OperatorKO7.ToolSearchFragmentCoverageListAudit
open OperatorKO7.ToolSearchFragmentCoverageExactness

/-- Paper-facing boundary proposition for the covered-family certificate layer
and the residual-family status-label layer. -/
abbrev ToolSearchResidualBoundaryCatalog (Sys : StepDuplicatingSystem) : Prop :=
  (∀ family : ToolSearchFragmentFamily,
    family ∈ theoremBackedToolSearchFamilies →
      coveredFragmentFamilyStatus family = CoverageStatus.covered
      ∧ familyCoveredByCertificate Sys family)
  ∧ (∀ family : ResidualFragmentFamily,
    family ∈ residualToolSearchFamilies →
      residualFragmentFamilyStatus family = CoverageStatus.residualExclusion)

/-- Every theorem-backed family in the covered list has covered status and a
certificate witness. -/
theorem covered_tool_search_families_have_status_and_certificate
    {Sys : StepDuplicatingSystem} :
    ∀ family : ToolSearchFragmentFamily,
      family ∈ theoremBackedToolSearchFamilies →
        coveredFragmentFamilyStatus family = CoverageStatus.covered
        ∧ familyCoveredByCertificate Sys family := by
  intro family hfamily
  exact ⟨theoremBackedToolSearchFamilies_status_covered family hfamily,
    theoremBackedToolSearchFamilies_have_certificate (Sys := Sys) family hfamily⟩

/-- Every residual family in the residual list keeps only the residual status
label. -/
theorem residual_tool_search_families_have_residual_status :
    ∀ family : ResidualFragmentFamily,
      family ∈ residualToolSearchFamilies →
        residualFragmentFamilyStatus family = CoverageStatus.residualExclusion := by
  intro family hfamily
  exact residualToolSearchFamilies_status_residual family hfamily

/-- Honest paper-facing boundary catalog for the M4 tool-search fragment
coverage stack. -/
theorem tool_search_residual_boundary_catalog
    {Sys : StepDuplicatingSystem} :
    ToolSearchResidualBoundaryCatalog Sys := by
  exact ⟨covered_tool_search_families_have_status_and_certificate (Sys := Sys),
    residual_tool_search_families_have_residual_status⟩

/-- Exact finite inventory bookkeeping is sufficient to recover the honest
residual-boundary catalog. -/
theorem tool_search_exact_inventory_implies_boundary_catalog
    {Sys : StepDuplicatingSystem}
    (_ : ToolSearchFragmentExactInventory) :
    ToolSearchResidualBoundaryCatalog Sys := by
  exact tool_search_residual_boundary_catalog (Sys := Sys)

end OperatorKO7.ToolSearchFragmentCoverageResidualBoundary
