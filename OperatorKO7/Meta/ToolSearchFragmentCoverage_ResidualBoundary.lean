import OperatorKO7.Meta.ToolSearchFragmentCoverage_Exactness

/-!
# Tool-search fragment status catalog

The catalog combines per-family covered status and certificate propositions for the listed
theorem-backed families with status labels for the listed residual families.
-/

namespace OperatorKO7.ToolSearchFragmentCoverageResidualBoundary

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.ToolSearchFragmentCoverage
open OperatorKO7.ToolSearchFragmentCoverageStatus
open OperatorKO7.ToolSearchFragmentCoveragePerFamily
open OperatorKO7.ToolSearchFragmentCoverageListAudit
open OperatorKO7.ToolSearchFragmentCoverageExactness

/-- Conjunction of covered-family certificate claims and residual-family status-label claims. -/
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

/-- Assemble the two group-level status propositions into the catalog. -/
theorem tool_search_residual_boundary_catalog
    {Sys : StepDuplicatingSystem} :
    ToolSearchResidualBoundaryCatalog Sys := by
  exact ⟨covered_tool_search_families_have_status_and_certificate (Sys := Sys),
    residual_tool_search_families_have_residual_status⟩

/-- Return the unconditional catalog while accepting an unused exact-inventory premise. This
theorem does not derive either catalog component from that premise. -/
theorem tool_search_exact_inventory_implies_boundary_catalog
    {Sys : StepDuplicatingSystem}
    (_ : ToolSearchFragmentExactInventory) :
    ToolSearchResidualBoundaryCatalog Sys := by
  exact tool_search_residual_boundary_catalog (Sys := Sys)

end OperatorKO7.ToolSearchFragmentCoverageResidualBoundary
