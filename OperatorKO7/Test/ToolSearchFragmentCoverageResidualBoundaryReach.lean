import OperatorKO7.Meta.ToolSearchFragmentCoverage_ResidualBoundary

namespace ToolSearchFragmentCoverageResidualBoundaryReach

#check OperatorKO7.ToolSearchFragmentCoverageResidualBoundary.ToolSearchResidualBoundaryCatalog
#check OperatorKO7.ToolSearchFragmentCoverageResidualBoundary.covered_tool_search_families_have_status_and_certificate
#check OperatorKO7.ToolSearchFragmentCoverageResidualBoundary.residual_tool_search_families_have_residual_status
#check OperatorKO7.ToolSearchFragmentCoverageResidualBoundary.tool_search_residual_boundary_catalog
#check OperatorKO7.ToolSearchFragmentCoverageResidualBoundary.tool_search_exact_inventory_implies_boundary_catalog

open OperatorKO7.ToolSearchFragmentCoverage
open OperatorKO7.ToolSearchFragmentCoverageStatus
open OperatorKO7.ToolSearchFragmentCoveragePerFamily
open OperatorKO7.ToolSearchFragmentCoverageListAudit
open OperatorKO7.ToolSearchFragmentCoverageExactness
open OperatorKO7.ToolSearchFragmentCoverageResidualBoundary

example {Sys : OperatorKO7.StepDuplicating.StepDuplicatingSchema.StepDuplicatingSystem} :
    ToolSearchResidualBoundaryCatalog Sys := by
  exact tool_search_residual_boundary_catalog (Sys := Sys)

example {Sys : OperatorKO7.StepDuplicating.StepDuplicatingSchema.StepDuplicatingSystem} :
    coveredFragmentFamilyStatus ToolSearchFragmentFamily.extendedCrossQuadratic =
      CoverageStatus.covered
      ∧ familyCoveredByCertificate Sys ToolSearchFragmentFamily.extendedCrossQuadratic := by
  exact covered_tool_search_families_have_status_and_certificate (Sys := Sys) _
    (theoremBackedToolSearchFamilies_complete _)

example : residualFragmentFamilyStatus ResidualFragmentFamily.unrestrictedNonlinearDirect =
    CoverageStatus.residualExclusion := by
  exact residual_tool_search_families_have_residual_status _ (residualToolSearchFamilies_complete _)

example {Sys : OperatorKO7.StepDuplicating.StepDuplicatingSchema.StepDuplicatingSystem} :
    ToolSearchResidualBoundaryCatalog Sys := by
  exact tool_search_exact_inventory_implies_boundary_catalog (Sys := Sys)
    tool_search_fragment_exact_inventory

end ToolSearchFragmentCoverageResidualBoundaryReach
