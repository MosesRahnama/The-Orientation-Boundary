import OperatorKO7.Meta.ToolSearchFragmentCoverage_ResidualBoundary

namespace ToolSearchFragmentCoverageExactnessReach

#check OperatorKO7.ToolSearchFragmentCoverageExactness.theoremBackedToolSearchFamilies_nodup
#check OperatorKO7.ToolSearchFragmentCoverageExactness.theoremBackedToolSearchFamilies_length
#check OperatorKO7.ToolSearchFragmentCoverageExactness.residualToolSearchFamilies_nodup
#check OperatorKO7.ToolSearchFragmentCoverageExactness.residualToolSearchFamilies_length
#check OperatorKO7.ToolSearchFragmentCoverageExactness.theoremBackedToolSearchFamilies_directScalar_filter
#check OperatorKO7.ToolSearchFragmentCoverageExactness.theoremBackedToolSearchFamilies_extendedDirect_filter
#check OperatorKO7.ToolSearchFragmentCoverageExactness.theoremBackedToolSearchFamilies_matrixProjection_filter
#check OperatorKO7.ToolSearchFragmentCoverageExactness.theoremBackedToolSearchFamilies_complete_exact
#check OperatorKO7.ToolSearchFragmentCoverageExactness.residualToolSearchFamilies_complete_exact
#check OperatorKO7.ToolSearchFragmentCoverageExactness.direct_scalar_family_group_catalog
#check OperatorKO7.ToolSearchFragmentCoverageExactness.extended_direct_family_group_catalog
#check OperatorKO7.ToolSearchFragmentCoverageExactness.matrix_projection_family_group_catalog
#check OperatorKO7.ToolSearchFragmentCoverageExactness.tool_search_group_partition_catalog
#check OperatorKO7.ToolSearchFragmentCoverageExactness.ToolSearchFragmentExactInventory
#check OperatorKO7.ToolSearchFragmentCoverageExactness.tool_search_fragment_exact_inventory

#check OperatorKO7.ToolSearchFragmentCoverageResidualBoundary.ToolSearchResidualBoundaryCatalog
#check OperatorKO7.ToolSearchFragmentCoverageResidualBoundary.covered_tool_search_families_have_status_and_certificate
#check OperatorKO7.ToolSearchFragmentCoverageResidualBoundary.residual_tool_search_families_have_residual_status
#check OperatorKO7.ToolSearchFragmentCoverageResidualBoundary.tool_search_residual_boundary_catalog
#check OperatorKO7.ToolSearchFragmentCoverageResidualBoundary.tool_search_exact_inventory_implies_boundary_catalog

open OperatorKO7.ToolSearchFragmentCoverage
open OperatorKO7.ToolSearchFragmentCoverageStatus
open OperatorKO7.ToolSearchFragmentCoverageListAudit
open OperatorKO7.ToolSearchFragmentCoverageExactness
open OperatorKO7.ToolSearchFragmentCoverageResidualBoundary

example : theoremBackedToolSearchFamilies.length = 14 := by
  exact theoremBackedToolSearchFamilies_length

example : residualToolSearchFamilies.length = 2 := by
  exact residualToolSearchFamilies_length

example :
    theoremBackedToolSearchFamilies.filter (fun family =>
      decide (OperatorKO7.ToolSearchFragmentCoveragePerFamily.toolSearchFragmentGroup family =
        OperatorKO7.ToolSearchFragmentCoveragePerFamily.ToolSearchFragmentGroup.directScalar)) =
      [ ToolSearchFragmentFamily.directAdditive
      , ToolSearchFragmentFamily.directAffine
      , ToolSearchFragmentFamily.directQuadratic
      , ToolSearchFragmentFamily.directMultilinear
      , ToolSearchFragmentFamily.directPolynomial
      ] := by
  exact theoremBackedToolSearchFamilies_directScalar_filter

example :
    ToolSearchFragmentFamily.extendedMaxPlus ∈ theoremBackedToolSearchFamilies := by
  exact theoremBackedToolSearchFamilies_complete _

example :
    (ToolSearchFragmentFamily.matrixArcticRowSum ∈ theoremBackedToolSearchFamilies
      ∧ OperatorKO7.ToolSearchFragmentCoveragePerFamily.toolSearchFragmentGroup
          ToolSearchFragmentFamily.matrixArcticRowSum
        = OperatorKO7.ToolSearchFragmentCoveragePerFamily.ToolSearchFragmentGroup.matrixProjection) := by
  exact
    (matrix_projection_family_group_catalog ToolSearchFragmentFamily.matrixArcticRowSum).2
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

example {Sys : OperatorKO7.StepDuplicating.StepDuplicatingSchema.StepDuplicatingSystem} :
    ToolSearchResidualBoundaryCatalog Sys := by
  exact tool_search_exact_inventory_implies_boundary_catalog (Sys := Sys)
    tool_search_fragment_exact_inventory

example :
    residualFragmentFamilyStatus ResidualFragmentFamily.unrestrictedMatrixClasses
      = CoverageStatus.residualExclusion := by
  exact residual_tool_search_families_have_residual_status _
    (residualToolSearchFamilies_complete _)

example :
    ToolSearchFragmentFamily.matrixTropicalRowSum ∈ theoremBackedToolSearchFamilies ↔
      ToolSearchFragmentFamily.matrixTropicalRowSum = .directAdditive
      ∨ ToolSearchFragmentFamily.matrixTropicalRowSum = .directAffine
      ∨ ToolSearchFragmentFamily.matrixTropicalRowSum = .directQuadratic
      ∨ ToolSearchFragmentFamily.matrixTropicalRowSum = .directMultilinear
      ∨ ToolSearchFragmentFamily.matrixTropicalRowSum = .directPolynomial
      ∨ ToolSearchFragmentFamily.matrixTropicalRowSum = .extendedCrossQuadratic
      ∨ ToolSearchFragmentFamily.matrixTropicalRowSum = .extendedMaxPlus
      ∨ ToolSearchFragmentFamily.matrixTropicalRowSum = .extendedWPOPolynomial
      ∨ ToolSearchFragmentFamily.matrixTropicalRowSum = .matrixFixedRow
      ∨ ToolSearchFragmentFamily.matrixTropicalRowSum = .matrixRowSum
      ∨ ToolSearchFragmentFamily.matrixTropicalRowSum = .matrixArcticFixedRow
      ∨ ToolSearchFragmentFamily.matrixTropicalRowSum = .matrixArcticRowSum
      ∨ ToolSearchFragmentFamily.matrixTropicalRowSum = .matrixTropicalFixedRow
      ∨ ToolSearchFragmentFamily.matrixTropicalRowSum = .matrixTropicalRowSum := by
  exact theoremBackedToolSearchFamilies_complete_exact _

end ToolSearchFragmentCoverageExactnessReach
