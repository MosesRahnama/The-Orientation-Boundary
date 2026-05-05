import OperatorKO7.Meta.ToolSearchFragmentCoverage_ResidualBoundary
import OperatorKO7.Meta.MatrixResidualClosureCatalog
import OperatorKO7.Meta.ResidualMethodClosureCatalog

/-!
# Tool Search Fragment Coverage Final Catalog

This module packages the paper-facing final M4 tool-search coverage surface:
certificate, exact finite inventory, honest residual boundary, and exact
group-membership catalogs.
-/

namespace OperatorKO7.ToolSearchFragmentCoverageFinalCatalog

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.ToolSearchFragmentCoverage
open OperatorKO7.ToolSearchFragmentCoverageStatus
open OperatorKO7.ToolSearchFragmentCoveragePerFamily
open OperatorKO7.ToolSearchFragmentCoverageListAudit
open OperatorKO7.ToolSearchFragmentCoverageExactness
open OperatorKO7.ToolSearchFragmentCoverageResidualBoundary
open OperatorKO7.MatrixResidualTaxonomy
open OperatorKO7.MatrixResidualClosureCatalog
open OperatorKO7.ResidualMethodClosureCatalog

/-- Paper-facing final theorem surface for the M4 tool-search coverage stack.
This is a named record rather than a loose conjunction so downstream files can
project exact fields without repacking the whole surface. -/
structure ToolSearchFragmentFinalCatalog (Sys : StepDuplicatingSystem) where
  certificate : ToolSearchCoverageCertificate Sys
  exactInventory : ToolSearchFragmentExactInventory
  residualBoundary : ToolSearchResidualBoundaryCatalog Sys
  matrixResidualClosureCertificate : MatrixResidualClosureCertificate
  residualMethodClosureCertificate : ResidualMethodClosureCertificate
  theoremBackedFamilyCovered :
    ∀ family : ToolSearchFragmentFamily,
      family ∈ theoremBackedToolSearchFamilies →
        coveredFragmentFamilyStatus family = CoverageStatus.covered
          ∧ familyCoveredByCertificate Sys family
  residualFamilyExclusion :
    ∀ family : ResidualFragmentFamily,
      family ∈ residualToolSearchFamilies →
        residualFragmentFamilyStatus family = CoverageStatus.residualExclusion
  directScalarGroupExact :
    ∀ family : ToolSearchFragmentFamily,
      (family ∈ theoremBackedToolSearchFamilies
        ∧ toolSearchFragmentGroup family = ToolSearchFragmentGroup.directScalar) ↔
        family = .directAdditive
        ∨ family = .directAffine
        ∨ family = .directQuadratic
        ∨ family = .directMultilinear
        ∨ family = .directPolynomial
  extendedDirectGroupExact :
    ∀ family : ToolSearchFragmentFamily,
      (family ∈ theoremBackedToolSearchFamilies
        ∧ toolSearchFragmentGroup family = ToolSearchFragmentGroup.extendedDirect) ↔
        family = .extendedCrossQuadratic
        ∨ family = .extendedMaxPlus
        ∨ family = .extendedWPOPolynomial
  matrixProjectionGroupExact :
    ∀ family : ToolSearchFragmentFamily,
      (family ∈ theoremBackedToolSearchFamilies
        ∧ toolSearchFragmentGroup family = ToolSearchFragmentGroup.matrixProjection) ↔
        family = .matrixFixedRow
        ∨ family = .matrixRowSum
        ∨ family = .matrixArcticFixedRow
        ∨ family = .matrixArcticRowSum
        ∨ family = .matrixTropicalFixedRow
        ∨ family = .matrixTropicalRowSum

/-- The paper-facing final M4 tool-search catalog is already carried by the
certificate, exactness, and residual-boundary layers. -/
theorem tool_search_fragment_final_catalog
    {Sys : StepDuplicatingSystem} : ToolSearchFragmentFinalCatalog Sys := by
  exact {
    certificate := tool_search_coverage_certificate (Sys := Sys)
    exactInventory := tool_search_fragment_exact_inventory
    residualBoundary := tool_search_residual_boundary_catalog (Sys := Sys)
    matrixResidualClosureCertificate := matrixResidualClosureCertificate
    residualMethodClosureCertificate := residualMethodClosureCertificate
    theoremBackedFamilyCovered :=
      covered_tool_search_families_have_status_and_certificate (Sys := Sys)
    residualFamilyExclusion := residual_tool_search_families_have_residual_status
    directScalarGroupExact := direct_scalar_family_group_catalog
    extendedDirectGroupExact := extended_direct_family_group_catalog
    matrixProjectionGroupExact := matrix_projection_family_group_catalog
  }

/-- The final catalog projects the theorem-backed coverage certificate. -/
theorem tool_search_fragment_final_projects_certificate
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    ToolSearchCoverageCertificate Sys := by
  exact h.certificate

/-- The final catalog projects the exact finite-inventory package. -/
theorem tool_search_fragment_final_projects_exact_inventory
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    ToolSearchFragmentExactInventory := by
  exact h.exactInventory

/-- The final catalog projects the theorem-backed family surface. -/
theorem tool_search_fragment_final_projects_theoremBacked_family
    {Sys : StepDuplicatingSystem}
    (_h : ToolSearchFragmentFinalCatalog Sys)
    (family : ToolSearchFragmentFamily) :
    family ∈ theoremBackedToolSearchFamilies := by
  exact theoremBackedToolSearchFamilies_complete family

/-- The final catalog projects the residual family surface. -/
theorem tool_search_fragment_final_projects_residual_family
    {Sys : StepDuplicatingSystem}
    (_h : ToolSearchFragmentFinalCatalog Sys)
    (family : ResidualFragmentFamily) :
    family ∈ residualToolSearchFamilies := by
  exact residualToolSearchFamilies_complete family

/-- The final catalog projects the honest residual-boundary package. -/
theorem tool_search_fragment_final_projects_residual_boundary
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    ToolSearchResidualBoundaryCatalog Sys := by
  exact h.residualBoundary

/-- The final catalog projects the exact matrix residual closure certificate. -/
theorem tool_search_fragment_final_projects_matrix_residual_closure_certificate
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    MatrixResidualClosureCertificate := by
  exact h.matrixResidualClosureCertificate

/-- The final catalog projects the cross-family residual-method closure certificate. -/
theorem tool_search_fragment_final_projects_residual_method_closure_certificate
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    ResidualMethodClosureCertificate := by
  exact h.residualMethodClosureCertificate

/-- The final catalog projects the exact final residual-matrix closure catalog. -/
theorem tool_search_fragment_final_projects_matrix_residual_closure_catalog
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    MatrixResidualClosureFinalCatalog :=
  (tool_search_fragment_final_projects_matrix_residual_closure_certificate h).finalCatalog

/-- The final catalog projects the accepted paper-facing matrix residual status catalog. -/
theorem tool_search_fragment_final_projects_matrix_residual_status_catalog
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    MatrixResidualStatusCatalog :=
  (tool_search_fragment_final_projects_matrix_residual_closure_certificate h).statusCatalog

/-- The final catalog projects the exact cross-family residual-method surface. -/
theorem tool_search_fragment_final_projects_residual_method_closure_catalog
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    ResidualMethodClosureCatalogSurface :=
  (tool_search_fragment_final_projects_residual_method_closure_certificate h).catalog

/-- The final catalog still exhibits a conditional-boundary row in the cross-family residual surface. -/
theorem tool_search_fragment_final_projects_residual_method_conditional_boundary_witness
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    ∃ row : ResidualMethodClosureCatalogRow,
      row ∈ residualMethodClosureCatalogRows ∧
      residualMethodClosureCatalogRowStatus row = .conditionalBoundary := by
  exact residualMethodClosureCatalog_exhibits_conditionalBoundary
    (tool_search_fragment_final_projects_residual_method_closure_catalog h)

/-- The final catalog still exhibits an open-residual row in the cross-family residual surface. -/
theorem tool_search_fragment_final_projects_residual_method_open_residual_witness
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    ∃ row : ResidualMethodClosureCatalogRow,
      row ∈ residualMethodClosureCatalogRows ∧
      residualMethodClosureCatalogRowStatus row = .openResidual := by
  exact residualMethodClosureCatalog_exhibits_openResidual
    (tool_search_fragment_final_projects_residual_method_closure_catalog h)

/-- The final catalog still exposes the non-overclaim theorem for cross-family residual closure. -/
theorem tool_search_fragment_final_projects_residual_method_not_universally_closed
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    ∃ row : ResidualMethodClosureCatalogRow,
      row ∈ residualMethodClosureCatalogRows ∧
      (residualMethodClosureCatalogRowStatus row = .openResidual ∨
        residualMethodClosureCatalogRowStatus row = .conditionalBoundary) :=
  (tool_search_fragment_final_projects_residual_method_closure_certificate h).notUniversallyClosed

/-- Covered theorem-backed families project to covered status and a
certificate witness through the final catalog. -/
theorem tool_search_fragment_final_covered_family_status_and_certificate
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys)
    (family : ToolSearchFragmentFamily)
    (hfamily : family ∈ theoremBackedToolSearchFamilies) :
    coveredFragmentFamilyStatus family = CoverageStatus.covered
      ∧ familyCoveredByCertificate Sys family := by
  exact h.theoremBackedFamilyCovered family hfamily

/-- Residual families project only to their residual status label through the
final catalog. -/
theorem tool_search_fragment_final_residual_family_status
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys)
    (family : ResidualFragmentFamily)
    (hfamily : family ∈ residualToolSearchFamilies) :
    residualFragmentFamilyStatus family = CoverageStatus.residualExclusion := by
  exact h.residualFamilyExclusion family hfamily

/-- The direct-scalar exact group catalog projects from the final catalog. -/
theorem tool_search_fragment_final_direct_scalar_group_exact
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys)
    (family : ToolSearchFragmentFamily) :
    (family ∈ theoremBackedToolSearchFamilies
      ∧ toolSearchFragmentGroup family = ToolSearchFragmentGroup.directScalar) ↔
      family = .directAdditive
      ∨ family = .directAffine
      ∨ family = .directQuadratic
      ∨ family = .directMultilinear
      ∨ family = .directPolynomial := by
  exact h.directScalarGroupExact family

/-- The extended-direct exact group catalog projects from the final catalog. -/
theorem tool_search_fragment_final_extended_direct_group_exact
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys)
    (family : ToolSearchFragmentFamily) :
    (family ∈ theoremBackedToolSearchFamilies
      ∧ toolSearchFragmentGroup family = ToolSearchFragmentGroup.extendedDirect) ↔
      family = .extendedCrossQuadratic
      ∨ family = .extendedMaxPlus
      ∨ family = .extendedWPOPolynomial := by
  exact h.extendedDirectGroupExact family

/-- The matrix-projection exact group catalog projects from the final catalog. -/
theorem tool_search_fragment_final_matrix_projection_group_exact
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys)
    (family : ToolSearchFragmentFamily) :
    (family ∈ theoremBackedToolSearchFamilies
      ∧ toolSearchFragmentGroup family = ToolSearchFragmentGroup.matrixProjection) ↔
      family = .matrixFixedRow
      ∨ family = .matrixRowSum
      ∨ family = .matrixArcticFixedRow
      ∨ family = .matrixArcticRowSum
      ∨ family = .matrixTropicalFixedRow
      ∨ family = .matrixTropicalRowSum := by
  exact h.matrixProjectionGroupExact family

/-- The final catalog keeps the aggregate unrestricted-matrix residual row honest
by projecting the exact non-overclaim matrix statuses. -/
theorem tool_search_fragment_final_projects_matrix_residual_non_overclaim_status
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    matrixResidualClosureStatus .arcticFull = .licensedEscape
      ∧ matrixResidualClosureStatus .tropicalFull = .licensedEscape
      ∧ matrixResidualClosureStatus .importDependentMatrix = .licensedEscape
      ∧ matrixResidualClosureStatus .unconstrainedRelation = .notYetMethodClass := by
  rcases tool_search_fragment_final_projects_matrix_residual_status_catalog h with
    ⟨_, hrest1⟩
  rcases hrest1 with ⟨_, hrest2⟩
  rcases hrest2 with ⟨_, hrest3⟩
  rcases hrest3 with ⟨_, hrest4⟩
  rcases hrest4 with ⟨_, hrest5⟩
  rcases hrest5 with ⟨harctic, hrest6⟩
  rcases hrest6 with ⟨htropical, hrest7⟩
  rcases hrest7 with ⟨himport, hunconstrained⟩
  exact ⟨harctic, htropical, himport, hunconstrained⟩

/-- The final catalog keeps the FBI residual-adequacy row explicitly conditional. -/
theorem tool_search_fragment_final_projects_fbi_conditional_boundary_status
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    residualMethodClosureCatalogRowStatus
      ResidualMethodClosureCatalogRow.fbiResidualAdequacyBoundary =
        .conditionalBoundary := by
  exact residualMethodClosureCatalog_projects_status
    (tool_search_fragment_final_projects_residual_method_closure_catalog h)
    .fbiResidualAdequacyBoundary

/-- The final catalog keeps the nonlinear unconstrained row explicitly open. -/
theorem tool_search_fragment_final_projects_nonlinear_open_residual_status
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    residualMethodClosureCatalogRowStatus
      ResidualMethodClosureCatalogRow.nonlinearUnconstrainedDirect =
        .openResidual := by
  exact residualMethodClosureCatalog_projects_status
    (tool_search_fragment_final_projects_residual_method_closure_catalog h)
    .nonlinearUnconstrainedDirect

/-- The final catalog exposes the explicit residual non-overclaim rows rather than
silently collapsing them into universal closure. -/
theorem tool_search_fragment_final_projects_explicit_non_overclaim_status
    {Sys : StepDuplicatingSystem}
    (h : ToolSearchFragmentFinalCatalog Sys) :
    residualMethodClosureCatalogRowStatus
        ResidualMethodClosureCatalogRow.fbiResidualAdequacyBoundary =
          .conditionalBoundary
      ∧ residualMethodClosureCatalogRowStatus
          ResidualMethodClosureCatalogRow.nonlinearUnconstrainedDirect =
            .openResidual := by
  exact ⟨tool_search_fragment_final_projects_fbi_conditional_boundary_status h,
    tool_search_fragment_final_projects_nonlinear_open_residual_status h⟩

end OperatorKO7.ToolSearchFragmentCoverageFinalCatalog
