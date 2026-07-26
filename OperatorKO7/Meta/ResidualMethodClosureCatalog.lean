import OperatorKO7.Meta.MatrixResidualClosureCatalog
import OperatorKO7.Meta.FBI_FinalCatalog
import OperatorKO7.Meta.GenericDPMethodBoundary
import OperatorKO7.Meta.SemanticMethodBoundary
import OperatorKO7.Meta.NonlinearDirectBoundary

/-!
# Residual Method Closure Catalog

The cross-family residual inventory is closed row by row.  Each of the twenty-
five rows carries a theorem-backed support proposition from its owning module;
the status vocabulary contains no open, conditional, or not-yet-classified
constructor.  The catalog is finite and exact, and the certificate exposes
universal support and closed-status projections for every row.
-/

namespace OperatorKO7.ResidualMethodClosureCatalog

open OperatorKO7.ToolSearchFragmentCoverageStatus
open OperatorKO7.MatrixResidualClosureCatalog
open OperatorKO7.FBIFinalCatalog
open OperatorKO7.GenericDPMethodBoundary
open OperatorKO7.SemanticMethodBoundary
open OperatorKO7.NonlinearDirectBoundary

/-- Source-family tags used by the catalog rows. -/
inductive ResidualMethodClosureCatalogSource where
  | matrix
  | fbi
  | genericDP
  | semantic
  | nonlinear
  deriving DecidableEq, Repr

/-- Theorem-backed status tags used by the closed catalog. -/
inductive ResidualMethodClosureStatus where
  | blocked
  | closedByLeanTheorem
  | reducedToExistingTheorem
  | licensedEscape
  | certifiedSuccess
  deriving DecidableEq, Repr

/-- Exact cross-family rows in the residual-method catalog. -/
inductive ResidualMethodClosureCatalogRow where
  | matrixComponentwiseWeakStrictReduction
  | matrixParetoProductReduction
  | matrixLexPriorityReduction
  | matrixPermutationLexPriorityReduction
  | matrixScalarizableWeightReduction
  | matrixArcticFullLicensedEscape
  | matrixTropicalFullLicensedEscape
  | matrixImportDependentLicensedEscape
  | matrixUnconstrainedRelationClosedByExactSplit
  | fbiFinalRouteStatusCatalog
  | fbiAdequacyBoundaryClosed
  | genericDPDirectPairExtraction
  | genericDPTransformedCallRoute
  | genericDPImportedOrdering
  | genericDPCertifiedEngine
  | semanticTransparentWholeTermMeasure
  | semanticImportedModelLogicalRelation
  | semanticCertifiedExternalEngine
  | nonlinearBoundedDegreeProjection
  | nonlinearBoundedCrossTermQuadratic
  | nonlinearBoundedMultilinear
  | nonlinearWpoPolynomialBranch
  | nonlinearMaxPlusDirectFragment
  | nonlinearGlobalCrossCoupledWitness
  | nonlinearUnconstrainedDirectExactLawBoundary
  deriving DecidableEq, Repr

/-- Enumeration of every row constructor. -/
def residualMethodClosureCatalogRows : List ResidualMethodClosureCatalogRow :=
  [ .matrixComponentwiseWeakStrictReduction
  , .matrixParetoProductReduction
  , .matrixLexPriorityReduction
  , .matrixPermutationLexPriorityReduction
  , .matrixScalarizableWeightReduction
  , .matrixArcticFullLicensedEscape
  , .matrixTropicalFullLicensedEscape
  , .matrixImportDependentLicensedEscape
  , .matrixUnconstrainedRelationClosedByExactSplit
  , .fbiFinalRouteStatusCatalog
  , .fbiAdequacyBoundaryClosed
  , .genericDPDirectPairExtraction
  , .genericDPTransformedCallRoute
  , .genericDPImportedOrdering
  , .genericDPCertifiedEngine
  , .semanticTransparentWholeTermMeasure
  , .semanticImportedModelLogicalRelation
  , .semanticCertifiedExternalEngine
  , .nonlinearBoundedDegreeProjection
  , .nonlinearBoundedCrossTermQuadratic
  , .nonlinearBoundedMultilinear
  , .nonlinearWpoPolynomialBranch
  , .nonlinearMaxPlusDirectFragment
  , .nonlinearGlobalCrossCoupledWitness
  , .nonlinearUnconstrainedDirectExactLawBoundary
  ]

/-- Source-family assignment. -/
def residualMethodClosureCatalogRowSource :
    ResidualMethodClosureCatalogRow → ResidualMethodClosureCatalogSource
  | .matrixComponentwiseWeakStrictReduction
  | .matrixParetoProductReduction
  | .matrixLexPriorityReduction
  | .matrixPermutationLexPriorityReduction
  | .matrixScalarizableWeightReduction
  | .matrixArcticFullLicensedEscape
  | .matrixTropicalFullLicensedEscape
  | .matrixImportDependentLicensedEscape
  | .matrixUnconstrainedRelationClosedByExactSplit => .matrix
  | .fbiFinalRouteStatusCatalog
  | .fbiAdequacyBoundaryClosed => .fbi
  | .genericDPDirectPairExtraction
  | .genericDPTransformedCallRoute
  | .genericDPImportedOrdering
  | .genericDPCertifiedEngine => .genericDP
  | .semanticTransparentWholeTermMeasure
  | .semanticImportedModelLogicalRelation
  | .semanticCertifiedExternalEngine => .semantic
  | .nonlinearBoundedDegreeProjection
  | .nonlinearBoundedCrossTermQuadratic
  | .nonlinearBoundedMultilinear
  | .nonlinearWpoPolynomialBranch
  | .nonlinearMaxPlusDirectFragment
  | .nonlinearGlobalCrossCoupledWitness
  | .nonlinearUnconstrainedDirectExactLawBoundary => .nonlinear

/-- Closed status assignment. -/
def residualMethodClosureCatalogRowStatus :
    ResidualMethodClosureCatalogRow → ResidualMethodClosureStatus
  | .matrixComponentwiseWeakStrictReduction
  | .matrixParetoProductReduction
  | .matrixLexPriorityReduction
  | .matrixPermutationLexPriorityReduction
  | .matrixScalarizableWeightReduction => .reducedToExistingTheorem
  | .matrixArcticFullLicensedEscape
  | .matrixTropicalFullLicensedEscape
  | .matrixImportDependentLicensedEscape => .licensedEscape
  | .matrixUnconstrainedRelationClosedByExactSplit => .closedByLeanTheorem
  | .fbiFinalRouteStatusCatalog
  | .fbiAdequacyBoundaryClosed => .closedByLeanTheorem
  | .genericDPDirectPairExtraction => .blocked
  | .genericDPTransformedCallRoute
  | .genericDPImportedOrdering => .licensedEscape
  | .genericDPCertifiedEngine => .certifiedSuccess
  | .semanticTransparentWholeTermMeasure => .reducedToExistingTheorem
  | .semanticImportedModelLogicalRelation => .licensedEscape
  | .semanticCertifiedExternalEngine => .certifiedSuccess
  | .nonlinearBoundedDegreeProjection => .reducedToExistingTheorem
  | .nonlinearBoundedCrossTermQuadratic
  | .nonlinearBoundedMultilinear
  | .nonlinearWpoPolynomialBranch
  | .nonlinearMaxPlusDirectFragment => .closedByLeanTheorem
  | .nonlinearGlobalCrossCoupledWitness => .licensedEscape
  | .nonlinearUnconstrainedDirectExactLawBoundary => .closedByLeanTheorem

/-- Row-specific theorem support. -/
def ResidualMethodClosureCatalogSupported :
    ResidualMethodClosureCatalogRow → Prop
  | .matrixComponentwiseWeakStrictReduction
  | .matrixParetoProductReduction
  | .matrixLexPriorityReduction
  | .matrixPermutationLexPriorityReduction
  | .matrixScalarizableWeightReduction
  | .matrixArcticFullLicensedEscape
  | .matrixTropicalFullLicensedEscape
  | .matrixImportDependentLicensedEscape =>
      MatrixResidualClosureFinalCatalog ∧ MatrixResidualStatusCatalog
  | .matrixUnconstrainedRelationClosedByExactSplit =>
      UnconstrainedRelationClosedByUnrestrictedSplitPayload
  | .fbiFinalRouteStatusCatalog =>
      FBIFinalRouteStatusCatalog
  | .fbiAdequacyBoundaryClosed =>
      FBIResidualAdequacyBoundaryCatalog ∧ FBIAdequacyBoundaryCatalog
  | .genericDPDirectPairExtraction =>
      GenericDPMethodSupported .directPairExtraction
  | .genericDPTransformedCallRoute =>
      GenericDPMethodSupported .transformedCallRoute
  | .genericDPImportedOrdering =>
      GenericDPMethodSupported .importedOrdering
  | .genericDPCertifiedEngine =>
      GenericDPMethodSupported .certifiedEngine
  | .semanticTransparentWholeTermMeasure =>
      SemanticMethodSupported .transparentWholeTermMeasure
  | .semanticImportedModelLogicalRelation =>
      SemanticMethodSupported .importedModelLogicalRelation
  | .semanticCertifiedExternalEngine =>
      SemanticMethodSupported .certifiedExternalEngine
  | .nonlinearBoundedDegreeProjection =>
      NonlinearDirectBoundarySupported .boundedDegreeDirectTransparentPolynomial
  | .nonlinearBoundedCrossTermQuadratic =>
      NonlinearDirectBoundarySupported .boundedCrossTermQuadratic
  | .nonlinearBoundedMultilinear =>
      NonlinearDirectBoundarySupported .boundedMultilinear
  | .nonlinearWpoPolynomialBranch =>
      NonlinearDirectBoundarySupported .wpoPolynomialBranch
  | .nonlinearMaxPlusDirectFragment =>
      NonlinearDirectBoundarySupported .maxPlusDirectFragment
  | .nonlinearGlobalCrossCoupledWitness =>
      NonlinearDirectBoundarySupported .globalCrossCoupledWitness
  | .nonlinearUnconstrainedDirectExactLawBoundary =>
      NonlinearDirectBoundarySupported .unconstrainedNonlinearDirect

/-- The row inventory has no duplicates. -/
theorem residualMethodClosureCatalogRows_nodup :
    residualMethodClosureCatalogRows.Nodup := by
  decide

/-- The row inventory has exactly twenty-five entries. -/
theorem residualMethodClosureCatalogRows_length :
    residualMethodClosureCatalogRows.length = 25 := by
  rfl

/-- Exact row membership. -/
theorem residualMethodClosureCatalogRows_complete_exact
    (row : ResidualMethodClosureCatalogRow) :
    row ∈ residualMethodClosureCatalogRows := by
  cases row <;> simp [residualMethodClosureCatalogRows]

/-- Every row carries its owning theorem support. -/
theorem residualMethodClosureCatalogSupported_holds
    (row : ResidualMethodClosureCatalogRow) :
    ResidualMethodClosureCatalogSupported row := by
  cases row with
  | matrixComponentwiseWeakStrictReduction
  | matrixParetoProductReduction
  | matrixLexPriorityReduction
  | matrixPermutationLexPriorityReduction
  | matrixScalarizableWeightReduction
  | matrixArcticFullLicensedEscape
  | matrixTropicalFullLicensedEscape
  | matrixImportDependentLicensedEscape =>
      exact ⟨matrixResidualClosureCertificate_projects_finalCatalog,
        matrixResidualClosureCertificate_projects_statusCatalog⟩
  | matrixUnconstrainedRelationClosedByExactSplit =>
      exact OperatorKO7.MatrixUnrestrictedSplit.unrestricted_matrix_classes_split_final_catalog_unconditional
  | fbiFinalRouteStatusCatalog =>
      exact fbi_final_catalog_certificate_projects_route_status_catalog
  | fbiAdequacyBoundaryClosed =>
      exact ⟨fbi_final_catalog_certificate_projects_residual_boundary,
        fbi_adequacy_boundary_catalog⟩
  | genericDPDirectPairExtraction =>
      exact genericDPMethodSupported_holds .directPairExtraction
  | genericDPTransformedCallRoute =>
      exact genericDPMethodSupported_holds .transformedCallRoute
  | genericDPImportedOrdering =>
      exact genericDPMethodSupported_holds .importedOrdering
  | genericDPCertifiedEngine =>
      exact genericDPMethodSupported_holds .certifiedEngine
  | semanticTransparentWholeTermMeasure =>
      exact semanticMethodSupported_holds .transparentWholeTermMeasure
  | semanticImportedModelLogicalRelation =>
      exact semanticMethodSupported_holds .importedModelLogicalRelation
  | semanticCertifiedExternalEngine =>
      exact semanticMethodSupported_holds .certifiedExternalEngine
  | nonlinearBoundedDegreeProjection =>
      exact boundedDegreeDirectTransparentPolynomial_requires_projection
  | nonlinearBoundedCrossTermQuadratic =>
      exact boundedCrossTermQuadratic_blocked
  | nonlinearBoundedMultilinear =>
      exact boundedMultilinear_blocked
  | nonlinearWpoPolynomialBranch =>
      exact wpoPolynomialBranch_blocked
  | nonlinearMaxPlusDirectFragment =>
      exact maxPlusDirectFragment_blocked
  | nonlinearGlobalCrossCoupledWitness =>
      exact globalCrossCoupledWitness_licensed_escape
  | nonlinearUnconstrainedDirectExactLawBoundary =>
      exact unconstrainedNonlinearDirect_exactLawBoundary

/-- Every row status is one of the five theorem-backed terminal statuses. -/
theorem residualMethodClosureCatalogRowStatus_terminal
    (row : ResidualMethodClosureCatalogRow) :
    residualMethodClosureCatalogRowStatus row = .blocked ∨
      residualMethodClosureCatalogRowStatus row = .closedByLeanTheorem ∨
      residualMethodClosureCatalogRowStatus row = .reducedToExistingTheorem ∨
      residualMethodClosureCatalogRowStatus row = .licensedEscape ∨
      residualMethodClosureCatalogRowStatus row = .certifiedSuccess := by
  cases row <;> simp [residualMethodClosureCatalogRowStatus]

/-- Exact closed catalog surface. -/
abbrev ResidualMethodClosureCatalogSurface : Prop :=
  ∀ row : ResidualMethodClosureCatalogRow,
    row ∈ residualMethodClosureCatalogRows ∧
      ResidualMethodClosureCatalogSupported row ∧
      (residualMethodClosureCatalogRowStatus row = .blocked ∨
        residualMethodClosureCatalogRowStatus row = .closedByLeanTheorem ∨
        residualMethodClosureCatalogRowStatus row = .reducedToExistingTheorem ∨
        residualMethodClosureCatalogRowStatus row = .licensedEscape ∨
        residualMethodClosureCatalogRowStatus row = .certifiedSuccess)

/-- The complete twenty-five-row surface is theorem-backed. -/
theorem residualMethodClosureCatalog_exact :
    ResidualMethodClosureCatalogSurface := by
  intro row
  exact ⟨residualMethodClosureCatalogRows_complete_exact row,
    residualMethodClosureCatalogSupported_holds row,
    residualMethodClosureCatalogRowStatus_terminal row⟩

/-- Project row support from the closed catalog. -/
theorem residualMethodClosureCatalog_projects_support
    (h : ResidualMethodClosureCatalogSurface)
    (row : ResidualMethodClosureCatalogRow) :
    ResidualMethodClosureCatalogSupported row :=
  (h row).2.1

/-- Project terminal status from the closed catalog. -/
theorem residualMethodClosureCatalog_projects_terminal_status
    (h : ResidualMethodClosureCatalogSurface)
    (row : ResidualMethodClosureCatalogRow) :
    residualMethodClosureCatalogRowStatus row = .blocked ∨
      residualMethodClosureCatalogRowStatus row = .closedByLeanTheorem ∨
      residualMethodClosureCatalogRowStatus row = .reducedToExistingTheorem ∨
      residualMethodClosureCatalogRowStatus row = .licensedEscape ∨
      residualMethodClosureCatalogRowStatus row = .certifiedSuccess :=
  (h row).2.2

/-- Universal closeout certificate for the residual-method inventory. -/
structure ResidualMethodClosureCertificate : Prop where
  catalog : ResidualMethodClosureCatalogSurface
  rowCount : residualMethodClosureCatalogRows.length = 25
  rowsNoDup : residualMethodClosureCatalogRows.Nodup
  allRowsSupported :
    ∀ row : ResidualMethodClosureCatalogRow,
      ResidualMethodClosureCatalogSupported row
  allRowsTerminal :
    ∀ row : ResidualMethodClosureCatalogRow,
      residualMethodClosureCatalogRowStatus row = .blocked ∨
        residualMethodClosureCatalogRowStatus row = .closedByLeanTheorem ∨
        residualMethodClosureCatalogRowStatus row = .reducedToExistingTheorem ∨
        residualMethodClosureCatalogRowStatus row = .licensedEscape ∨
        residualMethodClosureCatalogRowStatus row = .certifiedSuccess

/-- Fully closed residual-method certificate. -/
theorem residualMethodClosureCertificate :
    ResidualMethodClosureCertificate where
  catalog := residualMethodClosureCatalog_exact
  rowCount := residualMethodClosureCatalogRows_length
  rowsNoDup := residualMethodClosureCatalogRows_nodup
  allRowsSupported := residualMethodClosureCatalogSupported_holds
  allRowsTerminal := residualMethodClosureCatalogRowStatus_terminal

/-- Certificate projection to the exact catalog. -/
theorem residualMethodClosureCertificate_projects_catalog :
    ResidualMethodClosureCatalogSurface :=
  residualMethodClosureCertificate.catalog

/-- Certificate projection to universal row support. -/
theorem residualMethodClosureCertificate_projects_allRowsSupported :
    ∀ row : ResidualMethodClosureCatalogRow,
      ResidualMethodClosureCatalogSupported row :=
  residualMethodClosureCertificate.allRowsSupported

/-- Certificate projection to universal terminal status. -/
theorem residualMethodClosureCertificate_projects_allRowsTerminal :
    ∀ row : ResidualMethodClosureCatalogRow,
      residualMethodClosureCatalogRowStatus row = .blocked ∨
        residualMethodClosureCatalogRowStatus row = .closedByLeanTheorem ∨
        residualMethodClosureCatalogRowStatus row = .reducedToExistingTheorem ∨
        residualMethodClosureCatalogRowStatus row = .licensedEscape ∨
        residualMethodClosureCatalogRowStatus row = .certifiedSuccess :=
  residualMethodClosureCertificate.allRowsTerminal

end OperatorKO7.ResidualMethodClosureCatalog
