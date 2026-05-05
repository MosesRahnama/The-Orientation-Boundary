import OperatorKO7.Meta.MatrixResidualClosureCatalog
import OperatorKO7.Meta.FBI_FinalCatalog
import OperatorKO7.Meta.GenericDPMethodBoundary
import OperatorKO7.Meta.SemanticMethodBoundary
import OperatorKO7.Meta.NonlinearDirectBoundary

namespace OperatorKO7.ResidualMethodClosureCatalog

open OperatorKO7.ToolSearchFragmentCoverageStatus
open OperatorKO7.MatrixResidualClosureCatalog
open OperatorKO7.FBIFinalCatalog
open OperatorKO7.GenericDPMethodBoundary
open OperatorKO7.SemanticMethodBoundary
open OperatorKO7.NonlinearDirectBoundary

/-- Source surface imported by each cross-family residual catalog row. -/
inductive ResidualMethodClosureCatalogSource where
  | matrix
  | fbi
  | genericDP
  | semantic
  | nonlinear
  deriving DecidableEq, Repr

/-- Common paper-facing status vocabulary for the cross-family residual closure catalog. -/
inductive ResidualMethodClosureStatus where
  | blocked
  | closedByLeanTheorem
  | reducedToExistingTheorem
  | licensedEscape
  | certifiedSuccess
  | conditionalBoundary
  | openResidual
  | notYetMethodClass
  deriving DecidableEq, Repr

/-- Exact cross-family rows currently integrated into the WS-G residual closure catalog. -/
inductive ResidualMethodClosureCatalogRow where
  | matrixComponentwiseWeakStrictReduction
  | matrixParetoProductReduction
  | matrixLexPriorityReduction
  | matrixPermutationLexPriorityReduction
  | matrixScalarizableWeightReduction
  | matrixArcticFullLicensedEscape
  | matrixTropicalFullLicensedEscape
  | matrixImportDependentLicensedEscape
  | matrixUnconstrainedRelationNotYetMethodClass
  | fbiFinalRouteStatusCatalog
  | fbiResidualAdequacyBoundary
  | genericDPDirectPairExtraction
  | genericDPTransformedCallRoute
  | genericDPImportedOrdering
  | genericDPCertifiedProcedure
  | semanticTransparentWholeTermMeasure
  | semanticImportedModelLogicalRelation
  | semanticCertifiedExternalProcedure
  | nonlinearBoundedDegreeProjection
  | nonlinearBoundedCrossTermQuadratic
  | nonlinearBoundedMultilinear
  | nonlinearWpoPolynomialBranch
  | nonlinearMaxPlusDirectFragment
  | nonlinearGlobalCrossCoupledWitness
  | nonlinearUnconstrainedDirect
  deriving DecidableEq, Repr

/-- Exact finite inventory of the cross-family residual closure rows. -/
def residualMethodClosureCatalogRows : List ResidualMethodClosureCatalogRow :=
  [ .matrixComponentwiseWeakStrictReduction
  , .matrixParetoProductReduction
  , .matrixLexPriorityReduction
  , .matrixPermutationLexPriorityReduction
  , .matrixScalarizableWeightReduction
  , .matrixArcticFullLicensedEscape
  , .matrixTropicalFullLicensedEscape
  , .matrixImportDependentLicensedEscape
  , .matrixUnconstrainedRelationNotYetMethodClass
  , .fbiFinalRouteStatusCatalog
  , .fbiResidualAdequacyBoundary
  , .genericDPDirectPairExtraction
  , .genericDPTransformedCallRoute
  , .genericDPImportedOrdering
  , .genericDPCertifiedProcedure
  , .semanticTransparentWholeTermMeasure
  , .semanticImportedModelLogicalRelation
  , .semanticCertifiedExternalProcedure
  , .nonlinearBoundedDegreeProjection
  , .nonlinearBoundedCrossTermQuadratic
  , .nonlinearBoundedMultilinear
  , .nonlinearWpoPolynomialBranch
  , .nonlinearMaxPlusDirectFragment
  , .nonlinearGlobalCrossCoupledWitness
  , .nonlinearUnconstrainedDirect
  ]

/-- Source-surface projection for each catalog row. -/
def residualMethodClosureCatalogRowSource :
    ResidualMethodClosureCatalogRow → ResidualMethodClosureCatalogSource
  | .matrixComponentwiseWeakStrictReduction => .matrix
  | .matrixParetoProductReduction => .matrix
  | .matrixLexPriorityReduction => .matrix
  | .matrixPermutationLexPriorityReduction => .matrix
  | .matrixScalarizableWeightReduction => .matrix
  | .matrixArcticFullLicensedEscape => .matrix
  | .matrixTropicalFullLicensedEscape => .matrix
  | .matrixImportDependentLicensedEscape => .matrix
  | .matrixUnconstrainedRelationNotYetMethodClass => .matrix
  | .fbiFinalRouteStatusCatalog => .fbi
  | .fbiResidualAdequacyBoundary => .fbi
  | .genericDPDirectPairExtraction => .genericDP
  | .genericDPTransformedCallRoute => .genericDP
  | .genericDPImportedOrdering => .genericDP
  | .genericDPCertifiedProcedure => .genericDP
  | .semanticTransparentWholeTermMeasure => .semantic
  | .semanticImportedModelLogicalRelation => .semantic
  | .semanticCertifiedExternalProcedure => .semantic
  | .nonlinearBoundedDegreeProjection => .nonlinear
  | .nonlinearBoundedCrossTermQuadratic => .nonlinear
  | .nonlinearBoundedMultilinear => .nonlinear
  | .nonlinearWpoPolynomialBranch => .nonlinear
  | .nonlinearMaxPlusDirectFragment => .nonlinear
  | .nonlinearGlobalCrossCoupledWitness => .nonlinear
  | .nonlinearUnconstrainedDirect => .nonlinear

/-- Common status projection for each cross-family residual row. -/
def residualMethodClosureCatalogRowStatus :
    ResidualMethodClosureCatalogRow → ResidualMethodClosureStatus
  | .matrixComponentwiseWeakStrictReduction => .reducedToExistingTheorem
  | .matrixParetoProductReduction => .reducedToExistingTheorem
  | .matrixLexPriorityReduction => .reducedToExistingTheorem
  | .matrixPermutationLexPriorityReduction => .reducedToExistingTheorem
  | .matrixScalarizableWeightReduction => .reducedToExistingTheorem
  | .matrixArcticFullLicensedEscape => .licensedEscape
  | .matrixTropicalFullLicensedEscape => .licensedEscape
  | .matrixImportDependentLicensedEscape => .licensedEscape
  | .matrixUnconstrainedRelationNotYetMethodClass => .notYetMethodClass
  | .fbiFinalRouteStatusCatalog => .closedByLeanTheorem
  | .fbiResidualAdequacyBoundary => .conditionalBoundary
  | .genericDPDirectPairExtraction => .blocked
  | .genericDPTransformedCallRoute => .licensedEscape
  | .genericDPImportedOrdering => .licensedEscape
  | .genericDPCertifiedProcedure => .certifiedSuccess
  | .semanticTransparentWholeTermMeasure => .reducedToExistingTheorem
  | .semanticImportedModelLogicalRelation => .licensedEscape
  | .semanticCertifiedExternalProcedure => .certifiedSuccess
  | .nonlinearBoundedDegreeProjection => .reducedToExistingTheorem
  | .nonlinearBoundedCrossTermQuadratic => .closedByLeanTheorem
  | .nonlinearBoundedMultilinear => .closedByLeanTheorem
  | .nonlinearWpoPolynomialBranch => .closedByLeanTheorem
  | .nonlinearMaxPlusDirectFragment => .closedByLeanTheorem
  | .nonlinearGlobalCrossCoupledWitness => .licensedEscape
  | .nonlinearUnconstrainedDirect => .openResidual

/-- The finite cross-family row inventory has no duplicates. -/
theorem residualMethodClosureCatalogRows_nodup :
    residualMethodClosureCatalogRows.Nodup := by
  decide

/-- The finite cross-family row inventory has exact size twenty-five. -/
theorem residualMethodClosureCatalogRows_length :
    residualMethodClosureCatalogRows.length = 25 := by
  rfl

/-- Exact membership characterization for the cross-family residual catalog inventory. -/
theorem residualMethodClosureCatalogRows_complete_exact
    (row : ResidualMethodClosureCatalogRow) :
    row ∈ residualMethodClosureCatalogRows ↔
      row = .matrixComponentwiseWeakStrictReduction ∨
      row = .matrixParetoProductReduction ∨
      row = .matrixLexPriorityReduction ∨
      row = .matrixPermutationLexPriorityReduction ∨
      row = .matrixScalarizableWeightReduction ∨
      row = .matrixArcticFullLicensedEscape ∨
      row = .matrixTropicalFullLicensedEscape ∨
      row = .matrixImportDependentLicensedEscape ∨
      row = .matrixUnconstrainedRelationNotYetMethodClass ∨
      row = .fbiFinalRouteStatusCatalog ∨
      row = .fbiResidualAdequacyBoundary ∨
      row = .genericDPDirectPairExtraction ∨
      row = .genericDPTransformedCallRoute ∨
      row = .genericDPImportedOrdering ∨
      row = .genericDPCertifiedProcedure ∨
      row = .semanticTransparentWholeTermMeasure ∨
      row = .semanticImportedModelLogicalRelation ∨
      row = .semanticCertifiedExternalProcedure ∨
      row = .nonlinearBoundedDegreeProjection ∨
      row = .nonlinearBoundedCrossTermQuadratic ∨
      row = .nonlinearBoundedMultilinear ∨
      row = .nonlinearWpoPolynomialBranch ∨
      row = .nonlinearMaxPlusDirectFragment ∨
      row = .nonlinearGlobalCrossCoupledWitness ∨
      row = .nonlinearUnconstrainedDirect := by
  cases row <;> simp [residualMethodClosureCatalogRows]

/-- The source projection for each cross-family row is exact. -/
theorem residualMethodClosureCatalogRowSource_exact
    (row : ResidualMethodClosureCatalogRow) :
    residualMethodClosureCatalogRowSource row =
      match row with
      | .matrixComponentwiseWeakStrictReduction => .matrix
      | .matrixParetoProductReduction => .matrix
      | .matrixLexPriorityReduction => .matrix
      | .matrixPermutationLexPriorityReduction => .matrix
      | .matrixScalarizableWeightReduction => .matrix
      | .matrixArcticFullLicensedEscape => .matrix
      | .matrixTropicalFullLicensedEscape => .matrix
      | .matrixImportDependentLicensedEscape => .matrix
      | .matrixUnconstrainedRelationNotYetMethodClass => .matrix
      | .fbiFinalRouteStatusCatalog => .fbi
      | .fbiResidualAdequacyBoundary => .fbi
      | .genericDPDirectPairExtraction => .genericDP
      | .genericDPTransformedCallRoute => .genericDP
      | .genericDPImportedOrdering => .genericDP
      | .genericDPCertifiedProcedure => .genericDP
      | .semanticTransparentWholeTermMeasure => .semantic
      | .semanticImportedModelLogicalRelation => .semantic
      | .semanticCertifiedExternalProcedure => .semantic
      | .nonlinearBoundedDegreeProjection => .nonlinear
      | .nonlinearBoundedCrossTermQuadratic => .nonlinear
      | .nonlinearBoundedMultilinear => .nonlinear
      | .nonlinearWpoPolynomialBranch => .nonlinear
      | .nonlinearMaxPlusDirectFragment => .nonlinear
      | .nonlinearGlobalCrossCoupledWitness => .nonlinear
      | .nonlinearUnconstrainedDirect => .nonlinear := by
  cases row <;> rfl

/-- The common status projection for each cross-family row is exact. -/
theorem residualMethodClosureCatalogRowStatus_exact
    (row : ResidualMethodClosureCatalogRow) :
    residualMethodClosureCatalogRowStatus row =
      match row with
      | .matrixComponentwiseWeakStrictReduction => .reducedToExistingTheorem
      | .matrixParetoProductReduction => .reducedToExistingTheorem
      | .matrixLexPriorityReduction => .reducedToExistingTheorem
      | .matrixPermutationLexPriorityReduction => .reducedToExistingTheorem
      | .matrixScalarizableWeightReduction => .reducedToExistingTheorem
      | .matrixArcticFullLicensedEscape => .licensedEscape
      | .matrixTropicalFullLicensedEscape => .licensedEscape
      | .matrixImportDependentLicensedEscape => .licensedEscape
      | .matrixUnconstrainedRelationNotYetMethodClass => .notYetMethodClass
      | .fbiFinalRouteStatusCatalog => .closedByLeanTheorem
      | .fbiResidualAdequacyBoundary => .conditionalBoundary
      | .genericDPDirectPairExtraction => .blocked
      | .genericDPTransformedCallRoute => .licensedEscape
      | .genericDPImportedOrdering => .licensedEscape
      | .genericDPCertifiedProcedure => .certifiedSuccess
      | .semanticTransparentWholeTermMeasure => .reducedToExistingTheorem
      | .semanticImportedModelLogicalRelation => .licensedEscape
      | .semanticCertifiedExternalProcedure => .certifiedSuccess
      | .nonlinearBoundedDegreeProjection => .reducedToExistingTheorem
      | .nonlinearBoundedCrossTermQuadratic => .closedByLeanTheorem
      | .nonlinearBoundedMultilinear => .closedByLeanTheorem
      | .nonlinearWpoPolynomialBranch => .closedByLeanTheorem
      | .nonlinearMaxPlusDirectFragment => .closedByLeanTheorem
      | .nonlinearGlobalCrossCoupledWitness => .licensedEscape
      | .nonlinearUnconstrainedDirect => .openResidual := by
  cases row <;> rfl

    /-- Source-catalog support payload carried by each cross-family row. -/
    def ResidualMethodClosureCatalogSupported :
      ResidualMethodClosureCatalogRow → Prop
      | .matrixComponentwiseWeakStrictReduction =>
        MatrixResidualClosureFinalCatalog ∧ MatrixResidualStatusCatalog
      | .matrixParetoProductReduction =>
        MatrixResidualClosureFinalCatalog ∧ MatrixResidualStatusCatalog
      | .matrixLexPriorityReduction =>
        MatrixResidualClosureFinalCatalog ∧ MatrixResidualStatusCatalog
      | .matrixPermutationLexPriorityReduction =>
        MatrixResidualClosureFinalCatalog ∧ MatrixResidualStatusCatalog
      | .matrixScalarizableWeightReduction =>
        MatrixResidualClosureFinalCatalog ∧ MatrixResidualStatusCatalog
      | .matrixArcticFullLicensedEscape =>
        MatrixResidualClosureFinalCatalog ∧ MatrixResidualStatusCatalog
      | .matrixTropicalFullLicensedEscape =>
        MatrixResidualClosureFinalCatalog ∧ MatrixResidualStatusCatalog
      | .matrixImportDependentLicensedEscape =>
        MatrixResidualClosureFinalCatalog ∧ MatrixResidualStatusCatalog
      | .matrixUnconstrainedRelationNotYetMethodClass =>
        MatrixResidualClosureFinalCatalog ∧ MatrixResidualStatusCatalog
      | .fbiFinalRouteStatusCatalog =>
        FBIFinalRouteStatusCatalog
      | .fbiResidualAdequacyBoundary =>
        FBIResidualAdequacyBoundaryCatalog ∧ FBINonClaimCatalog
      | .genericDPDirectPairExtraction =>
        GenericDPMethodSupported .directPairExtraction
      | .genericDPTransformedCallRoute =>
        GenericDPMethodSupported .transformedCallRoute
      | .genericDPImportedOrdering =>
        GenericDPMethodSupported .importedOrdering
      | .genericDPCertifiedProcedure =>
        GenericDPMethodSupported .certifiedProcedure
      | .semanticTransparentWholeTermMeasure =>
        SemanticMethodSupported .transparentWholeTermMeasure
      | .semanticImportedModelLogicalRelation =>
        SemanticMethodSupported .importedModelLogicalRelation
      | .semanticCertifiedExternalProcedure =>
        SemanticMethodSupported .certifiedExternalProcedure
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
      | .nonlinearUnconstrainedDirect =>
        NonlinearDirectBoundarySupported .unconstrainedNonlinearDirect

    /-- Every cross-family row projects to existing theorem-backed source support. -/
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
      | matrixImportDependentLicensedEscape
      | matrixUnconstrainedRelationNotYetMethodClass =>
        exact ⟨matrixResidualClosureCertificate_projects_finalCatalog,
        matrixResidualClosureCertificate_projects_statusCatalog⟩
      | fbiFinalRouteStatusCatalog =>
        exact fbi_final_catalog_certificate_projects_route_status_catalog
      | fbiResidualAdequacyBoundary =>
        exact ⟨fbi_final_catalog_certificate_projects_residual_boundary,
        fbi_final_catalog_certificate_projects_non_claim_catalog⟩
      | genericDPDirectPairExtraction =>
        exact genericDPMethodSupported_holds .directPairExtraction
      | genericDPTransformedCallRoute =>
        exact genericDPMethodSupported_holds .transformedCallRoute
      | genericDPImportedOrdering =>
        exact genericDPMethodSupported_holds .importedOrdering
      | genericDPCertifiedProcedure =>
        exact genericDPMethodSupported_holds .certifiedProcedure
      | semanticTransparentWholeTermMeasure =>
        exact semanticMethodSupported_holds .transparentWholeTermMeasure
      | semanticImportedModelLogicalRelation =>
        exact semanticMethodSupported_holds .importedModelLogicalRelation
      | semanticCertifiedExternalProcedure =>
        exact semanticMethodSupported_holds .certifiedExternalProcedure
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
      | nonlinearUnconstrainedDirect =>
        exact unconstrainedNonlinearDirect_remains_open

    /-- Paper-facing proposition for the exact cross-family residual closure catalog. -/
    abbrev ResidualMethodClosureCatalogSurface : Prop :=
      ∀ row : ResidualMethodClosureCatalogRow,
      row ∈ residualMethodClosureCatalogRows ∧
        ResidualMethodClosureCatalogSupported row ∧
        residualMethodClosureCatalogRowStatus row =
        match row with
        | .matrixComponentwiseWeakStrictReduction => .reducedToExistingTheorem
        | .matrixParetoProductReduction => .reducedToExistingTheorem
        | .matrixLexPriorityReduction => .reducedToExistingTheorem
        | .matrixPermutationLexPriorityReduction => .reducedToExistingTheorem
        | .matrixScalarizableWeightReduction => .reducedToExistingTheorem
        | .matrixArcticFullLicensedEscape => .licensedEscape
        | .matrixTropicalFullLicensedEscape => .licensedEscape
        | .matrixImportDependentLicensedEscape => .licensedEscape
        | .matrixUnconstrainedRelationNotYetMethodClass => .notYetMethodClass
        | .fbiFinalRouteStatusCatalog => .closedByLeanTheorem
        | .fbiResidualAdequacyBoundary => .conditionalBoundary
        | .genericDPDirectPairExtraction => .blocked
        | .genericDPTransformedCallRoute => .licensedEscape
        | .genericDPImportedOrdering => .licensedEscape
        | .genericDPCertifiedProcedure => .certifiedSuccess
        | .semanticTransparentWholeTermMeasure => .reducedToExistingTheorem
        | .semanticImportedModelLogicalRelation => .licensedEscape
        | .semanticCertifiedExternalProcedure => .certifiedSuccess
        | .nonlinearBoundedDegreeProjection => .reducedToExistingTheorem
        | .nonlinearBoundedCrossTermQuadratic => .closedByLeanTheorem
        | .nonlinearBoundedMultilinear => .closedByLeanTheorem
        | .nonlinearWpoPolynomialBranch => .closedByLeanTheorem
        | .nonlinearMaxPlusDirectFragment => .closedByLeanTheorem
        | .nonlinearGlobalCrossCoupledWitness => .licensedEscape
        | .nonlinearUnconstrainedDirect => .openResidual

    /-- The exact cross-family residual closure catalog is realized by the current source surfaces. -/
    theorem residualMethodClosureCatalog_exact : ResidualMethodClosureCatalogSurface := by
      intro row
      constructor
      · exact (residualMethodClosureCatalogRows_complete_exact row).2 (by
          cases row <;> simp)
      constructor
      · exact residualMethodClosureCatalogSupported_holds row
      · exact residualMethodClosureCatalogRowStatus_exact row

    /-- The exact cross-family catalog projects the source support carried by each row. -/
    theorem residualMethodClosureCatalog_projects_support
      (h : ResidualMethodClosureCatalogSurface) (row : ResidualMethodClosureCatalogRow) :
      ResidualMethodClosureCatalogSupported row :=
      (h row).2.1

    /-- The exact cross-family catalog projects the common status carried by each row. -/
    theorem residualMethodClosureCatalog_projects_status
      (h : ResidualMethodClosureCatalogSurface) (row : ResidualMethodClosureCatalogRow) :
      residualMethodClosureCatalogRowStatus row =
        match row with
        | .matrixComponentwiseWeakStrictReduction => .reducedToExistingTheorem
        | .matrixParetoProductReduction => .reducedToExistingTheorem
        | .matrixLexPriorityReduction => .reducedToExistingTheorem
        | .matrixPermutationLexPriorityReduction => .reducedToExistingTheorem
        | .matrixScalarizableWeightReduction => .reducedToExistingTheorem
        | .matrixArcticFullLicensedEscape => .licensedEscape
        | .matrixTropicalFullLicensedEscape => .licensedEscape
        | .matrixImportDependentLicensedEscape => .licensedEscape
        | .matrixUnconstrainedRelationNotYetMethodClass => .notYetMethodClass
        | .fbiFinalRouteStatusCatalog => .closedByLeanTheorem
        | .fbiResidualAdequacyBoundary => .conditionalBoundary
        | .genericDPDirectPairExtraction => .blocked
        | .genericDPTransformedCallRoute => .licensedEscape
        | .genericDPImportedOrdering => .licensedEscape
        | .genericDPCertifiedProcedure => .certifiedSuccess
        | .semanticTransparentWholeTermMeasure => .reducedToExistingTheorem
        | .semanticImportedModelLogicalRelation => .licensedEscape
        | .semanticCertifiedExternalProcedure => .certifiedSuccess
        | .nonlinearBoundedDegreeProjection => .reducedToExistingTheorem
        | .nonlinearBoundedCrossTermQuadratic => .closedByLeanTheorem
        | .nonlinearBoundedMultilinear => .closedByLeanTheorem
        | .nonlinearWpoPolynomialBranch => .closedByLeanTheorem
        | .nonlinearMaxPlusDirectFragment => .closedByLeanTheorem
        | .nonlinearGlobalCrossCoupledWitness => .licensedEscape
        | .nonlinearUnconstrainedDirect => .openResidual :=
      (h row).2.2

    /-- The catalog still exposes an explicit conditional-boundary row through the FBI adequacy surface. -/
    theorem residualMethodClosureCatalog_exhibits_conditionalBoundary
      (h : ResidualMethodClosureCatalogSurface) :
      ∃ row : ResidualMethodClosureCatalogRow,
        row ∈ residualMethodClosureCatalogRows ∧
        residualMethodClosureCatalogRowStatus row = .conditionalBoundary := by
      refine ⟨.fbiResidualAdequacyBoundary, (h .fbiResidualAdequacyBoundary).1, ?_⟩
      exact residualMethodClosureCatalog_projects_status h .fbiResidualAdequacyBoundary

    /-- The catalog still exposes an explicit open-residual row through the nonlinear residual split. -/
    theorem residualMethodClosureCatalog_exhibits_openResidual
      (h : ResidualMethodClosureCatalogSurface) :
      ∃ row : ResidualMethodClosureCatalogRow,
        row ∈ residualMethodClosureCatalogRows ∧
        residualMethodClosureCatalogRowStatus row = .openResidual := by
      refine ⟨.nonlinearUnconstrainedDirect, (h .nonlinearUnconstrainedDirect).1, ?_⟩
      exact residualMethodClosureCatalog_projects_status h .nonlinearUnconstrainedDirect

    /-- Non-overclaim theorem: the cross-family catalog does not certify universal residual closure. -/
    theorem residualMethodClosureCatalog_not_universally_closed
      (h : ResidualMethodClosureCatalogSurface) :
      ∃ row : ResidualMethodClosureCatalogRow,
        row ∈ residualMethodClosureCatalogRows ∧
        (residualMethodClosureCatalogRowStatus row = .openResidual ∨
          residualMethodClosureCatalogRowStatus row = .conditionalBoundary) := by
      rcases residualMethodClosureCatalog_exhibits_openResidual h with ⟨row, hmem, hstatus⟩
      exact ⟨row, hmem, Or.inl hstatus⟩

    /-- Certificate packaging the exact cross-family catalog and its explicit non-overclaim boundary. -/
    structure ResidualMethodClosureCertificate where
      catalog : ResidualMethodClosureCatalogSurface
      notUniversallyClosed :
      ∃ row : ResidualMethodClosureCatalogRow,
        row ∈ residualMethodClosureCatalogRows ∧
        (residualMethodClosureCatalogRowStatus row = .openResidual ∨
          residualMethodClosureCatalogRowStatus row = .conditionalBoundary)

    /-- The cross-family WS-G residual closure certificate is realized by the current theorem-backed surfaces. -/
    theorem residualMethodClosureCertificate : ResidualMethodClosureCertificate := by
      exact {
      catalog := residualMethodClosureCatalog_exact
      notUniversallyClosed :=
        residualMethodClosureCatalog_not_universally_closed
        residualMethodClosureCatalog_exact
      }

    /-- The cross-family certificate projects the exact catalog. -/
    theorem residualMethodClosureCertificate_projects_catalog :
      ResidualMethodClosureCatalogSurface :=
      residualMethodClosureCertificate.catalog

    /-- The cross-family certificate projects the explicit non-overclaim boundary witness. -/
    theorem residualMethodClosureCertificate_projects_notUniversallyClosed :
      ∃ row : ResidualMethodClosureCatalogRow,
        row ∈ residualMethodClosureCatalogRows ∧
        (residualMethodClosureCatalogRowStatus row = .openResidual ∨
          residualMethodClosureCatalogRowStatus row = .conditionalBoundary) :=
      residualMethodClosureCertificate.notUniversallyClosed

end OperatorKO7.ResidualMethodClosureCatalog
