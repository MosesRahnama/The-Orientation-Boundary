import OperatorKO7.Meta.ResidualMethodClosureCatalog
import OperatorKO7.Meta.MatrixResidualClosureCatalog
import OperatorKO7.Meta.FBI_FinalCatalog
import OperatorKO7.Meta.GenericDPMethodBoundary
import OperatorKO7.Meta.SemanticMethodBoundary
import OperatorKO7.Meta.NonlinearDirectBoundary
import OperatorKO7.Meta.W1MethodCarrier

/-!
# Residual Method API

This module is a thin stable import boundary for the WS-G residual-method
surface. It re-exports the current certificate objects without duplicating
proof content or widening the root API.
-/

namespace OperatorKO7.ResidualMethodAPI

/-- Stable API alias for the WS-G residual catalog row carrier. -/
abbrev ResidualMethodClosureCatalogRow : Type :=
  OperatorKO7.ResidualMethodClosureCatalog.ResidualMethodClosureCatalogRow

/-- Stable API alias for the WS-G residual catalog status vocabulary. -/
abbrev ResidualMethodClosureStatus : Type :=
  OperatorKO7.ResidualMethodClosureCatalog.ResidualMethodClosureStatus

/-- Stable API alias for the exact WS-G residual catalog surface. -/
abbrev ResidualMethodClosureCatalogSurface : Prop :=
  OperatorKO7.ResidualMethodClosureCatalog.ResidualMethodClosureCatalogSurface

/-- Stable API alias for the explicit non-universal-closure witness on the WS-G
catalog surface. -/
abbrev ResidualMethodNonUniversalClosureWitness : Prop :=
  ∃ row : ResidualMethodClosureCatalogRow,
    row ∈ OperatorKO7.ResidualMethodClosureCatalog.residualMethodClosureCatalogRows ∧
      (OperatorKO7.ResidualMethodClosureCatalog.residualMethodClosureCatalogRowStatus row =
          OperatorKO7.ResidualMethodClosureCatalog.ResidualMethodClosureStatus.openResidual
        ∨ OperatorKO7.ResidualMethodClosureCatalog.residualMethodClosureCatalogRowStatus row =
          OperatorKO7.ResidualMethodClosureCatalog.ResidualMethodClosureStatus.conditionalBoundary)

/-- Stable API alias for the WS-G residual closure certificate. -/
abbrev ResidualMethodClosureCertificate : Prop :=
  OperatorKO7.ResidualMethodClosureCatalog.ResidualMethodClosureCertificate

/-- Stable API entrypoint for the WS-G residual closure certificate. -/
theorem residualMethodClosureCertificate : ResidualMethodClosureCertificate :=
  OperatorKO7.ResidualMethodClosureCatalog.residualMethodClosureCertificate

/-- Stable API entrypoint for the exact WS-G residual catalog surface. -/
theorem residualMethodClosureCatalog : ResidualMethodClosureCatalogSurface :=
  OperatorKO7.ResidualMethodClosureCatalog.residualMethodClosureCertificate_projects_catalog

/-- Stable API entrypoint for the explicit non-universal-closure witness. -/
theorem residualMethodClosureNotUniversallyClosed :
    ResidualMethodNonUniversalClosureWitness :=
  OperatorKO7.ResidualMethodClosureCatalog.residualMethodClosureCertificate_projects_notUniversallyClosed

/-- Stable API projection from the WS-G residual certificate to the exact catalog. -/
abbrev residualMethodClosureCertificateProjectsCatalog :=
  OperatorKO7.ResidualMethodClosureCatalog.residualMethodClosureCertificate_projects_catalog

/-- Stable API projection from the WS-G residual certificate to the explicit
non-universal-closure witness. -/
abbrev residualMethodClosureCertificateProjectsNotUniversallyClosed :=
  OperatorKO7.ResidualMethodClosureCatalog.residualMethodClosureCertificate_projects_notUniversallyClosed

/-- Stable API alias for the matrix residual closure certificate. -/
abbrev MatrixResidualClosureCertificate : Prop :=
  OperatorKO7.MatrixResidualClosureCatalog.MatrixResidualClosureCertificate

/-- Stable API entrypoint for the matrix residual closure certificate. -/
theorem matrixResidualClosureCertificate : MatrixResidualClosureCertificate :=
  OperatorKO7.MatrixResidualClosureCatalog.matrixResidualClosureCertificate

/-- Stable API projection from the matrix residual certificate to the final catalog. -/
abbrev matrixResidualClosureCertificateProjectsFinalCatalog :=
  OperatorKO7.MatrixResidualClosureCatalog.matrixResidualClosureCertificate_projects_finalCatalog

/-- Stable API projection from the matrix residual certificate to the status catalog. -/
abbrev matrixResidualClosureCertificateProjectsStatusCatalog :=
  OperatorKO7.MatrixResidualClosureCatalog.matrixResidualClosureCertificate_projects_statusCatalog

/-- Stable API alias for the FBI final catalog certificate. -/
abbrev FBIFinalCatalogCertificate : Prop :=
  OperatorKO7.FBIFinalCatalog.FBIFinalCatalogCertificate

/-- Stable API entrypoint for the FBI final catalog certificate. -/
theorem fbiFinalCatalogCertificate : FBIFinalCatalogCertificate :=
  OperatorKO7.FBIFinalCatalog.fbi_final_catalog_certificate

/-- Stable API projection from the FBI final certificate to the route-status catalog. -/
abbrev fbiFinalCatalogCertificateProjectsRouteStatusCatalog :=
  OperatorKO7.FBIFinalCatalog.fbi_final_catalog_certificate_projects_route_status_catalog

/-- Stable API projection from the FBI final certificate to the residual boundary. -/
abbrev fbiFinalCatalogCertificateProjectsResidualBoundary :=
  OperatorKO7.FBIFinalCatalog.fbi_final_catalog_certificate_projects_residual_boundary

/-- Stable API projection from the FBI final certificate to the non-claim catalog. -/
abbrev fbiFinalCatalogCertificateProjectsNonClaimCatalog :=
  OperatorKO7.FBIFinalCatalog.fbi_final_catalog_certificate_projects_non_claim_catalog

/-- Stable API alias for the generic DP boundary certificate. -/
abbrev GenericDPBoundaryCertificate : Prop :=
  OperatorKO7.GenericDPMethodBoundary.GenericDPBoundaryCertificate

/-- Stable API entrypoint for the generic DP boundary certificate. -/
theorem genericDPBoundaryCertificate : GenericDPBoundaryCertificate :=
  OperatorKO7.GenericDPMethodBoundary.genericDPBoundaryCertificate_exact

/-- Stable API projection from the generic DP boundary certificate to its catalog. -/
abbrev genericDPBoundaryCertificateProjectsCatalog :=
  OperatorKO7.GenericDPMethodBoundary.genericDPBoundaryCertificate_projects_catalog

/-- Stable API projection from the generic DP boundary certificate to its non-W0 witness. -/
abbrev genericDPBoundaryCertificateProjectsNonW0 :=
  OperatorKO7.GenericDPMethodBoundary.genericDPBoundaryCertificate_projects_nonW0

/-- Stable API alias for the semantic method boundary certificate. -/
abbrev SemanticMethodBoundaryCertificate : Prop :=
  OperatorKO7.SemanticMethodBoundary.SemanticMethodBoundaryCertificate

/-- Stable API entrypoint for the semantic method boundary certificate. -/
theorem semanticMethodBoundaryCertificate : SemanticMethodBoundaryCertificate :=
  OperatorKO7.SemanticMethodBoundary.semanticMethodBoundaryCertificate_exact

/-- Stable API projection from the semantic boundary certificate to its catalog. -/
abbrev semanticMethodBoundaryCertificateProjectsCatalog :=
  OperatorKO7.SemanticMethodBoundary.semanticMethodBoundaryCertificate_projects_catalog

/-- Stable API projection from the semantic boundary certificate to its imported-not-W0 witness. -/
abbrev semanticMethodBoundaryCertificateProjectsImportedNotW0 :=
  OperatorKO7.SemanticMethodBoundary.semanticMethodBoundaryCertificate_projects_importedNotW0

/-- Stable API alias for the nonlinear direct boundary certificate. -/
abbrev NonlinearDirectBoundaryCertificate : Prop :=
  OperatorKO7.NonlinearDirectBoundary.NonlinearDirectBoundaryCertificate

/-- Stable API entrypoint for the nonlinear direct boundary certificate. -/
theorem nonlinearDirectBoundaryCertificate : NonlinearDirectBoundaryCertificate :=
  OperatorKO7.NonlinearDirectBoundary.nonlinear_direct_boundary_certificate

/-- Stable API projection from the nonlinear direct certificate to its status catalog. -/
abbrev nonlinearDirectBoundaryCertificateProjectsStatusCatalog :=
  OperatorKO7.NonlinearDirectBoundary.nonlinear_direct_boundary_certificate_projects_status_catalog

/-- Stable API projection from the nonlinear direct certificate to its projection catalog. -/
abbrev nonlinearDirectBoundaryCertificateProjectsProjectionCatalog :=
  OperatorKO7.NonlinearDirectBoundary.nonlinear_direct_boundary_certificate_projects_projection_catalog

/-- Stable API alias for the W1 method carrier certificate. -/
abbrev W1MethodCarrierCertificate : Prop :=
  OperatorKO7.W1MethodCarrier.W1MethodCarrierCertificate

/-- Stable API entrypoint for the W1 method carrier certificate. -/
theorem w1MethodCarrierCertificate : W1MethodCarrierCertificate :=
  OperatorKO7.W1MethodCarrier.w1MethodCarrierCertificate_exact

/-- Stable API projection from the W1 carrier certificate to its catalog. -/
abbrev w1MethodCarrierCertificateProjectsCatalog :=
  OperatorKO7.W1MethodCarrier.w1MethodCarrierCertificate_projects_catalog

/-- Stable API projection from the W1 carrier certificate to its necessity witness. -/
abbrev w1MethodCarrierCertificateProjectsNecessity
    {row : OperatorKO7.W1MethodCarrier.W1MethodRow}
    (h : OperatorKO7.W1MethodCarrier.W1MethodRowSupported row) :=
  OperatorKO7.W1MethodCarrier.w1MethodCarrierCertificate_projects_necessity (row := row) h

/-- Stable API projection from the W1 carrier certificate to its separation witness. -/
abbrev w1MethodCarrierCertificateProjectsSeparation :=
  OperatorKO7.W1MethodCarrier.w1MethodCarrierCertificate_projects_separation

end OperatorKO7.ResidualMethodAPI
