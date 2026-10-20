import OperatorKO7.ResidualMethodAPI

namespace ResidualMethodAPIReach

open OperatorKO7.ResidualMethodAPI

#check ResidualMethodClosureCatalogRow
#check ResidualMethodClosureStatus
#check ResidualMethodClosureCatalogSurface
#check ResidualMethodUniversalSupport
#check ResidualMethodUniversalTerminalStatus
#check ResidualMethodClosureCertificate
#check residualMethodClosureCertificate
#check residualMethodClosureCatalog
#check residualMethodClosureAllRowsSupported
#check residualMethodClosureAllRowsTerminal
#check residualMethodClosureCertificateProjectsAllRowsSupported
#check residualMethodClosureCertificateProjectsAllRowsTerminal

#check MatrixResidualClosureCertificate
#check matrixResidualClosureCertificate
#check matrixResidualClosureCertificateProjectsFinalCatalog
#check matrixResidualClosureCertificateProjectsStatusCatalog

#check FBIFinalCatalogCertificate
#check fbiFinalCatalogCertificate
#check fbiFinalCatalogCertificateProjectsRouteStatusCatalog
#check fbiFinalCatalogCertificateProjectsResidualBoundary
#check fbiFinalCatalogCertificateProjectsNonClaimCatalog

#check GenericDPBoundaryCertificate
#check genericDPBoundaryCertificate
#check genericDPBoundaryCertificateProjectsCatalog
#check genericDPBoundaryCertificateProjectsNonW0

#check SemanticMethodBoundaryCertificate
#check semanticMethodBoundaryCertificate
#check semanticMethodBoundaryCertificateProjectsCatalog
#check semanticMethodBoundaryCertificateProjectsImportedNotW0

#check NonlinearDirectBoundaryCertificate
#check nonlinearDirectBoundaryCertificate
#check nonlinearDirectBoundaryCertificateProjectsStatusCatalog
#check nonlinearDirectBoundaryCertificateProjectsProjectionCatalog

#check W1MethodCarrierCertificate
#check w1MethodCarrierCertificate
#check w1MethodCarrierCertificateProjectsCatalog
#check w1MethodCarrierCertificateProjectsNecessity
#check w1MethodCarrierCertificateProjectsSeparation

example : ResidualMethodClosureCertificate :=
  residualMethodClosureCertificate

example : ResidualMethodClosureCatalogSurface :=
  residualMethodClosureCatalog

example : ResidualMethodUniversalSupport :=
  residualMethodClosureAllRowsSupported

example : ResidualMethodUniversalTerminalStatus :=
  residualMethodClosureAllRowsTerminal

example : ResidualMethodUniversalSupport :=
  residualMethodClosureCertificateProjectsAllRowsSupported

example : ResidualMethodUniversalTerminalStatus :=
  residualMethodClosureCertificateProjectsAllRowsTerminal

example : MatrixResidualClosureCertificate :=
  matrixResidualClosureCertificate

example :=
  matrixResidualClosureCertificateProjectsFinalCatalog

example :=
  matrixResidualClosureCertificateProjectsStatusCatalog

example : FBIFinalCatalogCertificate :=
  fbiFinalCatalogCertificate

example :=
  fbiFinalCatalogCertificateProjectsRouteStatusCatalog

example :=
  fbiFinalCatalogCertificateProjectsResidualBoundary

example :=
  fbiFinalCatalogCertificateProjectsNonClaimCatalog

example : GenericDPBoundaryCertificate :=
  genericDPBoundaryCertificate

example : SemanticMethodBoundaryCertificate :=
  semanticMethodBoundaryCertificate

example : NonlinearDirectBoundaryCertificate :=
  nonlinearDirectBoundaryCertificate

example : W1MethodCarrierCertificate :=
  w1MethodCarrierCertificate

/-- Every catalog row is supported and terminal under the stable API projections.
This replaces a stale gate line that referenced a non-universal-closure witness
which no longer exists anywhere in the tree. -/
example (row : ResidualMethodClosureCatalogRow) :
    OperatorKO7.ResidualMethodClosureCatalog.ResidualMethodClosureCatalogSupported row :=
  residualMethodClosureAllRowsSupported row

/-! ## WP-11 root reachability for the WP-3 polynomial payload observer

The observer's exhaustive declaration surface stays in
`Test/PolynomialPayloadObserverReach.lean`; this block only confirms it is
reachable through this root and records its axiom sets. -/

#check @OperatorKO7.StepDuplicating.polynomialPayloadObserver_no_global_orientation
#check @OperatorKO7.StepDuplicating.polynomialPayloadObserver_no_global_orientation_withoutPump
#check @OperatorKO7.StepDuplicating.polynomialPayloadObserver_cannot_orient_rule
#check @OperatorKO7.StepDuplicating.polynomialPayloadEval_lt_of_dominates
#check @OperatorKO7.StepDuplicating.escapePolynomialObserver_globallyOrients
#check @OperatorKO7.StepDuplicating.escapeFamily_hasUnboundedPayloadPump

#print axioms OperatorKO7.StepDuplicating.polynomialPayloadObserver_no_global_orientation
#print axioms OperatorKO7.StepDuplicating.polynomialPayloadObserver_no_global_orientation_withoutPump
#print axioms OperatorKO7.StepDuplicating.polynomialPayloadObserver_cannot_orient_rule
#print axioms OperatorKO7.StepDuplicating.polynomialPayloadEval_lt_of_dominates
#print axioms OperatorKO7.StepDuplicating.escapePolynomialObserver_globallyOrients
#print axioms OperatorKO7.StepDuplicating.escapeFamily_hasUnboundedPayloadPump

end ResidualMethodAPIReach
