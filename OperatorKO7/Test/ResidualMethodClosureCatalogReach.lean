import OperatorKO7.Meta.ResidualMethodClosureCatalog

/-!
# Reach and axiom gate for the residual-method closure catalog

Pins every explicit public declaration of
`OperatorKO7/Meta/ResidualMethodClosureCatalog.lean` with a paired axiom query,
and exercises the catalog's live status vocabulary.

The catalog's status enum was reduced to five terminal tags and three rows were
renamed; this gate is stated against that live surface. The two non-vacuity
examples witness the exact statuses that make the inventory terminally
classified without being universally closed.
-/

namespace ResidualMethodClosureCatalogReach

open OperatorKO7.ResidualMethodClosureCatalog

#check @ResidualMethodClosureCatalogSource
#check @ResidualMethodClosureStatus
#check @ResidualMethodClosureCatalogRow
#check @residualMethodClosureCatalogRows
#check @residualMethodClosureCatalogRowSource
#check @residualMethodClosureCatalogRowStatus
#check @ResidualMethodClosureCatalogSupported
#check @residualMethodClosureCatalogRows_nodup
#check @residualMethodClosureCatalogRows_length
#check @residualMethodClosureCatalogRows_complete_exact
#check @residualMethodClosureCatalogSupported_holds
#check @residualMethodClosureCatalogRowStatus_terminal
#check @ResidualMethodClosureCatalogSurface
#check @residualMethodClosureCatalog_exact
#check @residualMethodClosureCatalog_projects_support
#check @residualMethodClosureCatalog_projects_terminal_status
#check @ResidualMethodClosureRowNotInternallyClosed
#check @ResidualMethodClosureNotUniversallyClosed
#check @residualMethodClosureCatalog_exhibits_blocked
#check @residualMethodClosureCatalog_exhibits_licensedEscape
#check @residualMethodClosureCatalog_not_universally_closed
#check @ResidualMethodClosureCertificate
#check @residualMethodClosureCertificate
#check @residualMethodClosureCertificate_projects_catalog
#check @residualMethodClosureCertificate_projects_notUniversallyClosed
#check @residualMethodClosureCertificate_projects_allRowsSupported
#check @residualMethodClosureCertificate_projects_allRowsTerminal

#print axioms ResidualMethodClosureCatalogSource
#print axioms ResidualMethodClosureStatus
#print axioms ResidualMethodClosureCatalogRow
#print axioms residualMethodClosureCatalogRows
#print axioms residualMethodClosureCatalogRowSource
#print axioms residualMethodClosureCatalogRowStatus
#print axioms ResidualMethodClosureCatalogSupported
#print axioms residualMethodClosureCatalogRows_nodup
#print axioms residualMethodClosureCatalogRows_length
#print axioms residualMethodClosureCatalogRows_complete_exact
#print axioms residualMethodClosureCatalogSupported_holds
#print axioms residualMethodClosureCatalogRowStatus_terminal
#print axioms ResidualMethodClosureCatalogSurface
#print axioms residualMethodClosureCatalog_exact
#print axioms residualMethodClosureCatalog_projects_support
#print axioms residualMethodClosureCatalog_projects_terminal_status
#print axioms ResidualMethodClosureRowNotInternallyClosed
#print axioms ResidualMethodClosureNotUniversallyClosed
#print axioms residualMethodClosureCatalog_exhibits_blocked
#print axioms residualMethodClosureCatalog_exhibits_licensedEscape
#print axioms residualMethodClosureCatalog_not_universally_closed
#print axioms ResidualMethodClosureCertificate
#print axioms residualMethodClosureCertificate
#print axioms residualMethodClosureCertificate_projects_catalog
#print axioms residualMethodClosureCertificate_projects_notUniversallyClosed
#print axioms residualMethodClosureCertificate_projects_allRowsSupported
#print axioms residualMethodClosureCertificate_projects_allRowsTerminal

/-! ## Live-surface exercises -/

example : ResidualMethodClosureCatalogSurface :=
  residualMethodClosureCertificate_projects_catalog

example : ResidualMethodClosureCatalogRow.fbiAdequacyBoundaryClosed ∈
    residualMethodClosureCatalogRows := by
  decide

example :
    residualMethodClosureCatalogRowSource
      .semanticCertifiedExternalEngine = .semantic := rfl

example :
    residualMethodClosureCatalogRowStatus
      .nonlinearUnconstrainedDirectExactLawBoundary = .closedByLeanTheorem := rfl

example :
    ResidualMethodClosureCatalogSupported
      .matrixArcticFullLicensedEscape :=
  residualMethodClosureCatalog_projects_support
    residualMethodClosureCatalog_exact .matrixArcticFullLicensedEscape

example :
    ResidualMethodClosureCatalogSupported
      .fbiAdequacyBoundaryClosed :=
  residualMethodClosureCatalog_projects_support
    residualMethodClosureCatalog_exact .fbiAdequacyBoundaryClosed

example :
    ResidualMethodClosureCatalogSupported
      .genericDPImportedOrdering :=
  residualMethodClosureCatalog_projects_support
    residualMethodClosureCatalog_exact .genericDPImportedOrdering

example :
    ResidualMethodClosureCatalogSupported
      .semanticTransparentWholeTermMeasure :=
  residualMethodClosureCatalog_projects_support
    residualMethodClosureCatalog_exact .semanticTransparentWholeTermMeasure

example :
    ResidualMethodClosureCatalogSupported
      .nonlinearBoundedCrossTermQuadratic :=
  residualMethodClosureCatalog_projects_support
    residualMethodClosureCatalog_exact .nonlinearBoundedCrossTermQuadratic

/-- Non-vacuity of the standing-obstruction status. -/
example :
    residualMethodClosureCatalogRowStatus
      .genericDPDirectPairExtraction = .blocked :=
  residualMethodClosureCatalog_exhibits_blocked

/-- Non-vacuity of the external-license status. -/
example :
    residualMethodClosureCatalogRowStatus
      .matrixArcticFullLicensedEscape = .licensedEscape :=
  residualMethodClosureCatalog_exhibits_licensedEscape

/-- The inventory is terminally classified without being universally closed. -/
example : ResidualMethodClosureNotUniversallyClosed :=
  residualMethodClosureCertificate_projects_notUniversallyClosed

end ResidualMethodClosureCatalogReach
