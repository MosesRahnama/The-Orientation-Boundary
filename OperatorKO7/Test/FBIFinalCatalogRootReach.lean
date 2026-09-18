import OperatorKO7.ResidualMethodAPI

/-!
# FBI final-catalog root reach gate

WP-11 retargets this gate from the aggregate package root to
`OperatorKO7.ResidualMethodAPI`, which is the integrated root that directly
imports `Meta/FBI_FinalCatalog.lean`. The aggregate root cannot be used as a
validation target because the campaign forbids aggregate builds, so a gate
importing it could only ever be checked against a stale aggregate olean.
Reaching the catalog through its primary direct root is the stronger check: it
fails if the module is ever dropped from that root's import list.

The gate previously referenced `FBINonClaimCatalog`, `fbi_non_claim_catalog`,
and the certificate field `nonClaimCatalog`. None of those exist after WP-3
replaced the non-claim surface with the direction-indexed route/status catalog,
so the stale names are replaced here by the live certificate fields and the new
directional anchors. External TTT2 FBI remains MAYBE and that fact is gated.
-/

namespace FBIFinalCatalogRootReach

/-! ## Live final-catalog surface -/

#check @OperatorKO7.FBIFinalCatalog.FBIFinalRouteStatusCatalog
#check @OperatorKO7.FBIFinalCatalog.fbi_final_route_status_catalog
#check @OperatorKO7.FBIFinalCatalog.FBIResidualAdequacyBoundaryCatalog
#check @OperatorKO7.FBIFinalCatalog.fbi_residual_adequacy_boundary_catalog
#check @OperatorKO7.FBIFinalCatalog.FBIAdequacyBoundaryCatalog
#check @OperatorKO7.FBIFinalCatalog.fbi_adequacy_boundary_catalog
#check @OperatorKO7.FBIFinalCatalog.FBIClosureCatalog
#check @OperatorKO7.FBIFinalCatalog.fbi_closure_catalog
#check @OperatorKO7.FBIFinalCatalog.FBIFinalCatalogCertificate
#check @OperatorKO7.FBIFinalCatalog.fbi_final_catalog_certificate

#print axioms OperatorKO7.FBIFinalCatalog.fbi_final_route_status_catalog
#print axioms OperatorKO7.FBIFinalCatalog.fbi_residual_adequacy_boundary_catalog
#print axioms OperatorKO7.FBIFinalCatalog.fbi_adequacy_boundary_catalog
#print axioms OperatorKO7.FBIFinalCatalog.fbi_closure_catalog
#print axioms OperatorKO7.FBIFinalCatalog.fbi_final_catalog_certificate

/-! ## WP-3 direction-indexed route/status catalog -/

#check @OperatorKO7.FBIFinalCatalog.FBIDirectionalRouteRow
#check @OperatorKO7.FBIFinalCatalog.fbiDirectionalRouteRows
#check @OperatorKO7.FBIFinalCatalog.fbiDirectionalRouteRows_length
#check @OperatorKO7.FBIFinalCatalog.fbiDirectionalRouteRows_nodup
#check @OperatorKO7.FBIFinalCatalog.fbiDirectionalRouteRows_complete
#check @OperatorKO7.FBIFinalCatalog.fbiDirectionalRow_legacy_projection
#check @OperatorKO7.FBIFinalCatalog.FBIDirectionalRouteStatusCatalog
#check @OperatorKO7.FBIFinalCatalog.fbi_directional_route_status_catalog
#check @OperatorKO7.FBIFinalCatalog.fbi_forward_directional_coverage
#check @OperatorKO7.FBIFinalCatalog.fbi_backward_directional_coverage
#check @OperatorKO7.FBIFinalCatalog.FBIDirectionalCatalogCertificate
#check @OperatorKO7.FBIFinalCatalog.fbi_directional_catalog_certificate

#print axioms OperatorKO7.FBIFinalCatalog.fbiDirectionalRouteRows_length
#print axioms OperatorKO7.FBIFinalCatalog.fbiDirectionalRouteRows_nodup
#print axioms OperatorKO7.FBIFinalCatalog.fbiDirectionalRouteRows_complete
#print axioms OperatorKO7.FBIFinalCatalog.fbiDirectionalRow_legacy_projection
#print axioms OperatorKO7.FBIFinalCatalog.fbi_directional_route_status_catalog
#print axioms OperatorKO7.FBIFinalCatalog.fbi_forward_directional_coverage
#print axioms OperatorKO7.FBIFinalCatalog.fbi_backward_directional_coverage
#print axioms OperatorKO7.FBIFinalCatalog.fbi_directional_catalog_certificate

/-! ## External TTT2 FBI status stays MAYBE -/

#check @OperatorKO7.FBIFinalCatalog.FBIExternalToolStatus
#check @OperatorKO7.FBIFinalCatalog.fbi_external_ttt2_status_is_maybe
#check @OperatorKO7.FBIFinalCatalog.fbi_external_ttt2_status_ne_certifiedYes

#print axioms OperatorKO7.FBIFinalCatalog.fbi_external_ttt2_status_is_maybe
#print axioms OperatorKO7.FBIFinalCatalog.fbi_external_ttt2_status_ne_certifiedYes

/-! ## Certificate projections reached through the integrated root -/

example : OperatorKO7.FBIFinalCatalog.FBIFinalRouteStatusCatalog :=
  OperatorKO7.FBIFinalCatalog.fbi_final_catalog_certificate.routeStatusCatalog

example : OperatorKO7.FBIFinalCatalog.FBIResidualAdequacyBoundaryCatalog :=
  OperatorKO7.FBIFinalCatalog.fbi_final_catalog_certificate.residualAdequacyBoundary

example : OperatorKO7.FBIFinalCatalog.FBIAdequacyBoundaryCatalog :=
  OperatorKO7.FBIFinalCatalog.fbi_final_catalog_certificate.adequacyBoundary

example : OperatorKO7.FBIFinalCatalog.FBIClosureCatalog :=
  OperatorKO7.FBIFinalCatalog.fbi_final_catalog_certificate.closureCatalog

/-- The twelve direction-indexed rows are reachable through the integrated
root and carry their exact count. -/
example : OperatorKO7.FBIFinalCatalog.fbiDirectionalRouteRows.length = 12 :=
  OperatorKO7.FBIFinalCatalog.fbiDirectionalRouteRows_length

end FBIFinalCatalogRootReach
