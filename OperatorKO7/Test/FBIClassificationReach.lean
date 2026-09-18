import OperatorKO7.Meta.FBI_Classification

namespace FBIClassificationReach

open OperatorKO7
open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.FBIClassification

#check FBIDirection
#check FBIInstantiation
#check FBIComparisonWitness
#check FBIMethod
#check FBISuccessSemantics
#check FBIClosureStatus
#check FBIRoutesTo
#check FBIHasClosureStatus
#check fbiRouteClosureStatus
#check fbiClosureStatuses
#check fbiClosureStatuses_nodup
#check fbiClosureStatuses_length
#check fbiClosureStatuses_complete_exact
#check FBIFinalCatalogRow
#check fbiFinalCatalogRows
#check fbiFinalCatalogMethod
#check fbiFinalCatalogRoute?
#check fbiFinalCatalogStatus
#check FBIFinalCatalogRowSupported
#check fbiFinalCatalogRows_nodup
#check fbiFinalCatalogRows_length
#check fbiFinalCatalogRows_complete_exact
#check FBIFinalRouteStatusCatalog
#check fbi_final_catalog_row_route_status_exact
#check fbi_final_catalog_row_supported
#check fbi_final_route_status_catalog
#check FBIGenericAdequacyBoundary
#check FBIResidualBoundaryStatus
#check fbiGenericAdequacyBoundaries
#check fbiGenericAdequacyBoundaryInstantiation
#check fbiGenericAdequacyBoundaryStatus
#check fbiGenericForwardAdequacyClosureTheorem
#check fbiGenericBackwardAdequacyClosureTheorem
#check fbiGenericAdequacyBoundaries_nodup
#check fbiGenericAdequacyBoundaries_length
#check fbiGenericAdequacyBoundaries_complete_exact
#check FBIResidualAdequacyBoundaryCatalog
#check fbi_residual_adequacy_boundary_catalog
#check FBIFinalCatalogCertificate
#check fbi_final_catalog_certificate
#check fbi_final_catalog_certificate_projects_route_status_catalog
#check fbi_final_catalog_certificate_projects_residual_boundary
#check directForwardFBIMethod
#check importedWholeFBIMethod
#check transformedCallFBIMethod
#check certifiedFBIMethod
#check fbi_direct_evidence_routes_to_w0
#check fbi_transformed_call_evidence_routes_to_w2
#check fbi_construction_import_evidence_routes_to_w1
#check fbi_certificate_evidence_is_certified_success
#check fbi_success_with_route_evidence_has_closure_status
#check fbi_maybe_row_replaced_by_formal_status

example : FBIRoutesTo directForwardFBIMethod .W0 := by
  exact fbi_direct_evidence_routes_to_w0

example : FBIRoutesTo importedWholeFBIMethod .W1 := by
  exact fbi_construction_import_evidence_routes_to_w1.1

example : FBIRoutesTo transformedCallFBIMethod .W2 := by
  exact fbi_transformed_call_evidence_routes_to_w2.1

example : FBIHasClosureStatus certifiedFBIMethod .certifiedSuccess := by
  exact fbi_certificate_evidence_is_certified_success

example : FBIHasClosureStatus importedWholeFBIMethod (fbiRouteClosureStatus .W1) := by
  exact fbi_success_with_route_evidence_has_closure_status
    fbi_construction_import_evidence_routes_to_w1.1

example : FBIFinalCatalogRowSupported .constructionW1LicensedEscape := by
  exact fbi_final_catalog_row_supported _

example : (fbiFinalCatalogMethod .certifiedSuccess).successSemantics.route? = none := by
  exact (fbi_final_catalog_row_route_status_exact .certifiedSuccess).1

example : fbiGenericAdequacyBoundaryInstantiation .forwardAdequacy = .forwardOnly := by
  exact (fbi_residual_adequacy_boundary_catalog .forwardAdequacy).2.1

example : fbiGenericAdequacyBoundaryStatus .backwardAdequacy =
    .closedByNamedTheorem fbiGenericBackwardAdequacyClosureTheorem := by
  exact (fbi_residual_adequacy_boundary_catalog .backwardAdequacy).2.2

example : ∃ status ∈ fbiClosureStatuses, FBIHasClosureStatus transformedCallFBIMethod status := by
  exact fbi_maybe_row_replaced_by_formal_status transformedCallFBIMethod

/-! ## Direction-indexed catalog and external tool status: new anchors (WP-3 item A) -/

#check FBIExternalToolStatus
#check fbiExternalTTT2Status
#check fbi_external_ttt2_status_is_maybe
#check fbi_external_ttt2_status_ne_certifiedYes
#check FBIDirectionalRouteRow
#check fbiCatalogRowOfWitness
#check fbiDirectionalRow
#check fbiDirectionalRow_fst
#check fbiDirectionalRow_snd
#check fbiDirectionalRouteRows
#check fbiDirectionalRouteRows_length
#check fbiDirectionalRouteRows_nodup
#check fbiDirectionalRouteRows_complete
#check fbiDirectionalRow_mem
#check fbiDirectionalRow_legacy_projection
#check FBIDirectionalRouteStatusCatalog
#check fbi_directional_route_status_catalog

#print axioms fbiExternalTTT2Status
#print axioms FBIExternalToolStatus
#print axioms fbi_external_ttt2_status_is_maybe
#print axioms fbi_external_ttt2_status_ne_certifiedYes
#print axioms fbiCatalogRowOfWitness
#print axioms FBIDirectionalRouteRow
#print axioms fbiDirectionalRow
#print axioms fbiDirectionalRow_fst
#print axioms fbiDirectionalRow_snd
#print axioms fbiDirectionalRouteRows
#print axioms fbiDirectionalRouteRows_length
#print axioms fbiDirectionalRouteRows_nodup
#print axioms fbiDirectionalRouteRows_complete
#print axioms fbiDirectionalRow_mem
#print axioms fbiDirectionalRow_legacy_projection
#print axioms FBIDirectionalRouteStatusCatalog
#print axioms fbi_directional_route_status_catalog

/-- The catalog really has twelve rows. -/
example : fbiDirectionalRouteRows.length = 12 := fbiDirectionalRouteRows_length

/-- The instantiation component of each fixture's row is its own instantiation field. -/
example : (fbiDirectionalRow transformedCallFBIMethod).1 = FBIInstantiation.bidirectional := rfl

end FBIClassificationReach

/-! ## LASOT 18.2 reach/axiom parity completion (supervisor validation 2026-08-10):
every checked anchor above now carries a paired axiom print; opens replicated for print-scope resolution. -/

section LasotParityCompletion
open FBIClassificationReach
open OperatorKO7
open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.FBIClassification

#print axioms certifiedFBIMethod
#print axioms directForwardFBIMethod
#print axioms fbi_certificate_evidence_is_certified_success
#print axioms fbi_construction_import_evidence_routes_to_w1
#print axioms fbi_direct_evidence_routes_to_w0
#print axioms fbi_final_catalog_certificate
#print axioms fbi_final_catalog_certificate_projects_residual_boundary
#print axioms fbi_final_catalog_certificate_projects_route_status_catalog
#print axioms fbi_final_catalog_row_route_status_exact
#print axioms fbi_final_catalog_row_supported
#print axioms fbi_final_route_status_catalog
#print axioms fbi_maybe_row_replaced_by_formal_status
#print axioms fbi_residual_adequacy_boundary_catalog
#print axioms fbi_success_with_route_evidence_has_closure_status
#print axioms fbi_transformed_call_evidence_routes_to_w2
#print axioms FBIClosureStatus
#print axioms fbiClosureStatuses
#print axioms fbiClosureStatuses_complete_exact
#print axioms fbiClosureStatuses_length
#print axioms fbiClosureStatuses_nodup
#print axioms FBIComparisonWitness
#print axioms FBIDirection
#print axioms FBIFinalCatalogCertificate
#print axioms fbiFinalCatalogMethod
#print axioms fbiFinalCatalogRoute?
#print axioms FBIFinalCatalogRow
#print axioms fbiFinalCatalogRows
#print axioms fbiFinalCatalogRows_complete_exact
#print axioms fbiFinalCatalogRows_length
#print axioms fbiFinalCatalogRows_nodup
#print axioms FBIFinalCatalogRowSupported
#print axioms fbiFinalCatalogStatus
#print axioms FBIFinalRouteStatusCatalog
#print axioms fbiGenericAdequacyBoundaries
#print axioms fbiGenericAdequacyBoundaries_complete_exact
#print axioms fbiGenericAdequacyBoundaries_length
#print axioms fbiGenericAdequacyBoundaries_nodup
#print axioms FBIGenericAdequacyBoundary
#print axioms fbiGenericAdequacyBoundaryInstantiation
#print axioms fbiGenericAdequacyBoundaryStatus
#print axioms fbiGenericBackwardAdequacyClosureTheorem
#print axioms fbiGenericForwardAdequacyClosureTheorem
#print axioms FBIHasClosureStatus
#print axioms FBIInstantiation
#print axioms FBIMethod
#print axioms FBIResidualAdequacyBoundaryCatalog
#print axioms FBIResidualBoundaryStatus
#print axioms fbiRouteClosureStatus
#print axioms FBIRoutesTo
#print axioms FBISuccessSemantics
#print axioms importedWholeFBIMethod
#print axioms transformedCallFBIMethod
end LasotParityCompletion
