import OperatorKO7.Meta.FBI_Method

namespace OperatorKO7.FBIClassification

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog

/-- A formal FBI method routes to a construction route exactly when its success semantics records that route. -/
def FBIRoutesTo (method : FBIMethod) (route : ConstructionRoute) : Prop :=
  method.successSemantics.route? = some route

/-- A formal FBI method has a closure status exactly when its success semantics records that status. -/
def FBIHasClosureStatus (method : FBIMethod) (status : FBIClosureStatus) : Prop :=
  method.successSemantics.closureStatus = status

/-- Closure-status projection for FBI methods that carry route evidence. -/
def fbiRouteClosureStatus : ConstructionRoute → FBIClosureStatus
  | .W0 => .reducedToExistingTheorem .W0
  | .W1 => .licensedEscape .W1
  | .W2 => .licensedEscape .W2

/-- The finite FBI closure-status list formalized in this sprint. -/
def fbiClosureStatuses : List FBIClosureStatus :=
  [.reducedToExistingTheorem .W0,
    .licensedEscape .W1,
    .licensedEscape .W2,
    .certifiedSuccess]

/-- Final catalog rows for theorem-backed FBI route/status packaging. -/
inductive FBIFinalCatalogRow where
  | directW0Reduction
  | constructionW1LicensedEscape
  | transformedCallW2LicensedEscape
  | certifiedSuccess
deriving DecidableEq, Repr

/-- The finite theorem-backed FBI catalog landed in the final residual-method sprint. -/
def fbiFinalCatalogRows : List FBIFinalCatalogRow :=
  [.directW0Reduction,
    .constructionW1LicensedEscape,
    .transformedCallW2LicensedEscape,
    .certifiedSuccess]

/-- The FBI method carried by each final catalog row. -/
def fbiFinalCatalogMethod : FBIFinalCatalogRow → FBIMethod
  | .directW0Reduction => directForwardFBIMethod
  | .constructionW1LicensedEscape => importedWholeFBIMethod
  | .transformedCallW2LicensedEscape => transformedCallFBIMethod
  | .certifiedSuccess => certifiedFBIMethod

/-- The route projection carried by each final FBI catalog row. -/
def fbiFinalCatalogRoute? : FBIFinalCatalogRow → Option ConstructionRoute
  | .directW0Reduction => some .W0
  | .constructionW1LicensedEscape => some .W1
  | .transformedCallW2LicensedEscape => some .W2
  | .certifiedSuccess => none

/-- The closure status carried by each final FBI catalog row. -/
def fbiFinalCatalogStatus : FBIFinalCatalogRow → FBIClosureStatus
  | .directW0Reduction => .reducedToExistingTheorem .W0
  | .constructionW1LicensedEscape => .licensedEscape .W1
  | .transformedCallW2LicensedEscape => .licensedEscape .W2
  | .certifiedSuccess => .certifiedSuccess

/-- The theorem-backed support payload carried by each final FBI catalog row. -/
def FBIFinalCatalogRowSupported : FBIFinalCatalogRow → Prop
  | .directW0Reduction =>
      FBIRoutesTo directForwardFBIMethod .W0 ∧
        FBIHasClosureStatus directForwardFBIMethod (.reducedToExistingTheorem .W0)
  | .constructionW1LicensedEscape =>
      FBIRoutesTo importedWholeFBIMethod .W1 ∧
        FBIHasClosureStatus importedWholeFBIMethod (.licensedEscape .W1) ∧
        canonicalWitnessRoute .w1ImportedWhole = .W1 ∧
        canonicalWitnessW1ImportClass? .w1ImportedWhole = some .importedWholeWitness
  | .transformedCallW2LicensedEscape =>
      FBIRoutesTo transformedCallFBIMethod .W2 ∧
        FBIHasClosureStatus transformedCallFBIMethod (.licensedEscape .W2) ∧
        canonicalWitnessRoute .w2FullDuplicating = .W2 ∧
        canonicalWitnessW2TransformClass? .w2FullDuplicating = some .ko7DPProjection
  | .certifiedSuccess =>
      FBIHasClosureStatus certifiedFBIMethod .certifiedSuccess

/-- Generic FBI adequacy boundaries tracked by the final catalog ledger. -/
inductive FBIGenericAdequacyBoundary where
  | forwardAdequacy
  | backwardAdequacy
deriving DecidableEq, Repr

/-- Closed-status vocabulary for generic FBI adequacy rows. -/
inductive FBIResidualBoundaryStatus where
  | closedByNamedTheorem (theoremName : String)
deriving DecidableEq, Repr

/-- Verbatim theorem name closing the generic forward FBI adequacy question. -/
def fbiGenericForwardAdequacyClosureTheorem : String :=
  "fbi_generic_forward_adequacy_universal_unconditional"

/-- Verbatim theorem name closing the generic backward FBI adequacy question. -/
def fbiGenericBackwardAdequacyClosureTheorem : String :=
  "fbi_generic_backward_adequacy_universal_unconditional"

/-- The finite FBI adequacy boundary list tracked by the final catalog. -/
def fbiGenericAdequacyBoundaries : List FBIGenericAdequacyBoundary :=
  [.forwardAdequacy, .backwardAdequacy]

/-- Instantiation mode corresponding to each tracked generic FBI adequacy boundary. -/
def fbiGenericAdequacyBoundaryInstantiation : FBIGenericAdequacyBoundary → FBIInstantiation
  | .forwardAdequacy => .forwardOnly
  | .backwardAdequacy => .backwardOnly

/-- Residual-boundary status attached to each generic FBI adequacy row. -/
def fbiGenericAdequacyBoundaryStatus : FBIGenericAdequacyBoundary → FBIResidualBoundaryStatus
  | .forwardAdequacy => .closedByNamedTheorem fbiGenericForwardAdequacyClosureTheorem
  | .backwardAdequacy => .closedByNamedTheorem fbiGenericBackwardAdequacyClosureTheorem

/-- The finite FBI closure-status list has no duplicates. -/
theorem fbiClosureStatuses_nodup : fbiClosureStatuses.Nodup := by
  decide

/-- The finite FBI closure-status list has exact size four. -/
theorem fbiClosureStatuses_length : fbiClosureStatuses.length = 4 := by
  rfl

/-- Exact membership characterization for the formal FBI closure-status list. -/
theorem fbiClosureStatuses_complete_exact (status : FBIClosureStatus) :
    status ∈ fbiClosureStatuses ↔
      status = .reducedToExistingTheorem .W0
        ∨ status = .licensedEscape .W1
        ∨ status = .licensedEscape .W2
        ∨ status = .certifiedSuccess := by
  cases status with
  | reducedToExistingTheorem route =>
      cases route <;> simp [fbiClosureStatuses]
  | licensedEscape route =>
      cases route <;> simp [fbiClosureStatuses]
  | certifiedSuccess =>
      simp [fbiClosureStatuses]

/-- The finite final FBI catalog row list has no duplicates. -/
theorem fbiFinalCatalogRows_nodup : fbiFinalCatalogRows.Nodup := by
  decide

/-- The finite final FBI catalog row list has exact size four. -/
theorem fbiFinalCatalogRows_length : fbiFinalCatalogRows.length = 4 := by
  rfl

/-- Exact membership characterization for the final FBI route/status catalog. -/
theorem fbiFinalCatalogRows_complete_exact (row : FBIFinalCatalogRow) :
    row ∈ fbiFinalCatalogRows ↔
      row = .directW0Reduction
        ∨ row = .constructionW1LicensedEscape
        ∨ row = .transformedCallW2LicensedEscape
        ∨ row = .certifiedSuccess := by
  cases row <;> simp [fbiFinalCatalogRows]

/-- The finite generic FBI adequacy boundary list has no duplicates. -/
theorem fbiGenericAdequacyBoundaries_nodup : fbiGenericAdequacyBoundaries.Nodup := by
  decide

/-- The finite generic FBI adequacy boundary list has exact size two. -/
theorem fbiGenericAdequacyBoundaries_length : fbiGenericAdequacyBoundaries.length = 2 := by
  rfl

/-- Exact membership characterization for the generic FBI adequacy boundary list. -/
theorem fbiGenericAdequacyBoundaries_complete_exact (boundary : FBIGenericAdequacyBoundary) :
    boundary ∈ fbiGenericAdequacyBoundaries ↔
      boundary = .forwardAdequacy ∨ boundary = .backwardAdequacy := by
  cases boundary <;> simp [fbiGenericAdequacyBoundaries]

/-- Direct FBI evidence lands in the W0 route. -/
theorem fbi_direct_evidence_routes_to_w0 :
    FBIRoutesTo directForwardFBIMethod .W0 := by
  rfl

/-- Transformed-call FBI evidence lands in the existing W2 route catalog. -/
theorem fbi_transformed_call_evidence_routes_to_w2 :
    FBIRoutesTo transformedCallFBIMethod .W2
      ∧ canonicalWitnessRoute .w2FullDuplicating = .W2
      ∧ canonicalWitnessW2TransformClass? .w2FullDuplicating = some .ko7DPProjection := by
  exact ⟨rfl, canonical_w2_route_catalog.1.1, canonical_w2_route_catalog.1.2⟩

/-- Construction/import FBI evidence lands in the existing W1 route catalog. -/
theorem fbi_construction_import_evidence_routes_to_w1 :
    FBIRoutesTo importedWholeFBIMethod .W1
      ∧ canonicalWitnessRoute .w1ImportedWhole = .W1
      ∧ canonicalWitnessW1ImportClass? .w1ImportedWhole = some .importedWholeWitness := by
  exact ⟨rfl, canonical_w1_route_catalog.2.2.1.1, canonical_w1_route_catalog.2.2.1.2⟩

/-- Concrete FBI certificate evidence is classified as certified success. -/
theorem fbi_certificate_evidence_is_certified_success :
    FBIHasClosureStatus certifiedFBIMethod .certifiedSuccess := by
  rfl

/-- Any FBI success carrying route evidence inherits the matching formal closure status. -/
theorem fbi_success_with_route_evidence_has_closure_status
    {method : FBIMethod} {route : ConstructionRoute}
    (hroute : FBIRoutesTo method route) :
    FBIHasClosureStatus method (fbiRouteClosureStatus route) := by
  cases method with
  | mk instantiation comparisonWitness =>
      cases comparisonWitness <;> cases hroute <;> rfl

/-- Every formal FBI method lands in the finite closure-status list. -/
theorem fbi_method_has_listed_closure_status (method : FBIMethod) :
    method.successSemantics.closureStatus ∈ fbiClosureStatuses := by
  cases method with
  | mk instantiation comparisonWitness =>
      cases comparisonWitness <;>
        simp [FBIMethod.successSemantics, FBIComparisonWitness.closureStatus, fbiClosureStatuses]

/-- Every final FBI catalog row has exact route and status projections. -/
theorem fbi_final_catalog_row_route_status_exact (row : FBIFinalCatalogRow) :
    (fbiFinalCatalogMethod row).successSemantics.route? = fbiFinalCatalogRoute? row ∧
      (fbiFinalCatalogMethod row).successSemantics.closureStatus = fbiFinalCatalogStatus row := by
  cases row <;> exact ⟨rfl, rfl⟩

/-- Every final FBI catalog row is supported by explicit theorem-backed evidence. -/
theorem fbi_final_catalog_row_supported (row : FBIFinalCatalogRow) :
    FBIFinalCatalogRowSupported row := by
  cases row with
  | directW0Reduction =>
      exact ⟨fbi_direct_evidence_routes_to_w0,
        by
          simpa [fbiRouteClosureStatus] using
            fbi_success_with_route_evidence_has_closure_status fbi_direct_evidence_routes_to_w0⟩
  | constructionW1LicensedEscape =>
      exact ⟨fbi_construction_import_evidence_routes_to_w1.1,
        by
          simpa [fbiRouteClosureStatus] using
            fbi_success_with_route_evidence_has_closure_status
              fbi_construction_import_evidence_routes_to_w1.1,
        fbi_construction_import_evidence_routes_to_w1.2.1,
        fbi_construction_import_evidence_routes_to_w1.2.2⟩
  | transformedCallW2LicensedEscape =>
      exact ⟨fbi_transformed_call_evidence_routes_to_w2.1,
        by
          simpa [fbiRouteClosureStatus] using
            fbi_success_with_route_evidence_has_closure_status
              fbi_transformed_call_evidence_routes_to_w2.1,
        fbi_transformed_call_evidence_routes_to_w2.2.1,
        fbi_transformed_call_evidence_routes_to_w2.2.2⟩
  | certifiedSuccess =>
      exact fbi_certificate_evidence_is_certified_success

/-- Paper-facing proposition for the final theorem-backed FBI route/status catalog. -/
abbrev FBIFinalRouteStatusCatalog : Prop :=
  ∀ row : FBIFinalCatalogRow,
    row ∈ fbiFinalCatalogRows ∧
      FBIFinalCatalogRowSupported row ∧
      (fbiFinalCatalogMethod row).successSemantics.route? = fbiFinalCatalogRoute? row ∧
      (fbiFinalCatalogMethod row).successSemantics.closureStatus = fbiFinalCatalogStatus row

/-- The final FBI route/status catalog is fully realized by explicit theorem-backed rows. -/
theorem fbi_final_route_status_catalog : FBIFinalRouteStatusCatalog := by
  intro row
  exact ⟨(fbiFinalCatalogRows_complete_exact row).2 <| by
    cases row <;> simp,
    fbi_final_catalog_row_supported row,
    fbi_final_catalog_row_route_status_exact row⟩

/-- Paper-facing proposition for the explicit generic FBI adequacy boundary ledger. -/
abbrev FBIResidualAdequacyBoundaryCatalog : Prop :=
  ∀ boundary : FBIGenericAdequacyBoundary,
    boundary ∈ fbiGenericAdequacyBoundaries ∧
      (fbiGenericAdequacyBoundaryInstantiation boundary =
        match boundary with
        | .forwardAdequacy => FBIInstantiation.forwardOnly
        | .backwardAdequacy => FBIInstantiation.backwardOnly) 
      ∧ (fbiGenericAdequacyBoundaryStatus boundary =
        match boundary with
        | .forwardAdequacy => .closedByNamedTheorem fbiGenericForwardAdequacyClosureTheorem
        | .backwardAdequacy => .closedByNamedTheorem fbiGenericBackwardAdequacyClosureTheorem)

/-- The explicit FBI adequacy-boundary ledger closes both generic adequacy rows by named theorem. -/
theorem fbi_residual_adequacy_boundary_catalog : FBIResidualAdequacyBoundaryCatalog := by
  intro boundary
  cases boundary <;> simp [fbiGenericAdequacyBoundaries,
    fbiGenericAdequacyBoundaryInstantiation, fbiGenericAdequacyBoundaryStatus,
    fbiGenericForwardAdequacyClosureTheorem, fbiGenericBackwardAdequacyClosureTheorem]

/-- Certificate packaging the final FBI route/status catalog and the adequacy boundary ledger. -/
structure FBIFinalCatalogCertificate where
  routeStatusCatalog : FBIFinalRouteStatusCatalog
  residualAdequacyBoundary : FBIResidualAdequacyBoundaryCatalog

/-- The final FBI sprint closes the theorem-backed rows and packages the adequacy boundary ledger. -/
theorem fbi_final_catalog_certificate : FBIFinalCatalogCertificate := by
  exact {
    routeStatusCatalog := fbi_final_route_status_catalog
    residualAdequacyBoundary := fbi_residual_adequacy_boundary_catalog
  }

/-- The final FBI certificate projects the theorem-backed route/status catalog. -/
theorem fbi_final_catalog_certificate_projects_route_status_catalog :
    FBIFinalRouteStatusCatalog :=
  fbi_final_catalog_certificate.routeStatusCatalog

/-- The final FBI certificate projects the generic adequacy boundary ledger. -/
theorem fbi_final_catalog_certificate_projects_residual_boundary :
    FBIResidualAdequacyBoundaryCatalog :=
  fbi_final_catalog_certificate.residualAdequacyBoundary

/-- The internal FBI classification assigns every method a formal closure status. This is a
statement about the internal carrier only; it says nothing about the external TTT2 FBI strategy
run, whose status is recorded separately as `fbiExternalTTT2Status`. -/
theorem fbi_maybe_row_replaced_by_formal_status (method : FBIMethod) :
    ∃ status ∈ fbiClosureStatuses, FBIHasClosureStatus method status := by
  exact ⟨method.successSemantics.closureStatus,
    fbi_method_has_listed_closure_status method,
    rfl⟩

/-! ### External tool status, kept apart from the internal classification -/

/-- Status vocabulary for an *external* termination-tool run. This is deliberately disjoint from
`FBIClosureStatus`, which classifies the internal carrier only. -/
inductive FBIExternalToolStatus where
  /-- The tool's search did not succeed. This is a search non-success, not an impossibility. -/
  | maybe
  /-- The tool returned a success that was independently certified. -/
  | certifiedYes
deriving DecidableEq, Repr

/-- The external TTT2 forward/backward-instantiation run remains a search non-success. Nothing in
the internal direction-indexed catalog below changes it. -/
def fbiExternalTTT2Status : FBIExternalToolStatus := .maybe

/-- The external TTT2 FBI row is MAYBE. -/
theorem fbi_external_ttt2_status_is_maybe : fbiExternalTTT2Status = .maybe := rfl

/-- The external TTT2 FBI row is not a certified success. -/
theorem fbi_external_ttt2_status_ne_certifiedYes :
    fbiExternalTTT2Status ≠ .certifiedYes := by decide

/-! ### Direction-indexed route/status catalog

The rows below index the existing route/status classification by instantiation mode. This is a
direction-indexed route/status catalog. It is not a semantic adequacy criterion and not a generic
adequacy theorem: the catalog component is computed from the comparison-witness constructor, and
the instantiation component is definitionally the method's own instantiation field. -/

/-- A direction-indexed route/status row: an instantiation mode paired with a final catalog row. -/
abbrev FBIDirectionalRouteRow := FBIInstantiation × FBIFinalCatalogRow

/-- The final catalog row determined by a comparison-witness constructor. -/
def fbiCatalogRowOfWitness : FBIComparisonWitness → FBIFinalCatalogRow
  | .directWholeTermComparison => .directW0Reduction
  | .transformedCallEvidence _ _ _ _ => .transformedCallW2LicensedEscape
  | .constructionImportEvidence _ _ _ _ => .constructionW1LicensedEscape
  | .concreteCertificateEvidence _ => .certifiedSuccess

/-- The total direction-indexed assignment from methods to rows. -/
def fbiDirectionalRow (method : FBIMethod) : FBIDirectionalRouteRow :=
  (method.instantiation, fbiCatalogRowOfWitness method.comparisonWitness)

/-- The instantiation component of a method's row is definitionally the method's instantiation. -/
theorem fbiDirectionalRow_fst (method : FBIMethod) :
    (fbiDirectionalRow method).1 = method.instantiation := rfl

/-- The catalog component of a method's row is the row computed from its comparison witness. -/
theorem fbiDirectionalRow_snd (method : FBIMethod) :
    (fbiDirectionalRow method).2 = fbiCatalogRowOfWitness method.comparisonWitness := rfl

/-- The exact twelve-row direction-indexed route/status catalog: three instantiation modes times
four final catalog rows. -/
def fbiDirectionalRouteRows : List FBIDirectionalRouteRow :=
  [ (.forwardOnly, .directW0Reduction)
  , (.forwardOnly, .constructionW1LicensedEscape)
  , (.forwardOnly, .transformedCallW2LicensedEscape)
  , (.forwardOnly, .certifiedSuccess)
  , (.backwardOnly, .directW0Reduction)
  , (.backwardOnly, .constructionW1LicensedEscape)
  , (.backwardOnly, .transformedCallW2LicensedEscape)
  , (.backwardOnly, .certifiedSuccess)
  , (.bidirectional, .directW0Reduction)
  , (.bidirectional, .constructionW1LicensedEscape)
  , (.bidirectional, .transformedCallW2LicensedEscape)
  , (.bidirectional, .certifiedSuccess)
  ]

/-- The direction-indexed catalog has exact size twelve. -/
theorem fbiDirectionalRouteRows_length : fbiDirectionalRouteRows.length = 12 := by rfl

/-- The direction-indexed catalog has no duplicate rows. -/
theorem fbiDirectionalRouteRows_nodup : fbiDirectionalRouteRows.Nodup := by decide

/-- Every direction-indexed row occurs in the catalog. -/
theorem fbiDirectionalRouteRows_complete (row : FBIDirectionalRouteRow) :
    row ∈ fbiDirectionalRouteRows := by
  obtain ⟨instantiation, catalogRow⟩ := row
  cases instantiation <;> cases catalogRow <;> decide

/-- Every method's direction-indexed row is one of the twelve. -/
theorem fbiDirectionalRow_mem (method : FBIMethod) :
    fbiDirectionalRow method ∈ fbiDirectionalRouteRows :=
  fbiDirectionalRouteRows_complete _

/-- **Legacy projection.** The catalog component of a method's direction-indexed row carries the
method's own route and closure-status tags, so the pre-existing route/status classification is
recovered from the direction-indexed one without change. -/
theorem fbiDirectionalRow_legacy_projection (method : FBIMethod) :
    method.successSemantics.route? = fbiFinalCatalogRoute? (fbiDirectionalRow method).2 ∧
      method.successSemantics.closureStatus =
        fbiFinalCatalogStatus (fbiDirectionalRow method).2 := by
  cases method with
  | mk instantiation comparisonWitness =>
      cases comparisonWitness <;> exact ⟨rfl, rfl⟩

/-- Paper-facing proposition for the direction-indexed route/status catalog. -/
abbrev FBIDirectionalRouteStatusCatalog : Prop :=
  ∀ method : FBIMethod,
    fbiDirectionalRow method ∈ fbiDirectionalRouteRows ∧
      (fbiDirectionalRow method).1 = method.instantiation ∧
      method.successSemantics.route? = fbiFinalCatalogRoute? (fbiDirectionalRow method).2 ∧
      method.successSemantics.closureStatus =
        fbiFinalCatalogStatus (fbiDirectionalRow method).2

/-- The direction-indexed route/status catalog is total over `FBIMethod`. -/
theorem fbi_directional_route_status_catalog : FBIDirectionalRouteStatusCatalog := by
  intro method
  exact ⟨fbiDirectionalRow_mem method, fbiDirectionalRow_fst method,
    (fbiDirectionalRow_legacy_projection method).1,
    (fbiDirectionalRow_legacy_projection method).2⟩

end OperatorKO7.FBIClassification
