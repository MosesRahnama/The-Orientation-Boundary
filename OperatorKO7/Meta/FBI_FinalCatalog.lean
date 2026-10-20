import OperatorKO7.Meta.FBI_AdequacyBoundary

/-!
# FBI Final Catalog Boundary

This module provides a thin import boundary for the theorem-backed FBI final
catalog. It re-exports the compact route/status and residual-boundary surfaces
without requiring downstream users to depend directly on the full FBI
classification namespace.
-/

namespace OperatorKO7.FBIFinalCatalog

/-- Legacy compatibility alias for closed-carrier catalog coverage. It is not semantic adequacy. -/
abbrev FBIFinalCoverage (method : FBIMethod) : Prop :=
  OperatorKO7.FBIAdequacyBoundary.FBIFinalCoverage method

/-- Legacy compatibility alias for the forward-indexed catalog datum type. -/
abbrev FBIGenericForwardAdequacyData : Type :=
  OperatorKO7.FBIAdequacyBoundary.FBIGenericForwardAdequacyData

/-- Legacy compatibility alias for the backward-indexed catalog datum type. -/
abbrev FBIGenericBackwardAdequacyData : Type :=
  OperatorKO7.FBIAdequacyBoundary.FBIGenericBackwardAdequacyData

/-- Legacy compatibility alias for the canonical forward-indexed catalog fragment. -/
abbrev canonicalForwardAdequacyData : FBIGenericForwardAdequacyData :=
  OperatorKO7.FBIAdequacyBoundary.canonicalForwardAdequacyData

/-- Legacy compatibility alias for the canonical backward-indexed catalog fragment. -/
abbrev canonicalBackwardAdequacyData : FBIGenericBackwardAdequacyData :=
  OperatorKO7.FBIAdequacyBoundary.canonicalBackwardAdequacyData

/-- Stable API alias for the theorem-backed FBI route/status catalog. -/
abbrev FBIFinalRouteStatusCatalog : Prop :=
  OperatorKO7.FBIClassification.FBIFinalRouteStatusCatalog

/-- Stable API entrypoint for the theorem-backed FBI route/status catalog. -/
theorem fbi_final_route_status_catalog : FBIFinalRouteStatusCatalog :=
  OperatorKO7.FBIClassification.fbi_final_route_status_catalog

/-- Stable API alias for the residual adequacy boundary reconciled by the FBI final catalog. -/
abbrev FBIResidualAdequacyBoundaryCatalog : Prop :=
  OperatorKO7.FBIClassification.FBIResidualAdequacyBoundaryCatalog

/-- Stable API entrypoint for the residual adequacy boundary reconciled by the FBI final catalog. -/
theorem fbi_residual_adequacy_boundary_catalog : FBIResidualAdequacyBoundaryCatalog :=
  OperatorKO7.FBIClassification.fbi_residual_adequacy_boundary_catalog

/-- Stable API alias for the exact FBI adequacy-boundary catalog. -/
abbrev FBIAdequacyBoundaryCatalog : Prop :=
  OperatorKO7.FBIAdequacyBoundary.FBIAdequacyBoundaryCatalog

/-- Stable API entrypoint for the exact FBI adequacy-boundary catalog. -/
theorem fbi_adequacy_boundary_catalog : FBIAdequacyBoundaryCatalog :=
  OperatorKO7.FBIAdequacyBoundary.fbi_adequacy_boundary_catalog

/-- Stable API projection of the named forward adequacy datum. -/
theorem fbi_adequacy_boundary_catalog_projects_forward_data :
    Nonempty FBIGenericForwardAdequacyData :=
  OperatorKO7.FBIAdequacyBoundary.fbi_adequacy_boundary_catalog_projects_forward_data
    OperatorKO7.FBIAdequacyBoundary.fbi_adequacy_boundary_catalog

/-- Stable API projection of the named backward adequacy datum. -/
theorem fbi_adequacy_boundary_catalog_projects_backward_data :
    Nonempty FBIGenericBackwardAdequacyData :=
  OperatorKO7.FBIAdequacyBoundary.fbi_adequacy_boundary_catalog_projects_backward_data
    OperatorKO7.FBIAdequacyBoundary.fbi_adequacy_boundary_catalog

/-- Stable API projection of universal forward FBI coverage. -/
theorem fbi_adequacy_boundary_catalog_projects_forward_universal_coverage
    (method : FBIMethod) :
    OperatorKO7.FBIAdequacyBoundary.FBIGenericForwardAdequacyClass method ->
      FBIFinalCoverage method :=
  OperatorKO7.FBIAdequacyBoundary.fbi_adequacy_boundary_catalog_projects_forward_universal_coverage
    OperatorKO7.FBIAdequacyBoundary.fbi_adequacy_boundary_catalog method

/-- Stable API projection of universal backward FBI coverage. -/
theorem fbi_adequacy_boundary_catalog_projects_backward_universal_coverage
    (method : FBIMethod) :
    OperatorKO7.FBIAdequacyBoundary.FBIGenericBackwardAdequacyClass method ->
      FBIFinalCoverage method :=
  OperatorKO7.FBIAdequacyBoundary.fbi_adequacy_boundary_catalog_projects_backward_universal_coverage
    OperatorKO7.FBIAdequacyBoundary.fbi_adequacy_boundary_catalog method

/-- Stable API projection of the canonical forward adequacy fragment. -/
theorem canonicalForwardAdequacyData_projects_directW0 :
    canonicalForwardAdequacyData.method.successSemantics.route? = some .W0 ∧
      canonicalForwardAdequacyData.method.successSemantics.closureStatus =
        .reducedToExistingTheorem .W0 :=
  OperatorKO7.FBIAdequacyBoundary.canonicalForwardAdequacyData_projects_directW0

/-- Stable API projection of the canonical backward adequacy fragment. -/
theorem canonicalBackwardAdequacyData_projects_importedWholeW1 :
    canonicalBackwardAdequacyData.method.successSemantics.route? = some .W1 ∧
      canonicalBackwardAdequacyData.method.successSemantics.closureStatus =
        .licensedEscape .W1 :=
  OperatorKO7.FBIAdequacyBoundary.canonicalBackwardAdequacyData_projects_importedWholeW1

/-- The four theorem-backed closure obligations exposed by the FBI carrier. -/
inductive FBIClosureRow where
  | genericForwardAdequacy
  | genericBackwardAdequacy
  | completeMethodCoverage
  | directionParametricCoverage
  deriving DecidableEq, Repr

/-- Exact enumeration of the FBI closure rows. -/
def fbiClosureRows : List FBIClosureRow :=
  [.genericForwardAdequacy,
    .genericBackwardAdequacy,
    .completeMethodCoverage,
    .directionParametricCoverage]

/-- Row-specific proof content.  No row is represented by a string-only status. -/
def FBIClosureRowSupported : FBIClosureRow → Prop
  | .genericForwardAdequacy =>
      ∀ method : FBIMethod,
        OperatorKO7.FBIAdequacyBoundary.FBIGenericForwardAdequacyClass method →
          FBIFinalCoverage method
  | .genericBackwardAdequacy =>
      ∀ method : FBIMethod,
        OperatorKO7.FBIAdequacyBoundary.FBIGenericBackwardAdequacyClass method →
          FBIFinalCoverage method
  | .completeMethodCoverage =>
      ∀ method : FBIMethod,
        method.successSemantics.closureStatus ∈
            OperatorKO7.FBIClassification.fbiClosureStatuses ∧
          FBIFinalCoverage method
  | .directionParametricCoverage =>
      ∀ direction : FBIDirection, ∀ method : FBIMethod,
        method.matchesDirection direction → FBIFinalCoverage method

/-- The closure-row list has no duplicates. -/
theorem fbiClosureRows_nodup : fbiClosureRows.Nodup := by
  decide

/-- The closure-row list has exact size four. -/
theorem fbiClosureRows_length : fbiClosureRows.length = 4 := by
  rfl

/-- Every closure-row constructor occurs in the list. -/
theorem fbiClosureRows_complete_exact (row : FBIClosureRow) :
    row ∈ fbiClosureRows := by
  cases row <;> simp [fbiClosureRows]

/-- Every FBI closure row is discharged by an actual theorem. -/
theorem fbiClosureRowSupported_holds (row : FBIClosureRow) :
    FBIClosureRowSupported row := by
  cases row with
  | genericForwardAdequacy =>
      intro method h
      exact (OperatorKO7.FBIGenericAdequacy.fbi_forward_directional_coverage method h.1).2.2
  | genericBackwardAdequacy =>
      intro method h
      exact (OperatorKO7.FBIGenericAdequacy.fbi_backward_directional_coverage method h.1).2.2
  | completeMethodCoverage =>
      exact OperatorKO7.FBIAdequacyBoundary.fbi_no_outside_catalog_method
  | directionParametricCoverage =>
      intro direction method h
      exact (OperatorKO7.FBIGenericAdequacy.fbi_directional_coverage direction method h).2

/-- Exact theorem-backed closure catalog for the full `FBIMethod` datatype. -/
abbrev FBIClosureCatalog : Prop :=
  ∀ row : FBIClosureRow,
    row ∈ fbiClosureRows ∧ FBIClosureRowSupported row

/-- All FBI closure rows are proved. -/
theorem fbi_closure_catalog : FBIClosureCatalog := by
  intro row
  exact ⟨fbiClosureRows_complete_exact row,
    fbiClosureRowSupported_holds row⟩

/-- The closure catalog projects universal forward adequacy. -/
theorem fbi_closure_catalog_projects_forward_adequacy
    (method : FBIMethod) :
    OperatorKO7.FBIAdequacyBoundary.FBIGenericForwardAdequacyClass method →
      FBIFinalCoverage method :=
  (fbi_closure_catalog .genericForwardAdequacy).2 method

/-- The closure catalog projects universal backward adequacy. -/
theorem fbi_closure_catalog_projects_backward_adequacy
    (method : FBIMethod) :
    OperatorKO7.FBIAdequacyBoundary.FBIGenericBackwardAdequacyClass method →
      FBIFinalCoverage method :=
  (fbi_closure_catalog .genericBackwardAdequacy).2 method

/-- The closure catalog classifies every inhabitant of the closed FBI carrier. -/
theorem fbi_closure_catalog_projects_complete_method_coverage
    (method : FBIMethod) :
    method.successSemantics.closureStatus ∈
        OperatorKO7.FBIClassification.fbiClosureStatuses ∧
      FBIFinalCoverage method :=
  (fbi_closure_catalog .completeMethodCoverage).2 method

/-- The closure catalog projects direction-parametric coverage. -/
theorem fbi_closure_catalog_projects_direction_coverage
    (direction : FBIDirection) (method : FBIMethod) :
    method.matchesDirection direction → FBIFinalCoverage method :=
  (fbi_closure_catalog .directionParametricCoverage).2 direction method

/-- Paper-facing certificate for the fully closed FBI import boundary. -/
structure FBIFinalCatalogCertificate : Prop where
  routeStatusCatalog : FBIFinalRouteStatusCatalog
  residualAdequacyBoundary : FBIResidualAdequacyBoundaryCatalog
  adequacyBoundary : FBIAdequacyBoundaryCatalog
  closureCatalog : FBIClosureCatalog
  noOutsideCatalog : ∀ method : FBIMethod,
    method.successSemantics.closureStatus ∈
        OperatorKO7.FBIClassification.fbiClosureStatuses ∧
      FBIFinalCoverage method
  directionUniversal : ∀ direction : FBIDirection, ∀ method : FBIMethod,
    method.matchesDirection direction → FBIFinalCoverage method

/-- Fully theorem-backed FBI final-catalog certificate. -/
theorem fbi_final_catalog_certificate : FBIFinalCatalogCertificate := by
  exact {
    routeStatusCatalog := fbi_final_route_status_catalog
    residualAdequacyBoundary := fbi_residual_adequacy_boundary_catalog
    adequacyBoundary := fbi_adequacy_boundary_catalog
    closureCatalog := fbi_closure_catalog
    noOutsideCatalog :=
      OperatorKO7.FBIAdequacyBoundary.fbi_no_outside_catalog_method
    directionUniversal := fun direction method h =>
      (OperatorKO7.FBIGenericAdequacy.fbi_directional_coverage direction method h).2
  }

/-- The certificate projects the theorem-backed FBI route/status catalog. -/
theorem fbi_final_catalog_certificate_projects_route_status_catalog :
    FBIFinalRouteStatusCatalog :=
  fbi_final_catalog_certificate.routeStatusCatalog

/-- The certificate projects the residual adequacy boundary. -/
theorem fbi_final_catalog_certificate_projects_residual_boundary :
    FBIResidualAdequacyBoundaryCatalog :=
  fbi_final_catalog_certificate.residualAdequacyBoundary

/-- The certificate projects the exact adequacy catalog. -/
theorem fbi_final_catalog_certificate_projects_adequacy_boundary :
    FBIAdequacyBoundaryCatalog :=
  fbi_final_catalog_certificate.adequacyBoundary

/-- The certificate projects the complete closure catalog. -/
theorem fbi_final_catalog_certificate_projects_closure_catalog :
    FBIClosureCatalog :=
  fbi_final_catalog_certificate.closureCatalog

/-- The certificate projects complete classification of every FBI method. -/
theorem fbi_final_catalog_certificate_projects_no_outside_catalog_method
    (method : FBIMethod) :
    method.successSemantics.closureStatus ∈
        OperatorKO7.FBIClassification.fbiClosureStatuses ∧
      FBIFinalCoverage method :=
  fbi_final_catalog_certificate.noOutsideCatalog method

/-- Deprecated compatibility projection. Its proof consumes the direction premise, but the legacy
conclusion erases that direction; use `fbi_directional_coverage_indexed` for the indexed statement. -/
theorem fbi_final_catalog_certificate_projects_direction_universal
    (direction : FBIDirection) (method : FBIMethod) :
    method.matchesDirection direction → FBIFinalCoverage method :=
  fbi_final_catalog_certificate.directionUniversal direction method

/-! ## Direction-indexed route/status catalog

Stable API surface for the twelve-row direction-indexed catalog. These are route and status
classification statements. They are not semantic adequacy theorems and make no orientation claim,
and they leave the external TTT2 FBI result untouched. -/

/-- Stable API alias for a direction-indexed route/status row. -/
abbrev FBIDirectionalRouteRow : Type :=
  OperatorKO7.FBIClassification.FBIDirectionalRouteRow

/-- Stable API alias for the twelve-row direction-indexed catalog. -/
abbrev fbiDirectionalRouteRows : List FBIDirectionalRouteRow :=
  OperatorKO7.FBIClassification.fbiDirectionalRouteRows

/-- Stable API alias for the total method-to-row assignment. -/
abbrev fbiDirectionalRow (method : FBIMethod) : FBIDirectionalRouteRow :=
  OperatorKO7.FBIClassification.fbiDirectionalRow method

/-- The direction-indexed catalog has exact size twelve. -/
theorem fbiDirectionalRouteRows_length : fbiDirectionalRouteRows.length = 12 :=
  OperatorKO7.FBIClassification.fbiDirectionalRouteRows_length

/-- The direction-indexed catalog has no duplicate rows. -/
theorem fbiDirectionalRouteRows_nodup : fbiDirectionalRouteRows.Nodup :=
  OperatorKO7.FBIClassification.fbiDirectionalRouteRows_nodup

/-- Every direction-indexed row occurs in the catalog. -/
theorem fbiDirectionalRouteRows_complete (row : FBIDirectionalRouteRow) :
    row ∈ fbiDirectionalRouteRows :=
  OperatorKO7.FBIClassification.fbiDirectionalRouteRows_complete row

/-- The instantiation component of a method's row is definitionally its instantiation field. -/
theorem fbiDirectionalRow_fst (method : FBIMethod) :
    (fbiDirectionalRow method).1 = method.instantiation :=
  OperatorKO7.FBIClassification.fbiDirectionalRow_fst method

/-- Legacy projection: the direction-indexed row recovers the method's route and status tags. -/
theorem fbiDirectionalRow_legacy_projection (method : FBIMethod) :
    method.successSemantics.route? =
        OperatorKO7.FBIClassification.fbiFinalCatalogRoute? (fbiDirectionalRow method).2 ∧
      method.successSemantics.closureStatus =
        OperatorKO7.FBIClassification.fbiFinalCatalogStatus (fbiDirectionalRow method).2 :=
  OperatorKO7.FBIClassification.fbiDirectionalRow_legacy_projection method

/-- Stable API alias for the direction-indexed route/status catalog proposition. -/
abbrev FBIDirectionalRouteStatusCatalog : Prop :=
  OperatorKO7.FBIClassification.FBIDirectionalRouteStatusCatalog

/-- Stable API entrypoint for the direction-indexed route/status catalog. -/
theorem fbi_directional_route_status_catalog : FBIDirectionalRouteStatusCatalog :=
  OperatorKO7.FBIClassification.fbi_directional_route_status_catalog

/-- Direction-indexed coverage that consumes its premise and exposes the direction. -/
theorem fbi_directional_coverage_indexed (direction : FBIDirection) (method : FBIMethod)
    (h : method.matchesDirection direction) :
    direction ∈ (fbiDirectionalRow method).1.directions ∧ FBIFinalCoverage method :=
  OperatorKO7.FBIGenericAdequacy.fbi_directional_coverage direction method h

/-- Forward-indexed coverage that consumes its instantiation premise. -/
theorem fbi_forward_directional_coverage (method : FBIMethod)
    (h : method.instantiation = .forwardOnly) :
    (fbiDirectionalRow method).1 = FBIInstantiation.forwardOnly ∧
      FBIDirection.forward ∈ (fbiDirectionalRow method).1.directions ∧
      FBIFinalCoverage method :=
  OperatorKO7.FBIGenericAdequacy.fbi_forward_directional_coverage method h

/-- Backward-indexed coverage that consumes its instantiation premise. -/
theorem fbi_backward_directional_coverage (method : FBIMethod)
    (h : method.instantiation = .backwardOnly) :
    (fbiDirectionalRow method).1 = FBIInstantiation.backwardOnly ∧
      FBIDirection.backward ∈ (fbiDirectionalRow method).1.directions ∧
      FBIFinalCoverage method :=
  OperatorKO7.FBIGenericAdequacy.fbi_backward_directional_coverage method h

/-- Stable API alias for the external tool status vocabulary. -/
abbrev FBIExternalToolStatus : Type :=
  OperatorKO7.FBIClassification.FBIExternalToolStatus

/-- **The external TTT2 FBI strategy run remains MAYBE.** The internal direction-indexed catalog
classifies the internal `FBIMethod` carrier only; it does not upgrade any external tool result. -/
theorem fbi_external_ttt2_status_is_maybe :
    OperatorKO7.FBIClassification.fbiExternalTTT2Status = .maybe :=
  OperatorKO7.FBIClassification.fbi_external_ttt2_status_is_maybe

/-- The external TTT2 FBI row is not a certified success. -/
theorem fbi_external_ttt2_status_ne_certifiedYes :
    OperatorKO7.FBIClassification.fbiExternalTTT2Status ≠ .certifiedYes :=
  OperatorKO7.FBIClassification.fbi_external_ttt2_status_ne_certifiedYes

/-- Paper-facing certificate for the direction-indexed catalog: twelve rows, duplicate-free,
complete, totally assigned, legacy-projecting, and leaving the external tool status at MAYBE. -/
structure FBIDirectionalCatalogCertificate : Prop where
  /-- The catalog has exactly twelve rows. -/
  rowCount : fbiDirectionalRouteRows.length = 12
  /-- The rows are pairwise distinct. -/
  nodup : fbiDirectionalRouteRows.Nodup
  /-- Every row occurs. -/
  complete : ∀ row : FBIDirectionalRouteRow, row ∈ fbiDirectionalRouteRows
  /-- The assignment is total and legacy-projecting. -/
  totalAssignment : FBIDirectionalRouteStatusCatalog
  /-- The external tool status is unchanged. -/
  externalStillMaybe : OperatorKO7.FBIClassification.fbiExternalTTT2Status = .maybe

/-- The direction-indexed catalog certificate is fully theorem-backed. -/
theorem fbi_directional_catalog_certificate : FBIDirectionalCatalogCertificate where
  rowCount := fbiDirectionalRouteRows_length
  nodup := fbiDirectionalRouteRows_nodup
  complete := fbiDirectionalRouteRows_complete
  totalAssignment := fbi_directional_route_status_catalog
  externalStillMaybe := fbi_external_ttt2_status_is_maybe

attribute [deprecated fbi_directional_coverage_indexed (since := "2026-08-08")]
  fbi_final_catalog_certificate_projects_direction_universal

end OperatorKO7.FBIFinalCatalog
