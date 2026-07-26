import OperatorKO7.Meta.FBI_AdequacyBoundary

/-!
# FBI Final Catalog Boundary

This module provides a thin import boundary for the theorem-backed FBI final
catalog. It re-exports the compact route/status and residual-boundary surfaces
without requiring downstream users to depend directly on the full FBI
classification namespace.
-/

namespace OperatorKO7.FBIFinalCatalog

/-- Stable API alias for exact final-catalog coverage coming from adequacy data. -/
abbrev FBIFinalCoverage (method : FBIMethod) : Prop :=
  OperatorKO7.FBIAdequacyBoundary.FBIFinalCoverage method

/-- Stable API alias for the exact forward adequacy datum type. -/
abbrev FBIGenericForwardAdequacyData : Type :=
  OperatorKO7.FBIAdequacyBoundary.FBIGenericForwardAdequacyData

/-- Stable API alias for the exact backward adequacy datum type. -/
abbrev FBIGenericBackwardAdequacyData : Type :=
  OperatorKO7.FBIAdequacyBoundary.FBIGenericBackwardAdequacyData

/-- Stable API alias for the exact canonical forward adequacy fragment. -/
abbrev canonicalForwardAdequacyData : FBIGenericForwardAdequacyData :=
  OperatorKO7.FBIAdequacyBoundary.canonicalForwardAdequacyData

/-- Stable API alias for the exact canonical backward adequacy fragment. -/
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
      exact OperatorKO7.FBIAdequacyBoundary.fbi_generic_forward_adequacy_universal_unconditional
  | genericBackwardAdequacy =>
      exact OperatorKO7.FBIAdequacyBoundary.fbi_generic_backward_adequacy_universal_unconditional
  | completeMethodCoverage =>
      exact OperatorKO7.FBIAdequacyBoundary.fbi_no_outside_catalog_method
  | directionParametricCoverage =>
      exact OperatorKO7.FBIAdequacyBoundary.fbi_generic_adequacy_universal_unconditional

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
    directionUniversal :=
      OperatorKO7.FBIAdequacyBoundary.fbi_generic_adequacy_universal_unconditional
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

/-- The certificate projects direction-parametric FBI coverage. -/
theorem fbi_final_catalog_certificate_projects_direction_universal
    (direction : FBIDirection) (method : FBIMethod) :
    method.matchesDirection direction → FBIFinalCoverage method :=
  fbi_final_catalog_certificate.directionUniversal direction method

end OperatorKO7.FBIFinalCatalog
