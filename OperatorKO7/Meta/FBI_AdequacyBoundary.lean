import OperatorKO7.Meta.FBI_GenericAdequacy

/-!
# FBI direction-tag and catalog-coverage packages

The forward and backward data structures store an `FBIMethod`, an instantiation-tag equality, and a
declared final-catalog row with route and status equalities. The catalog and certificate declarations
package these fields and the closed-grammar coverage theorems from `FBI_GenericAdequacy`. Their types
establish constructor-to-catalog classification; they do not add an independent semantic adequacy or
orientation predicate.
-/

namespace OperatorKO7.FBIAdequacyBoundary

open OperatorKO7.FBIClassification
open OperatorKO7.FBIGenericAdequacy

/-- Existence of a declared catalog row matching the method's route and status tags. -/
abbrev FBIFinalCoverage (method : FBIMethod) : Prop :=
  OperatorKO7.FBIGenericAdequacy.FBIFinalCoverage method

/-- Alias for the forward-only tag paired with the mirrored witness-constructor predicate. -/
abbrev FBIGenericForwardAdequacyClass : FBIMethod → Prop :=
  OperatorKO7.FBIGenericAdequacy.FBIGenericForwardAdequacyClass

/-- Alias for the backward-only tag paired with the mirrored witness-constructor predicate. -/
abbrev FBIGenericBackwardAdequacyClass : FBIMethod → Prop :=
  OperatorKO7.FBIGenericAdequacy.FBIGenericBackwardAdequacyClass

/-- Forward-only method tag plus a supplied matching catalog row. -/
structure FBIGenericForwardAdequacyData where
  method : FBIMethod
  forwardOnly : method.instantiation = .forwardOnly
  coveredRow : FBIFinalCatalogRow
  coveredRow_mem : coveredRow ∈ fbiFinalCatalogRows
  route_exact : method.successSemantics.route? = fbiFinalCatalogRoute? coveredRow
  status_exact : method.successSemantics.closureStatus = fbiFinalCatalogStatus coveredRow

/-- Backward-only method tag plus a supplied matching catalog row. -/
structure FBIGenericBackwardAdequacyData where
  method : FBIMethod
  backwardOnly : method.instantiation = .backwardOnly
  coveredRow : FBIFinalCatalogRow
  coveredRow_mem : coveredRow ∈ fbiFinalCatalogRows
  route_exact : method.successSemantics.route? = fbiFinalCatalogRoute? coveredRow
  status_exact : method.successSemantics.closureStatus = fbiFinalCatalogStatus coveredRow

/-- Fixture pairing `directForwardFBIMethod` with the direct W0 catalog row. -/
def canonicalForwardAdequacyData : FBIGenericForwardAdequacyData where
  method := directForwardFBIMethod
  forwardOnly := rfl
  coveredRow := .directW0Reduction
  coveredRow_mem := by
    simp [fbiFinalCatalogRows]
  route_exact := rfl
  status_exact := rfl

/-- Fixture pairing `importedWholeFBIMethod` with the construction W1 catalog row. -/
def canonicalBackwardAdequacyData : FBIGenericBackwardAdequacyData where
  method := importedWholeFBIMethod
  backwardOnly := rfl
  coveredRow := .constructionW1LicensedEscape
  coveredRow_mem := by
    simp [fbiFinalCatalogRows]
  route_exact := rfl
  status_exact := rfl

/-- Project catalog coverage from the fields of forward data. -/
theorem fbi_forward_adequacy_data_projects_final_coverage
    (data : FBIGenericForwardAdequacyData) :
    FBIFinalCoverage data.method := by
  exact ⟨data.coveredRow, data.coveredRow_mem, data.route_exact, data.status_exact⟩

/-- Project catalog coverage from the fields of backward data. -/
theorem fbi_backward_adequacy_data_projects_final_coverage
    (data : FBIGenericBackwardAdequacyData) :
    FBIFinalCoverage data.method := by
  exact ⟨data.coveredRow, data.coveredRow_mem, data.route_exact, data.status_exact⟩

/-- A forward datum's stored row gives membership in the closure-status list. -/
theorem fbi_forward_adequacy_data_has_listed_closure_status
    (data : FBIGenericForwardAdequacyData) :
    data.method.successSemantics.closureStatus ∈ fbiClosureStatuses := by
  exact data.status_exact ▸ by
    cases data.coveredRow <;> simp [fbiClosureStatuses, fbiFinalCatalogStatus]

/-- A backward datum's stored row gives membership in the closure-status list. -/
theorem fbi_backward_adequacy_data_has_listed_closure_status
    (data : FBIGenericBackwardAdequacyData) :
    data.method.successSemantics.closureStatus ∈ fbiClosureStatuses := by
  exact data.status_exact ▸ by
    cases data.coveredRow <;> simp [fbiClosureStatuses, fbiFinalCatalogStatus]

/-- Enumerate the four closure-status constructors for a forward datum. -/
theorem fbi_forward_adequacy_data_implies_existing_status
    (data : FBIGenericForwardAdequacyData) :
    data.method.successSemantics.closureStatus = .reducedToExistingTheorem .W0
      ∨ data.method.successSemantics.closureStatus = .licensedEscape .W1
      ∨ data.method.successSemantics.closureStatus = .licensedEscape .W2
      ∨ data.method.successSemantics.closureStatus = .certifiedSuccess := by
  exact (fbiClosureStatuses_complete_exact data.method.successSemantics.closureStatus).1
    (fbi_forward_adequacy_data_has_listed_closure_status data)

/-- Enumerate the four closure-status constructors for a backward datum. -/
theorem fbi_backward_adequacy_data_implies_existing_status
    (data : FBIGenericBackwardAdequacyData) :
    data.method.successSemantics.closureStatus = .reducedToExistingTheorem .W0
      ∨ data.method.successSemantics.closureStatus = .licensedEscape .W1
      ∨ data.method.successSemantics.closureStatus = .licensedEscape .W2
      ∨ data.method.successSemantics.closureStatus = .certifiedSuccess := by
  exact (fbiClosureStatuses_complete_exact data.method.successSemantics.closureStatus).1
    (fbi_backward_adequacy_data_has_listed_closure_status data)

/-- Apply `fbi_final_catalog_row_supported` to a forward datum's stored row. -/
theorem fbi_forward_adequacy_data_projects_supported_row
    (data : FBIGenericForwardAdequacyData) :
    FBIFinalCatalogRowSupported data.coveredRow :=
  fbi_final_catalog_row_supported data.coveredRow

/-- Apply `fbi_final_catalog_row_supported` to a backward datum's stored row. -/
theorem fbi_backward_adequacy_data_projects_supported_row
    (data : FBIGenericBackwardAdequacyData) :
    FBIFinalCatalogRowSupported data.coveredRow :=
  fbi_final_catalog_row_supported data.coveredRow

/-- Compute the route and status tags of `canonicalForwardAdequacyData`. -/
theorem canonicalForwardAdequacyData_projects_directW0 :
    canonicalForwardAdequacyData.method.successSemantics.route? = some .W0 ∧
      canonicalForwardAdequacyData.method.successSemantics.closureStatus =
        .reducedToExistingTheorem .W0 := by
  exact ⟨rfl, rfl⟩

/-- Compute the route and status tags of `canonicalBackwardAdequacyData`. -/
theorem canonicalBackwardAdequacyData_projects_importedWholeW1 :
    canonicalBackwardAdequacyData.method.successSemantics.route? = some .W1 ∧
      canonicalBackwardAdequacyData.method.successSemantics.closureStatus =
        .licensedEscape .W1 := by
  exact ⟨rfl, rfl⟩

/-- Proposition packaging membership and status metadata for both boundary constructors, a fixture
for each direction, and closed-grammar final-catalog coverage. -/
abbrev FBIAdequacyBoundaryCatalog : Prop :=
  ∀ boundary : FBIGenericAdequacyBoundary,
    boundary ∈ fbiGenericAdequacyBoundaries ∧
      (fbiGenericAdequacyBoundaryInstantiation boundary =
        match boundary with
        | .forwardAdequacy => FBIInstantiation.forwardOnly
        | .backwardAdequacy => FBIInstantiation.backwardOnly) ∧
      (fbiGenericAdequacyBoundaryStatus boundary =
        match boundary with
        | .forwardAdequacy => .closedByNamedTheorem fbiGenericForwardAdequacyClosureTheorem
        | .backwardAdequacy => .closedByNamedTheorem fbiGenericBackwardAdequacyClosureTheorem) ∧
      match boundary with
      | .forwardAdequacy =>
          Nonempty FBIGenericForwardAdequacyData ∧
            ∀ method : FBIMethod,
              FBIGenericForwardAdequacyClass method -> FBIFinalCoverage method
      | .backwardAdequacy =>
          Nonempty FBIGenericBackwardAdequacyData ∧
            ∀ method : FBIMethod,
              FBIGenericBackwardAdequacyClass method -> FBIFinalCoverage method

/-- Construct `FBIAdequacyBoundaryCatalog` by cases on its two constructors. -/
theorem fbi_adequacy_boundary_catalog : FBIAdequacyBoundaryCatalog := by
  intro boundary
  cases boundary with
  | forwardAdequacy =>
      exact ⟨by simp [fbiGenericAdequacyBoundaries],
        rfl,
        by simp [fbiGenericAdequacyBoundaryStatus,
          fbiGenericForwardAdequacyClosureTheorem],
        ⟨⟨canonicalForwardAdequacyData⟩,
          fun method h =>
            (OperatorKO7.FBIGenericAdequacy.fbi_forward_directional_coverage
              method h.1).2.2⟩⟩
  | backwardAdequacy =>
      exact ⟨by simp [fbiGenericAdequacyBoundaries],
        rfl,
        by simp [fbiGenericAdequacyBoundaryStatus,
          fbiGenericBackwardAdequacyClosureTheorem],
        ⟨⟨canonicalBackwardAdequacyData⟩,
          fun method h =>
            (OperatorKO7.FBIGenericAdequacy.fbi_backward_directional_coverage
              method h.1).2.2⟩⟩

/-- Project the stored closure-status equality for either boundary constructor. -/
theorem fbi_adequacy_boundary_catalog_projects_status
    (h : FBIAdequacyBoundaryCatalog) (boundary : FBIGenericAdequacyBoundary) :
    fbiGenericAdequacyBoundaryStatus boundary =
      match boundary with
      | .forwardAdequacy => .closedByNamedTheorem fbiGenericForwardAdequacyClosureTheorem
      | .backwardAdequacy => .closedByNamedTheorem fbiGenericBackwardAdequacyClosureTheorem :=
  (h boundary).2.2.1

/-- The adequacy-boundary catalog projects a named forward adequacy datum. -/
theorem fbi_adequacy_boundary_catalog_projects_forward_data
    (h : FBIAdequacyBoundaryCatalog) :
    Nonempty FBIGenericForwardAdequacyData := by
  simpa using (h .forwardAdequacy).2.2.2.1

/-- The adequacy-boundary catalog projects a named backward adequacy datum. -/
theorem fbi_adequacy_boundary_catalog_projects_backward_data
    (h : FBIAdequacyBoundaryCatalog) :
    Nonempty FBIGenericBackwardAdequacyData := by
  simpa using (h .backwardAdequacy).2.2.2.1

/-- Project forward closed-grammar catalog coverage. -/
theorem fbi_adequacy_boundary_catalog_projects_forward_universal_coverage
    (h : FBIAdequacyBoundaryCatalog) (method : FBIMethod) :
    FBIGenericForwardAdequacyClass method -> FBIFinalCoverage method := by
  simpa using (h .forwardAdequacy).2.2.2.2 method

/-- Project backward closed-grammar catalog coverage. -/
theorem fbi_adequacy_boundary_catalog_projects_backward_universal_coverage
    (h : FBIAdequacyBoundaryCatalog) (method : FBIMethod) :
    FBIGenericBackwardAdequacyClass method -> FBIFinalCoverage method := by
  simpa using (h .backwardAdequacy).2.2.2.2 method

/-- Record packaging the catalog proposition and constructor-to-catalog coverage functions. -/
structure FBIAdequacyBoundaryCertificate where
  catalog : FBIAdequacyBoundaryCatalog
  forwardCoverage : ∀ data : FBIGenericForwardAdequacyData, FBIFinalCoverage data.method
  backwardCoverage : ∀ data : FBIGenericBackwardAdequacyData, FBIFinalCoverage data.method
  forwardUniversal : ∀ method : FBIMethod,
    FBIGenericForwardAdequacyClass method -> FBIFinalCoverage method
  backwardUniversal : ∀ method : FBIMethod,
    FBIGenericBackwardAdequacyClass method -> FBIFinalCoverage method
  noOutsideCatalog : ∀ method : FBIMethod,
    method.successSemantics.closureStatus ∈ fbiClosureStatuses ∧ FBIFinalCoverage method
  genericUniversal : ∀ direction : FBIDirection,
    ∀ method : FBIMethod,
      method.matchesDirection direction -> FBIFinalCoverage method

/-- Populate `FBIAdequacyBoundaryCertificate` from the catalog-classification theorems. -/
theorem fbi_adequacy_boundary_certificate : FBIAdequacyBoundaryCertificate := by
  exact {
    catalog := fbi_adequacy_boundary_catalog
    forwardCoverage := fbi_forward_adequacy_data_projects_final_coverage
    backwardCoverage := fbi_backward_adequacy_data_projects_final_coverage
    forwardUniversal := fun method h =>
      (OperatorKO7.FBIGenericAdequacy.fbi_forward_directional_coverage method h.1).2.2
    backwardUniversal := fun method h =>
      (OperatorKO7.FBIGenericAdequacy.fbi_backward_directional_coverage method h.1).2.2
    noOutsideCatalog := fbi_no_outside_catalog_method
    genericUniversal := fun direction method h =>
      (OperatorKO7.FBIGenericAdequacy.fbi_directional_coverage direction method h).2
  }

/-- Project the catalog field of `fbi_adequacy_boundary_certificate`. -/
theorem fbi_adequacy_boundary_certificate_projects_catalog :
    FBIAdequacyBoundaryCatalog :=
  fbi_adequacy_boundary_certificate.catalog

/-- The certificate projects conditional forward final-catalog coverage. -/
theorem fbi_adequacy_boundary_certificate_projects_forward_coverage
    (data : FBIGenericForwardAdequacyData) :
    FBIFinalCoverage data.method :=
  fbi_adequacy_boundary_certificate.forwardCoverage data

/-- The certificate projects conditional backward final-catalog coverage. -/
theorem fbi_adequacy_boundary_certificate_projects_backward_coverage
    (data : FBIGenericBackwardAdequacyData) :
    FBIFinalCoverage data.method :=
  fbi_adequacy_boundary_certificate.backwardCoverage data

/-- Project forward closed-grammar catalog coverage from the certificate. -/
theorem fbi_adequacy_boundary_certificate_projects_forward_universal_coverage
    (method : FBIMethod) :
    FBIGenericForwardAdequacyClass method -> FBIFinalCoverage method :=
  fbi_adequacy_boundary_certificate.forwardUniversal method

/-- Project backward closed-grammar catalog coverage from the certificate. -/
theorem fbi_adequacy_boundary_certificate_projects_backward_universal_coverage
    (method : FBIMethod) :
    FBIGenericBackwardAdequacyClass method -> FBIFinalCoverage method :=
  fbi_adequacy_boundary_certificate.backwardUniversal method

/-- Project constructor-to-catalog coverage from the certificate. -/
theorem fbi_adequacy_boundary_certificate_projects_no_outside_catalog
    (method : FBIMethod) :
    method.successSemantics.closureStatus ∈ fbiClosureStatuses ∧ FBIFinalCoverage method :=
  fbi_adequacy_boundary_certificate.noOutsideCatalog method

/-- Project catalog coverage for a method carrying the supplied direction-membership premise. -/
theorem fbi_adequacy_boundary_certificate_projects_generic_coverage
    (direction : FBIDirection) (method : FBIMethod) :
    method.matchesDirection direction -> FBIFinalCoverage method :=
  fbi_adequacy_boundary_certificate.genericUniversal direction method

/-- Deprecated compatibility re-export. The conclusion omits the consumed forward direction;
prefer `OperatorKO7.FBIGenericAdequacy.fbi_forward_directional_coverage`. -/
theorem fbi_generic_forward_adequacy_universal_unconditional
    (method : FBIMethod) (h : FBIGenericForwardAdequacyClass method) :
    FBIFinalCoverage method :=
  (OperatorKO7.FBIGenericAdequacy.fbi_forward_directional_coverage method h.1).2.2

/-- Deprecated compatibility re-export. The conclusion omits the consumed backward direction;
prefer `OperatorKO7.FBIGenericAdequacy.fbi_backward_directional_coverage`. -/
theorem fbi_generic_backward_adequacy_universal_unconditional
    (method : FBIMethod) (h : FBIGenericBackwardAdequacyClass method) :
    FBIFinalCoverage method :=
  (OperatorKO7.FBIGenericAdequacy.fbi_backward_directional_coverage method h.1).2.2

/-- Re-export constructor-to-catalog coverage for `FBIMethod`. -/
theorem fbi_no_outside_catalog_method (method : FBIMethod) :
    method.successSemantics.closureStatus ∈ fbiClosureStatuses ∧
      FBIFinalCoverage method :=
  OperatorKO7.FBIGenericAdequacy.fbi_no_outside_catalog_method method

/-- Deprecated compatibility re-export. Its proof consumes the direction premise, but the legacy
conclusion erases that direction; use `fbi_directional_coverage` for the indexed statement. -/
theorem fbi_generic_adequacy_universal_unconditional
    (direction : FBIDirection) (method : FBIMethod)
    (h : method.matchesDirection direction) :
    FBIFinalCoverage method :=
  (OperatorKO7.FBIGenericAdequacy.fbi_directional_coverage direction method h).2

/-! ### Direction-indexed route data

Data records for the direction-indexed route/status catalog. These are route/status classification
records; they carry no semantic adequacy or orientation claim. -/

/-- A method together with a direction it explicitly instantiates and the direction-indexed catalog
row it lands in. -/
structure FBIDirectionalRouteData where
  /-- The classified method. -/
  method : FBIMethod
  /-- A direction the method's instantiation mode explicitly carries. -/
  direction : FBIDirection
  /-- Consumed premise: the direction is in the method's instantiation direction list. -/
  direction_matches : method.matchesDirection direction
  /-- The direction-indexed row. -/
  row : FBIDirectionalRouteRow
  /-- The row is the method's computed row. -/
  row_eq : row = fbiDirectionalRow method
  /-- The row is one of the twelve. -/
  row_mem : row ∈ fbiDirectionalRouteRows

/-- Forward fixture: the direct whole-term method under the forward direction. -/
def canonicalForwardDirectionalData : FBIDirectionalRouteData where
  method := directForwardFBIMethod
  direction := .forward
  direction_matches := by
    simp [FBIMethod.matchesDirection, FBIInstantiation.matchesDirection,
      FBIInstantiation.directions, directForwardFBIMethod]
  row := fbiDirectionalRow directForwardFBIMethod
  row_eq := rfl
  row_mem := fbiDirectionalRow_mem _

/-- Backward fixture: the imported-whole method under the backward direction. -/
def canonicalBackwardDirectionalData : FBIDirectionalRouteData where
  method := importedWholeFBIMethod
  direction := .backward
  direction_matches := by
    simp [FBIMethod.matchesDirection, FBIInstantiation.matchesDirection,
      FBIInstantiation.directions, importedWholeFBIMethod]
  row := fbiDirectionalRow importedWholeFBIMethod
  row_eq := rfl
  row_mem := fbiDirectionalRow_mem _

/-- A directional datum's stored direction is carried by its row's instantiation component, and the
method is covered by the final catalog. The stored premise is consumed. -/
theorem fbi_directional_data_projects_coverage (data : FBIDirectionalRouteData) :
    data.direction ∈ (fbiDirectionalRow data.method).1.directions ∧
      FBIFinalCoverage data.method :=
  OperatorKO7.FBIGenericAdequacy.fbi_directional_coverage data.direction data.method
    data.direction_matches

/-- A directional datum's row reproduces the method's route and status tags. -/
theorem fbi_directional_data_projects_legacy_tags (data : FBIDirectionalRouteData) :
    data.method.successSemantics.route? = fbiFinalCatalogRoute? data.row.2 ∧
      data.method.successSemantics.closureStatus = fbiFinalCatalogStatus data.row.2 := by
  rw [data.row_eq]
  exact fbiDirectionalRow_legacy_projection data.method

/-- Re-export of the twelve-row direction-indexed route/status catalog. -/
theorem fbi_directional_route_status_catalog :
    OperatorKO7.FBIClassification.FBIDirectionalRouteStatusCatalog :=
  OperatorKO7.FBIClassification.fbi_directional_route_status_catalog

/-- Re-export: the external TTT2 FBI strategy run remains a search non-success. -/
theorem fbi_external_ttt2_status_is_maybe :
    OperatorKO7.FBIClassification.fbiExternalTTT2Status = .maybe :=
  OperatorKO7.FBIClassification.fbi_external_ttt2_status_is_maybe

attribute [deprecated OperatorKO7.FBIGenericAdequacy.fbi_forward_directional_coverage
    (since := "2026-08-08")]
  fbi_generic_forward_adequacy_universal_unconditional
attribute [deprecated OperatorKO7.FBIGenericAdequacy.fbi_backward_directional_coverage
    (since := "2026-08-08")]
  fbi_generic_backward_adequacy_universal_unconditional
attribute [deprecated OperatorKO7.FBIGenericAdequacy.fbi_directional_coverage
    (since := "2026-08-08")]
  fbi_generic_adequacy_universal_unconditional

end OperatorKO7.FBIAdequacyBoundary
