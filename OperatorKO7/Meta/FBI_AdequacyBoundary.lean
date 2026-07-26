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
          fbi_generic_forward_adequacy_universal_unconditional⟩⟩
  | backwardAdequacy =>
      exact ⟨by simp [fbiGenericAdequacyBoundaries],
        rfl,
        by simp [fbiGenericAdequacyBoundaryStatus,
          fbiGenericBackwardAdequacyClosureTheorem],
        ⟨⟨canonicalBackwardAdequacyData⟩,
          fbi_generic_backward_adequacy_universal_unconditional⟩⟩

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
    forwardUniversal := fbi_generic_forward_adequacy_universal_unconditional
    backwardUniversal := fbi_generic_backward_adequacy_universal_unconditional
    noOutsideCatalog := fbi_no_outside_catalog_method
    genericUniversal := fbi_generic_adequacy_universal_unconditional
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

/-- Re-export forward closed-grammar catalog coverage. -/
theorem fbi_generic_forward_adequacy_universal_unconditional
    (method : FBIMethod) (h : FBIGenericForwardAdequacyClass method) :
    FBIFinalCoverage method :=
  OperatorKO7.FBIGenericAdequacy.fbi_generic_forward_adequacy_universal_unconditional method h

/-- Re-export backward closed-grammar catalog coverage. -/
theorem fbi_generic_backward_adequacy_universal_unconditional
    (method : FBIMethod) (h : FBIGenericBackwardAdequacyClass method) :
    FBIFinalCoverage method :=
  OperatorKO7.FBIGenericAdequacy.fbi_generic_backward_adequacy_universal_unconditional method h

/-- Re-export constructor-to-catalog coverage for `FBIMethod`. -/
theorem fbi_no_outside_catalog_method (method : FBIMethod) :
    method.successSemantics.closureStatus ∈ fbiClosureStatuses ∧
      FBIFinalCoverage method :=
  OperatorKO7.FBIGenericAdequacy.fbi_no_outside_catalog_method method

/-- Re-export catalog coverage under a direction-membership premise. -/
theorem fbi_generic_adequacy_universal_unconditional
    (direction : FBIDirection) (method : FBIMethod)
    (h : method.matchesDirection direction) :
    FBIFinalCoverage method :=
  OperatorKO7.FBIGenericAdequacy.fbi_generic_adequacy_universal_unconditional direction method h

end OperatorKO7.FBIAdequacyBoundary
