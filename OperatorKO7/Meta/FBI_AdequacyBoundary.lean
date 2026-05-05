import OperatorKO7.Meta.FBI_GenericAdequacy

/-!
# FBI Adequacy Boundary

This module packages the exact forward and backward adequacy fragments proved
from the current FBI method carrier together with the universal generic FBI
adequacy closure that the closed grammar supports. Each direction retains a
named boundary object, and the module re-exports the universal coverage
theorems into the existing final FBI route/status catalog.
-/

namespace OperatorKO7.FBIAdequacyBoundary

open OperatorKO7.FBIClassification
open OperatorKO7.FBIGenericAdequacy

/-- Final-catalog coverage for a single FBI method. -/
abbrev FBIFinalCoverage (method : FBIMethod) : Prop :=
  OperatorKO7.FBIGenericAdequacy.FBIFinalCoverage method

/-- Stable adequacy-boundary alias for the generic forward adequacy class. -/
abbrev FBIGenericForwardAdequacyClass : FBIMethod → Prop :=
  OperatorKO7.FBIGenericAdequacy.FBIGenericForwardAdequacyClass

/-- Stable adequacy-boundary alias for the generic backward adequacy class. -/
abbrev FBIGenericBackwardAdequacyClass : FBIMethod → Prop :=
  OperatorKO7.FBIGenericAdequacy.FBIGenericBackwardAdequacyClass

/-- Exact forward-only adequacy data currently realized at the FBI layer. -/
structure FBIGenericForwardAdequacyData where
  method : FBIMethod
  forwardOnly : method.instantiation = .forwardOnly
  coveredRow : FBIFinalCatalogRow
  coveredRow_mem : coveredRow ∈ fbiFinalCatalogRows
  route_exact : method.successSemantics.route? = fbiFinalCatalogRoute? coveredRow
  status_exact : method.successSemantics.closureStatus = fbiFinalCatalogStatus coveredRow

/-- Exact backward-only adequacy data currently realized at the FBI layer. -/
structure FBIGenericBackwardAdequacyData where
  method : FBIMethod
  backwardOnly : method.instantiation = .backwardOnly
  coveredRow : FBIFinalCatalogRow
  coveredRow_mem : coveredRow ∈ fbiFinalCatalogRows
  route_exact : method.successSemantics.route? = fbiFinalCatalogRoute? coveredRow
  status_exact : method.successSemantics.closureStatus = fbiFinalCatalogStatus coveredRow

/-- The direct forward FBI method gives one exact forward adequacy fragment. -/
def canonicalForwardAdequacyData : FBIGenericForwardAdequacyData where
  method := directForwardFBIMethod
  forwardOnly := rfl
  coveredRow := .directW0Reduction
  coveredRow_mem := by
    simp [fbiFinalCatalogRows]
  route_exact := rfl
  status_exact := rfl

/-- The imported-whole FBI method gives one exact backward adequacy fragment. -/
def canonicalBackwardAdequacyData : FBIGenericBackwardAdequacyData where
  method := importedWholeFBIMethod
  backwardOnly := rfl
  coveredRow := .constructionW1LicensedEscape
  coveredRow_mem := by
    simp [fbiFinalCatalogRows]
  route_exact := rfl
  status_exact := rfl

/-- Any forward adequacy datum projects to exact final-catalog coverage. -/
theorem fbi_forward_adequacy_data_projects_final_coverage
    (data : FBIGenericForwardAdequacyData) :
    FBIFinalCoverage data.method := by
  exact ⟨data.coveredRow, data.coveredRow_mem, data.route_exact, data.status_exact⟩

/-- Any backward adequacy datum projects to exact final-catalog coverage. -/
theorem fbi_backward_adequacy_data_projects_final_coverage
    (data : FBIGenericBackwardAdequacyData) :
    FBIFinalCoverage data.method := by
  exact ⟨data.coveredRow, data.coveredRow_mem, data.route_exact, data.status_exact⟩

/-- Any forward adequacy datum lands in the listed FBI closure-status catalog. -/
theorem fbi_forward_adequacy_data_has_listed_closure_status
    (data : FBIGenericForwardAdequacyData) :
    data.method.successSemantics.closureStatus ∈ fbiClosureStatuses := by
  exact data.status_exact ▸ by
    cases data.coveredRow <;> simp [fbiClosureStatuses, fbiFinalCatalogStatus]

/-- Any backward adequacy datum lands in the listed FBI closure-status catalog. -/
theorem fbi_backward_adequacy_data_has_listed_closure_status
    (data : FBIGenericBackwardAdequacyData) :
    data.method.successSemantics.closureStatus ∈ fbiClosureStatuses := by
  exact data.status_exact ▸ by
    cases data.coveredRow <;> simp [fbiClosureStatuses, fbiFinalCatalogStatus]

/-- Under exact forward adequacy data, the FBI method has one existing listed
status and no new status constructor is introduced. -/
theorem fbi_forward_adequacy_data_implies_existing_status
    (data : FBIGenericForwardAdequacyData) :
    data.method.successSemantics.closureStatus = .reducedToExistingTheorem .W0
      ∨ data.method.successSemantics.closureStatus = .licensedEscape .W1
      ∨ data.method.successSemantics.closureStatus = .licensedEscape .W2
      ∨ data.method.successSemantics.closureStatus = .certifiedSuccess := by
  exact (fbiClosureStatuses_complete_exact data.method.successSemantics.closureStatus).1
    (fbi_forward_adequacy_data_has_listed_closure_status data)

/-- Under exact backward adequacy data, the FBI method has one existing listed
status and no new status constructor is introduced. -/
theorem fbi_backward_adequacy_data_implies_existing_status
    (data : FBIGenericBackwardAdequacyData) :
    data.method.successSemantics.closureStatus = .reducedToExistingTheorem .W0
      ∨ data.method.successSemantics.closureStatus = .licensedEscape .W1
      ∨ data.method.successSemantics.closureStatus = .licensedEscape .W2
      ∨ data.method.successSemantics.closureStatus = .certifiedSuccess := by
  exact (fbiClosureStatuses_complete_exact data.method.successSemantics.closureStatus).1
    (fbi_backward_adequacy_data_has_listed_closure_status data)

/-- Any forward adequacy datum lands on a theorem-backed final FBI row. -/
theorem fbi_forward_adequacy_data_projects_supported_row
    (data : FBIGenericForwardAdequacyData) :
    FBIFinalCatalogRowSupported data.coveredRow :=
  fbi_final_catalog_row_supported data.coveredRow

/-- Any backward adequacy datum lands on a theorem-backed final FBI row. -/
theorem fbi_backward_adequacy_data_projects_supported_row
    (data : FBIGenericBackwardAdequacyData) :
    FBIFinalCatalogRowSupported data.coveredRow :=
  fbi_final_catalog_row_supported data.coveredRow

/-- The canonical forward adequacy fragment closes to the direct W0 row. -/
theorem canonicalForwardAdequacyData_projects_directW0 :
    canonicalForwardAdequacyData.method.successSemantics.route? = some .W0 ∧
      canonicalForwardAdequacyData.method.successSemantics.closureStatus =
        .reducedToExistingTheorem .W0 := by
  exact ⟨rfl, rfl⟩

/-- The canonical backward adequacy fragment closes to the imported-whole W1 row. -/
theorem canonicalBackwardAdequacyData_projects_importedWholeW1 :
    canonicalBackwardAdequacyData.method.successSemantics.route? = some .W1 ∧
      canonicalBackwardAdequacyData.method.successSemantics.closureStatus =
        .licensedEscape .W1 := by
  exact ⟨rfl, rfl⟩

/-- Paper-facing proposition for the exact FBI adequacy boundary: both generic
adequacy rows are closed by named theorem, each direction retains its canonical
fragment witness, and the closed grammar carries universal final-catalog
coverage. -/
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

/-- The exact FBI adequacy boundary is realized by the two closed generic
adequacy rows together with the canonical fragments and universal coverage
theorems. -/
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

/-- The adequacy-boundary catalog projects the exact closure status for each
generic adequacy question. -/
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

/-- The adequacy-boundary catalog projects universal forward FBI coverage. -/
theorem fbi_adequacy_boundary_catalog_projects_forward_universal_coverage
    (h : FBIAdequacyBoundaryCatalog) (method : FBIMethod) :
    FBIGenericForwardAdequacyClass method -> FBIFinalCoverage method := by
  simpa using (h .forwardAdequacy).2.2.2.2 method

/-- The adequacy-boundary catalog projects universal backward FBI coverage. -/
theorem fbi_adequacy_boundary_catalog_projects_backward_universal_coverage
    (h : FBIAdequacyBoundaryCatalog) (method : FBIMethod) :
    FBIGenericBackwardAdequacyClass method -> FBIFinalCoverage method := by
  simpa using (h .backwardAdequacy).2.2.2.2 method

/-- Certificate packaging the exact adequacy-boundary catalog together with the
conditional fragment projections and the universal FBI adequacy theorems. -/
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

/-- The FBI adequacy-boundary certificate is realized by the exact boundary
catalog, the conditional fragment projections, and the universal FBI adequacy
theorems. -/
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

/-- The certificate projects the exact FBI adequacy-boundary catalog. -/
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

/-- The certificate projects universal forward FBI coverage. -/
theorem fbi_adequacy_boundary_certificate_projects_forward_universal_coverage
    (method : FBIMethod) :
    FBIGenericForwardAdequacyClass method -> FBIFinalCoverage method :=
  fbi_adequacy_boundary_certificate.forwardUniversal method

/-- The certificate projects universal backward FBI coverage. -/
theorem fbi_adequacy_boundary_certificate_projects_backward_universal_coverage
    (method : FBIMethod) :
    FBIGenericBackwardAdequacyClass method -> FBIFinalCoverage method :=
  fbi_adequacy_boundary_certificate.backwardUniversal method

/-- The certificate projects the no-outside-catalog FBI theorem. -/
theorem fbi_adequacy_boundary_certificate_projects_no_outside_catalog
    (method : FBIMethod) :
    method.successSemantics.closureStatus ∈ fbiClosureStatuses ∧ FBIFinalCoverage method :=
  fbi_adequacy_boundary_certificate.noOutsideCatalog method

/-- The certificate projects universal FBI adequacy for every matched direction. -/
theorem fbi_adequacy_boundary_certificate_projects_generic_coverage
    (direction : FBIDirection) (method : FBIMethod) :
    method.matchesDirection direction -> FBIFinalCoverage method :=
  fbi_adequacy_boundary_certificate.genericUniversal direction method

/-- Universal forward FBI adequacy closes unconditionally on the closed grammar. -/
theorem fbi_generic_forward_adequacy_universal_unconditional
    (method : FBIMethod) (h : FBIGenericForwardAdequacyClass method) :
    FBIFinalCoverage method :=
  OperatorKO7.FBIGenericAdequacy.fbi_generic_forward_adequacy_universal_unconditional method h

/-- Universal backward FBI adequacy closes unconditionally on the closed grammar. -/
theorem fbi_generic_backward_adequacy_universal_unconditional
    (method : FBIMethod) (h : FBIGenericBackwardAdequacyClass method) :
    FBIFinalCoverage method :=
  OperatorKO7.FBIGenericAdequacy.fbi_generic_backward_adequacy_universal_unconditional method h

/-- No FBI method sits outside the theorem-backed final FBI catalog. -/
theorem fbi_no_outside_catalog_method (method : FBIMethod) :
    method.successSemantics.closureStatus ∈ fbiClosureStatuses ∧
      FBIFinalCoverage method :=
  OperatorKO7.FBIGenericAdequacy.fbi_no_outside_catalog_method method

/-- Universal FBI adequacy closes unconditionally for every matched direction. -/
theorem fbi_generic_adequacy_universal_unconditional
    (direction : FBIDirection) (method : FBIMethod)
    (h : method.matchesDirection direction) :
    FBIFinalCoverage method :=
  OperatorKO7.FBIGenericAdequacy.fbi_generic_adequacy_universal_unconditional direction method h

end OperatorKO7.FBIAdequacyBoundary
