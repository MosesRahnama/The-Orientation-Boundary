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

/-- Stable API alias for the residual adequacy boundary left open by the FBI final catalog. -/
abbrev FBIResidualAdequacyBoundaryCatalog : Prop :=
  OperatorKO7.FBIClassification.FBIResidualAdequacyBoundaryCatalog

/-- Stable API entrypoint for the residual adequacy boundary left open by the FBI final catalog. -/
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

/-- Paper-facing list of FBI mathematical questions intentionally left open. -/
inductive FBIOpenQuestion where
  | genericForwardAdequacy
  | genericBackwardAdequacy
  | genericImpossibility
  | universalNecessity
deriving DecidableEq, Repr

/-- The finite FBI non-claim ledger exposed by this boundary module. -/
def fbiOpenQuestions : List FBIOpenQuestion :=
  [.genericForwardAdequacy,
    .genericBackwardAdequacy,
    .genericImpossibility,
    .universalNecessity]

/-- The FBI non-claim ledger has no duplicates. -/
theorem fbiOpenQuestions_nodup : fbiOpenQuestions.Nodup := by
  decide

/-- The FBI non-claim ledger has exact size four. -/
theorem fbiOpenQuestions_length : fbiOpenQuestions.length = 4 := by
  rfl

/-- Exact membership characterization for the FBI non-claim ledger. -/
theorem fbiOpenQuestions_complete_exact (question : FBIOpenQuestion) :
    question ∈ fbiOpenQuestions ↔
      question = .genericForwardAdequacy
        ∨ question = .genericBackwardAdequacy
        ∨ question = .genericImpossibility
        ∨ question = .universalNecessity := by
  cases question <;> simp [fbiOpenQuestions]

/-- Status ledger for the paper-facing FBI question rows. -/
inductive FBIOpenQuestionStatus where
  | open
  | closedByNamedTheorem (theoremName : String)
deriving DecidableEq, Repr

/-- Verbatim theorem name closing the generic FBI impossibility row. -/
def fbiGenericImpossibilityClosureTheorem : String :=
  "fbi_no_outside_catalog_method"

/-- Exact status carried by each FBI question row in the final catalog wrapper. -/
def fbiOpenQuestionStatus : FBIOpenQuestion → FBIOpenQuestionStatus
  | .genericForwardAdequacy =>
      .closedByNamedTheorem OperatorKO7.FBIClassification.fbiGenericForwardAdequacyClosureTheorem
  | .genericBackwardAdequacy =>
      .closedByNamedTheorem OperatorKO7.FBIClassification.fbiGenericBackwardAdequacyClosureTheorem
  | .genericImpossibility => .closedByNamedTheorem fbiGenericImpossibilityClosureTheorem
  | .universalNecessity => .open

/-- Paper-facing package of the FBI question-status ledger after generic adequacy closes. -/
abbrev FBINonClaimCatalog : Prop :=
  fbiOpenQuestionStatus .genericForwardAdequacy =
      .closedByNamedTheorem OperatorKO7.FBIClassification.fbiGenericForwardAdequacyClosureTheorem
    ∧ fbiOpenQuestionStatus .genericBackwardAdequacy =
        .closedByNamedTheorem OperatorKO7.FBIClassification.fbiGenericBackwardAdequacyClosureTheorem
    ∧ fbiOpenQuestionStatus .genericImpossibility =
        .closedByNamedTheorem fbiGenericImpossibilityClosureTheorem
    ∧ fbiOpenQuestionStatus .universalNecessity = .open
    ∧ FBIOpenQuestion.genericForwardAdequacy ∈ fbiOpenQuestions
    ∧ FBIOpenQuestion.genericBackwardAdequacy ∈ fbiOpenQuestions
    ∧ FBIOpenQuestion.genericImpossibility ∈ fbiOpenQuestions
    ∧ FBIOpenQuestion.universalNecessity ∈ fbiOpenQuestions

/-- The thin FBI wrapper makes the post-Lane-F question ledger explicit. -/
theorem fbi_non_claim_catalog : FBINonClaimCatalog := by
  simp [FBINonClaimCatalog, fbiOpenQuestions, fbiOpenQuestionStatus,
    OperatorKO7.FBIClassification.fbiGenericForwardAdequacyClosureTheorem,
    OperatorKO7.FBIClassification.fbiGenericBackwardAdequacyClosureTheorem,
    fbiGenericImpossibilityClosureTheorem]

/-- The generic-forward question row is closed by the universal forward adequacy theorem. -/
theorem fbi_non_claim_genericForward_projects_adequacy_boundary :
    FBIOpenQuestion.genericForwardAdequacy ∈ fbiOpenQuestions ∧
      fbiOpenQuestionStatus .genericForwardAdequacy =
        .closedByNamedTheorem OperatorKO7.FBIClassification.fbiGenericForwardAdequacyClosureTheorem ∧
      (∀ method : FBIMethod,
        OperatorKO7.FBIAdequacyBoundary.FBIGenericForwardAdequacyClass method ->
          FBIFinalCoverage method) := by
  exact ⟨by simp [fbiOpenQuestions],
    by simp [fbiOpenQuestionStatus,
      OperatorKO7.FBIClassification.fbiGenericForwardAdequacyClosureTheorem],
    OperatorKO7.FBIAdequacyBoundary.fbi_generic_forward_adequacy_universal_unconditional⟩

/-- The generic-backward question row is closed by the universal backward adequacy theorem. -/
theorem fbi_non_claim_genericBackward_projects_adequacy_boundary :
    FBIOpenQuestion.genericBackwardAdequacy ∈ fbiOpenQuestions ∧
      fbiOpenQuestionStatus .genericBackwardAdequacy =
        .closedByNamedTheorem OperatorKO7.FBIClassification.fbiGenericBackwardAdequacyClosureTheorem ∧
      (∀ method : FBIMethod,
        OperatorKO7.FBIAdequacyBoundary.FBIGenericBackwardAdequacyClass method ->
          FBIFinalCoverage method) := by
  exact ⟨by simp [fbiOpenQuestions],
    by simp [fbiOpenQuestionStatus,
      OperatorKO7.FBIClassification.fbiGenericBackwardAdequacyClosureTheorem],
    OperatorKO7.FBIAdequacyBoundary.fbi_generic_backward_adequacy_universal_unconditional⟩

/-- The generic-impossibility row is closed by the no-outside-catalog theorem. -/
theorem fbi_non_claim_genericImpossibility_projects_no_outside_catalog_method :
    FBIOpenQuestion.genericImpossibility ∈ fbiOpenQuestions ∧
      fbiOpenQuestionStatus .genericImpossibility =
        .closedByNamedTheorem fbiGenericImpossibilityClosureTheorem ∧
      (∀ method : FBIMethod,
        method.successSemantics.closureStatus ∈ OperatorKO7.FBIClassification.fbiClosureStatuses ∧
          FBIFinalCoverage method) := by
  exact ⟨by simp [fbiOpenQuestions],
    by simp [fbiOpenQuestionStatus, fbiGenericImpossibilityClosureTheorem],
    OperatorKO7.FBIAdequacyBoundary.fbi_no_outside_catalog_method⟩

/-- The explicit FBI non-claim ledger projects to the exact adequacy-boundary catalog. -/
theorem fbi_non_claim_catalog_projects_adequacy_boundary :
    FBIAdequacyBoundaryCatalog :=
  fbi_adequacy_boundary_catalog

/-- Paper-facing certificate for the FBI final-catalog import boundary. -/
structure FBIFinalCatalogCertificate where
  routeStatusCatalog : FBIFinalRouteStatusCatalog
  residualAdequacyBoundary : FBIResidualAdequacyBoundaryCatalog
  nonClaimCatalog : FBINonClaimCatalog
  noOutsideCatalog : ∀ method : FBIMethod,
    method.successSemantics.closureStatus ∈ OperatorKO7.FBIClassification.fbiClosureStatuses ∧
      FBIFinalCoverage method

/-- The FBI import boundary packages the theorem-backed catalog and the explicit non-claims. -/
theorem fbi_final_catalog_certificate : FBIFinalCatalogCertificate := by
  exact {
    routeStatusCatalog := fbi_final_route_status_catalog
    residualAdequacyBoundary := fbi_residual_adequacy_boundary_catalog
    nonClaimCatalog := fbi_non_claim_catalog
    noOutsideCatalog := OperatorKO7.FBIAdequacyBoundary.fbi_no_outside_catalog_method
  }

/-- The certificate projects the theorem-backed FBI route/status catalog. -/
theorem fbi_final_catalog_certificate_projects_route_status_catalog :
    FBIFinalRouteStatusCatalog :=
  fbi_final_catalog_certificate.routeStatusCatalog

/-- The certificate projects the residual adequacy boundary. -/
theorem fbi_final_catalog_certificate_projects_residual_boundary :
    FBIResidualAdequacyBoundaryCatalog :=
  fbi_final_catalog_certificate.residualAdequacyBoundary

/-- The certificate projects the explicit FBI non-claim ledger. -/
theorem fbi_final_catalog_certificate_projects_non_claim_catalog :
    FBINonClaimCatalog :=
  fbi_final_catalog_certificate.nonClaimCatalog

/-- The certificate projects the no-outside-catalog FBI theorem. -/
theorem fbi_final_catalog_certificate_projects_no_outside_catalog_method
    (method : FBIMethod) :
    method.successSemantics.closureStatus ∈ OperatorKO7.FBIClassification.fbiClosureStatuses ∧
      FBIFinalCoverage method :=
  fbi_final_catalog_certificate.noOutsideCatalog method

end OperatorKO7.FBIFinalCatalog
