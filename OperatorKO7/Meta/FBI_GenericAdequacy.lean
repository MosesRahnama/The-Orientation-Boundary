import OperatorKO7.Meta.FBI_Classification

namespace OperatorKO7.FBIGenericAdequacy

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogCertificate
open OperatorKO7.FBIClassification
open OperatorKO7.TransformedCallClassification

/-!
# FBI constructor and catalog coverage

`FBIAdmissibleComparisonWitness` mirrors the constructors of
`FBIComparisonWitness`, so `fbi_admissible_comparison_witness` is exhaustive by
case analysis on that closed datatype. `fbi_no_outside_catalog_method` maps
each comparison-witness constructor to a declared final-catalog row. The three
generic-adequacy declarations reuse that catalog coverage and do not use their
direction-specific hypotheses. Their formal
content is closed-grammar catalog coverage rather than an independent semantic
adequacy criterion.
-/

/-- Existence of a declared catalog row matching the method's route and closure-status fields. -/
abbrev FBIFinalCoverage (method : FBIMethod) : Prop :=
  ∃ row : FBIFinalCatalogRow,
    row ∈ fbiFinalCatalogRows ∧
      method.successSemantics.route? = fbiFinalCatalogRoute? row ∧
      method.successSemantics.closureStatus = fbiFinalCatalogStatus row

/-- Constructor-by-constructor predicate mirroring `FBIComparisonWitness`. -/
inductive FBIAdmissibleComparisonWitness : FBIComparisonWitness → Prop where
  | directWholeTermComparison :
      FBIAdmissibleComparisonWitness .directWholeTermComparison
  | transformedCallEvidence
      (witness : CanonicalConstructionWitness)
      (transformClass : W2TransformClass)
      (route_is_w2 : canonicalWitnessRoute witness = .W2)
      (transform_matches : canonicalWitnessW2TransformClass? witness = some transformClass) :
      FBIAdmissibleComparisonWitness
        (.transformedCallEvidence witness transformClass route_is_w2 transform_matches)
  | constructionImportEvidence
      (witness : CanonicalConstructionWitness)
      (importClass : W1ImportClass)
      (route_is_w1 : canonicalWitnessRoute witness = .W1)
      (import_matches : canonicalWitnessW1ImportClass? witness = some importClass) :
      FBIAdmissibleComparisonWitness
        (.constructionImportEvidence witness importClass route_is_w1 import_matches)
  | concreteCertificateEvidence
      (certificate : CanonicalConstructionCertificate) :
      FBIAdmissibleComparisonWitness (.concreteCertificateEvidence certificate)

/-- Each constructor of `FBIComparisonWitness` has the corresponding predicate constructor. -/
theorem fbi_admissible_comparison_witness
    (comparisonWitness : FBIComparisonWitness) :
    FBIAdmissibleComparisonWitness comparisonWitness := by
  cases comparisonWitness with
  | directWholeTermComparison =>
      exact .directWholeTermComparison
  | transformedCallEvidence witness transformClass route_is_w2 transform_matches =>
      exact .transformedCallEvidence witness transformClass route_is_w2 transform_matches
  | constructionImportEvidence witness importClass route_is_w1 import_matches =>
      exact .constructionImportEvidence witness importClass route_is_w1 import_matches
  | concreteCertificateEvidence certificate =>
      exact .concreteCertificateEvidence certificate

/-- Forward-only instantiation paired with the mirrored constructor predicate. -/
abbrev FBIGenericForwardAdequacyClass (method : FBIMethod) : Prop :=
  method.instantiation = .forwardOnly ∧
    FBIAdmissibleComparisonWitness method.comparisonWitness

/-- Backward-only instantiation paired with the mirrored constructor predicate. -/
abbrev FBIGenericBackwardAdequacyClass (method : FBIMethod) : Prop :=
  method.instantiation = .backwardOnly ∧
    FBIAdmissibleComparisonWitness method.comparisonWitness

/-- Each method constructor maps to a declared final-catalog row and listed closure status. -/
theorem fbi_no_outside_catalog_method (method : FBIMethod) :
    method.successSemantics.closureStatus ∈ fbiClosureStatuses ∧
      FBIFinalCoverage method := by
  cases method with
  | mk instantiation comparisonWitness =>
      refine ⟨?_, ?_⟩
      · simpa using
          (fbi_method_has_listed_closure_status
            { instantiation := instantiation, comparisonWitness := comparisonWitness })
      · cases comparisonWitness with
        | directWholeTermComparison =>
            exact ⟨.directW0Reduction, by simp [fbiFinalCatalogRows], rfl, rfl⟩
        | transformedCallEvidence witness transformClass route_is_w2 transform_matches =>
            exact ⟨.transformedCallW2LicensedEscape, by simp [fbiFinalCatalogRows], rfl, rfl⟩
        | constructionImportEvidence witness importClass route_is_w1 import_matches =>
            exact ⟨.constructionW1LicensedEscape, by simp [fbiFinalCatalogRows], rfl, rfl⟩
        | concreteCertificateEvidence certificate =>
            exact ⟨.certifiedSuccess, by simp [fbiFinalCatalogRows], rfl, rfl⟩

/-! ### Deprecated compatibility aliases

The three declarations below are retained only so that existing downstream callers keep compiling.
Each ignores its direction hypothesis (`_h` is unused) and therefore proves nothing about the
direction: the content is `fbi_no_outside_catalog_method` alone, and the name's "adequacy" wording
overstates it. Prefer the direction-indexed replacements in the next section, which consume their
hypotheses and expose the direction in the conclusion. -/

/-- Deprecated compatibility alias. Catalog coverage obtained from
`fbi_no_outside_catalog_method`; `_h` is not used, so this is not a forward-adequacy theorem.
Superseded by `fbi_forward_directional_coverage`. -/
theorem fbi_generic_forward_adequacy_universal_unconditional
    (method : FBIMethod) (_h : FBIGenericForwardAdequacyClass method) :
    FBIFinalCoverage method :=
  (fbi_no_outside_catalog_method method).2

/-- Deprecated compatibility alias. Catalog coverage obtained from
`fbi_no_outside_catalog_method`; `_h` is not used, so this is not a backward-adequacy theorem.
Superseded by `fbi_backward_directional_coverage`. -/
theorem fbi_generic_backward_adequacy_universal_unconditional
    (method : FBIMethod) (_h : FBIGenericBackwardAdequacyClass method) :
    FBIFinalCoverage method :=
  (fbi_no_outside_catalog_method method).2

/-- Deprecated compatibility alias. Catalog coverage obtained from
`fbi_no_outside_catalog_method`; `_h` is not used, so the direction is not reflected in the
conclusion. Superseded by `fbi_directional_coverage`. -/
theorem fbi_generic_adequacy_universal_unconditional
    (direction : FBIDirection) (method : FBIMethod)
    (_h : method.matchesDirection direction) :
    FBIFinalCoverage method :=
  (fbi_no_outside_catalog_method method).2

/-! ### Direction-indexed coverage

Each theorem below consumes its direction hypothesis and exposes the direction in its conclusion. -/

/-- **Forward-indexed coverage.** The instantiation hypothesis is consumed to compute the row's
instantiation component, and the forward direction appears in the conclusion. -/
theorem fbi_forward_directional_coverage (method : FBIMethod)
    (h : method.instantiation = .forwardOnly) :
    (fbiDirectionalRow method).1 = FBIInstantiation.forwardOnly ∧
      FBIDirection.forward ∈ (fbiDirectionalRow method).1.directions ∧
      FBIFinalCoverage method := by
  refine ⟨?_, ?_, (fbi_no_outside_catalog_method method).2⟩
  · rw [fbiDirectionalRow_fst, h]
  · rw [fbiDirectionalRow_fst, h]
    simp [FBIInstantiation.directions]

/-- **Backward-indexed coverage.** The instantiation hypothesis is consumed, and the backward
direction appears in the conclusion. -/
theorem fbi_backward_directional_coverage (method : FBIMethod)
    (h : method.instantiation = .backwardOnly) :
    (fbiDirectionalRow method).1 = FBIInstantiation.backwardOnly ∧
      FBIDirection.backward ∈ (fbiDirectionalRow method).1.directions ∧
      FBIFinalCoverage method := by
  refine ⟨?_, ?_, (fbi_no_outside_catalog_method method).2⟩
  · rw [fbiDirectionalRow_fst, h]
  · rw [fbiDirectionalRow_fst, h]
    simp [FBIInstantiation.directions]

/-- **Direction-parametric indexed coverage.** The direction-membership hypothesis is consumed and
re-exposed against the row's instantiation component. -/
theorem fbi_directional_coverage (direction : FBIDirection) (method : FBIMethod)
    (h : method.matchesDirection direction) :
    direction ∈ (fbiDirectionalRow method).1.directions ∧ FBIFinalCoverage method := by
  refine ⟨?_, (fbi_no_outside_catalog_method method).2⟩
  rw [fbiDirectionalRow_fst]
  exact h

/-- The direction-indexed row of any method is one of the twelve catalog rows, and its catalog
component reproduces the method's route and status tags. -/
theorem fbi_directional_row_classified (method : FBIMethod) :
    fbiDirectionalRow method ∈ fbiDirectionalRouteRows ∧
      method.successSemantics.route? = fbiFinalCatalogRoute? (fbiDirectionalRow method).2 ∧
      method.successSemantics.closureStatus =
        fbiFinalCatalogStatus (fbiDirectionalRow method).2 :=
  ⟨fbiDirectionalRow_mem method,
    (fbiDirectionalRow_legacy_projection method).1,
    (fbiDirectionalRow_legacy_projection method).2⟩

attribute [deprecated fbi_forward_directional_coverage (since := "2026-08-08")]
  fbi_generic_forward_adequacy_universal_unconditional
attribute [deprecated fbi_backward_directional_coverage (since := "2026-08-08")]
  fbi_generic_backward_adequacy_universal_unconditional
attribute [deprecated fbi_directional_coverage (since := "2026-08-08")]
  fbi_generic_adequacy_universal_unconditional

end OperatorKO7.FBIGenericAdequacy
