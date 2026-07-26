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

/-- Catalog coverage obtained from `fbi_no_outside_catalog_method`; `_h` is not used. -/
theorem fbi_generic_forward_adequacy_universal_unconditional
    (method : FBIMethod) (_h : FBIGenericForwardAdequacyClass method) :
    FBIFinalCoverage method :=
  (fbi_no_outside_catalog_method method).2

/-- Catalog coverage obtained from `fbi_no_outside_catalog_method`; `_h` is not used. -/
theorem fbi_generic_backward_adequacy_universal_unconditional
    (method : FBIMethod) (_h : FBIGenericBackwardAdequacyClass method) :
    FBIFinalCoverage method :=
  (fbi_no_outside_catalog_method method).2

/-- Catalog coverage obtained from `fbi_no_outside_catalog_method`; `_h` is not used. -/
theorem fbi_generic_adequacy_universal_unconditional
    (direction : FBIDirection) (method : FBIMethod)
    (_h : method.matchesDirection direction) :
    FBIFinalCoverage method :=
  (fbi_no_outside_catalog_method method).2

end OperatorKO7.FBIGenericAdequacy
