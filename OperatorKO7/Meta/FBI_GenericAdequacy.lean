import OperatorKO7.Meta.FBI_Classification

namespace OperatorKO7.FBIGenericAdequacy

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogCertificate
open OperatorKO7.FBIClassification
open OperatorKO7.TransformedCallClassification

/-- Final-catalog coverage for a single FBI method. -/
abbrev FBIFinalCoverage (method : FBIMethod) : Prop :=
  ∃ row : FBIFinalCatalogRow,
    row ∈ fbiFinalCatalogRows ∧
      method.successSemantics.route? = fbiFinalCatalogRoute? row ∧
      method.successSemantics.closureStatus = fbiFinalCatalogStatus row

/-- Closed grammar of admissible FBI comparison witnesses. -/
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

/-- Every FBI comparison witness in the current carrier lies in the closed grammar. -/
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

/-- Generic forward FBI adequacy class from the closed admissible grammar. -/
abbrev FBIGenericForwardAdequacyClass (method : FBIMethod) : Prop :=
  method.instantiation = .forwardOnly ∧
    FBIAdmissibleComparisonWitness method.comparisonWitness

/-- Generic backward FBI adequacy class from the closed admissible grammar. -/
abbrev FBIGenericBackwardAdequacyClass (method : FBIMethod) : Prop :=
  method.instantiation = .backwardOnly ∧
    FBIAdmissibleComparisonWitness method.comparisonWitness

/-- Any FBI method lies on one of the theorem-backed final FBI catalog rows. -/
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

/-- Every forward-only FBI method in the closed grammar is covered by the final catalog. -/
theorem fbi_generic_forward_adequacy_universal_unconditional
    (method : FBIMethod) (_h : FBIGenericForwardAdequacyClass method) :
    FBIFinalCoverage method :=
  (fbi_no_outside_catalog_method method).2

/-- Every backward-only FBI method in the closed grammar is covered by the final catalog. -/
theorem fbi_generic_backward_adequacy_universal_unconditional
    (method : FBIMethod) (_h : FBIGenericBackwardAdequacyClass method) :
    FBIFinalCoverage method :=
  (fbi_no_outside_catalog_method method).2

/-- Every FBI method whose instantiation matches a direction is covered by the final catalog. -/
theorem fbi_generic_adequacy_universal_unconditional
    (direction : FBIDirection) (method : FBIMethod)
    (_h : method.matchesDirection direction) :
    FBIFinalCoverage method :=
  (fbi_no_outside_catalog_method method).2

end OperatorKO7.FBIGenericAdequacy
