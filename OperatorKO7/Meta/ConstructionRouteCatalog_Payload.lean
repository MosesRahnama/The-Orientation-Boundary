import OperatorKO7.Meta.ConstructionRouteCatalog

namespace OperatorKO7.ConstructionRouteCatalogPayload

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.TransformedCallClassification
open OperatorKO7.BenchmarkedPRCFamily

def canonicalWitnessW1Success? : CanonicalConstructionWitness → Option W1ConstructionSuccess
  | .w1MPO => some mpo_w1_success
  | .w1Polynomial => some poly_w1_success
  | .w1ImportedWhole => some importedWhole_w1_success
  | .w1Transparency => some transparency_w1_success
  | .w2FullDuplicating => none
  | .w2FullLinear => none

def canonicalWitnessW2Success? : CanonicalConstructionWitness → Option W2ConstructionSuccess
  | .w1MPO => none
  | .w1Polynomial => none
  | .w1ImportedWhole => none
  | .w1Transparency => none
  | .w2FullDuplicating => some fullDuplicating_w2_success
  | .w2FullLinear => some fullLinear_w2_success

def CanonicalW1SuccessPayloadCatalog : Prop :=
  (canonicalWitnessW1Success? .w1MPO = some mpo_w1_success ∧
    canonicalWitnessRoute .w1MPO = mpo_w1_success.route ∧
    canonicalWitnessW1ImportClass? .w1MPO = some mpo_w1_success.importClass ∧
    PermittedW1Import mpo_w1_success.importClass ∧
    mpo_w1_success.route ≠ .W0) ∧
  (canonicalWitnessW1Success? .w1Polynomial = some poly_w1_success ∧
    canonicalWitnessRoute .w1Polynomial = poly_w1_success.route ∧
    canonicalWitnessW1ImportClass? .w1Polynomial = some poly_w1_success.importClass ∧
    PermittedW1Import poly_w1_success.importClass ∧
    poly_w1_success.route ≠ .W0) ∧
  (canonicalWitnessW1Success? .w1ImportedWhole = some importedWhole_w1_success ∧
    canonicalWitnessRoute .w1ImportedWhole = importedWhole_w1_success.route ∧
    canonicalWitnessW1ImportClass? .w1ImportedWhole = some importedWhole_w1_success.importClass ∧
    PermittedW1Import importedWhole_w1_success.importClass ∧
    importedWhole_w1_success.route ≠ .W0) ∧
  (canonicalWitnessW1Success? .w1Transparency = some transparency_w1_success ∧
    canonicalWitnessRoute .w1Transparency = transparency_w1_success.route ∧
    canonicalWitnessW1ImportClass? .w1Transparency = some transparency_w1_success.importClass ∧
    PermittedW1Import transparency_w1_success.importClass ∧
    transparency_w1_success.route ≠ .W0)

def CanonicalW2SuccessPayloadCatalog : Prop :=
  (canonicalWitnessW2Success? .w2FullDuplicating = some fullDuplicating_w2_success ∧
    canonicalWitnessRoute .w2FullDuplicating = fullDuplicating_w2_success.route ∧
    canonicalWitnessW2TransformClass? .w2FullDuplicating =
      some fullDuplicating_w2_success.transformClass ∧
    fullDuplicating_w2_success.target = fullDuplicating ∧
    PermittedW2Transform fullDuplicating_w2_success.transformClass fullDuplicating_w2_success.target ∧
    fullDuplicating_w2_success.route ≠ .W0) ∧
  (canonicalWitnessW2Success? .w2FullLinear = some fullLinear_w2_success ∧
    canonicalWitnessRoute .w2FullLinear = fullLinear_w2_success.route ∧
    canonicalWitnessW2TransformClass? .w2FullLinear = some fullLinear_w2_success.transformClass ∧
    fullLinear_w2_success.target = fullLinear ∧
    PermittedW2Transform fullLinear_w2_success.transformClass fullLinear_w2_success.target ∧
    fullLinear_w2_success.route ≠ .W0)

theorem canonical_w1_success_payload_catalog : CanonicalW1SuccessPayloadCatalog := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · simpa [mpo_w1_success] using mpo_w1_success_requires_precedence_import
    · decide
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · simpa [poly_w1_success] using poly_w1_success_requires_global_polynomial_import
    · decide
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · simpa [importedWhole_w1_success] using importedWhole_w1_success_requires_imported_whole
    · decide
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · simpa [transparency_w1_success] using transparency_w1_success_requires_transparency_import
    · decide

theorem canonical_w2_success_payload_catalog : CanonicalW2SuccessPayloadCatalog := by
  refine ⟨?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · simpa [fullDuplicating_w2_success] using
        fullDuplicating_w2_success_requires_ko7_dp_projection
    · decide
  · refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · simpa [fullLinear_w2_success] using fullLinear_w2_success_requires_benchmark_family_transform
    · decide

theorem canonical_route_payload_catalog :
    CanonicalW1SuccessPayloadCatalog ∧ CanonicalW2SuccessPayloadCatalog := by
  exact ⟨canonical_w1_success_payload_catalog, canonical_w2_success_payload_catalog⟩

theorem canonical_w1_payloads_have_permitted_imports :
    PermittedW1Import mpo_w1_success.importClass ∧
      PermittedW1Import poly_w1_success.importClass ∧
      PermittedW1Import importedWhole_w1_success.importClass ∧
      PermittedW1Import transparency_w1_success.importClass := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · simpa [mpo_w1_success] using mpo_w1_success_requires_precedence_import
  · simpa [poly_w1_success] using poly_w1_success_requires_global_polynomial_import
  · simpa [importedWhole_w1_success] using importedWhole_w1_success_requires_imported_whole
  · simpa [transparency_w1_success] using transparency_w1_success_requires_transparency_import

theorem canonical_w2_payloads_have_permitted_transforms :
    PermittedW2Transform fullDuplicating_w2_success.transformClass fullDuplicating_w2_success.target ∧
      PermittedW2Transform fullLinear_w2_success.transformClass fullLinear_w2_success.target := by
  refine ⟨?_, ?_⟩
  · simpa [fullDuplicating_w2_success] using fullDuplicating_w2_success_requires_ko7_dp_projection
  · simpa [fullLinear_w2_success] using fullLinear_w2_success_requires_benchmark_family_transform

theorem fullDuplicating_route_payloads_separate_from_direct_search :
    (canonicalWitnessW1Success? .w1ImportedWhole = some importedWhole_w1_success ∧
      importedWhole_w1_success.route ≠ .W0 ∧
      HasImportedWholeWitness fullDuplicating ∧
      ¬ HasDirectWitness fullDuplicating) ∧
      (canonicalWitnessW2Success? .w2FullDuplicating = some fullDuplicating_w2_success ∧
        fullDuplicating_w2_success.route ≠ .W0 ∧
        HasTransformedCallWitness fullDuplicating ∧
        ¬ HasDirectWitness fullDuplicating) := by
  refine ⟨?_, ?_⟩
  · exact ⟨rfl, importedWhole_w1_success_separates_from_w0.1,
      importedWhole_w1_success_separates_from_w0.2.1,
      importedWhole_w1_success_separates_from_w0.2.2⟩
  · exact ⟨rfl, fullDuplicating_w2_separates_from_direct_search.1,
      fullDuplicating_w2_separates_from_direct_search.2.1,
      fullDuplicating_w2_separates_from_direct_search.2.2⟩

end OperatorKO7.ConstructionRouteCatalogPayload
