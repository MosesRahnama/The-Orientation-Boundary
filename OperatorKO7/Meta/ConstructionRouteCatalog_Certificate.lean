import OperatorKO7.Meta.ConstructionRouteCatalog_Payload

namespace OperatorKO7.ConstructionRouteCatalogCertificate

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogPayload
open OperatorKO7.TransformedCallClassification
open OperatorKO7.BenchmarkedPRCFamily

/-- Paper-facing proposition for the finite canonical route catalog. -/
abbrev CanonicalConstructionRouteCatalog : Prop :=
  ((canonicalWitnessRoute .w1MPO = .W1 ∧ canonicalWitnessW1ImportClass? .w1MPO = some .precedence) ∧
    (canonicalWitnessRoute .w1Polynomial = .W1 ∧
      canonicalWitnessW1ImportClass? .w1Polynomial = some .globalPolynomial) ∧
    (canonicalWitnessRoute .w1ImportedWhole = .W1 ∧
      canonicalWitnessW1ImportClass? .w1ImportedWhole = some .importedWholeWitness) ∧
    (canonicalWitnessRoute .w1Transparency = .W1 ∧
      canonicalWitnessW1ImportClass? .w1Transparency = some .transparencyEssentiality)) ∧
    ((canonicalWitnessRoute .w2FullDuplicating = .W2 ∧
      canonicalWitnessW2TransformClass? .w2FullDuplicating = some .ko7DPProjection) ∧
      (canonicalWitnessRoute .w2FullLinear = .W2 ∧
        canonicalWitnessW2TransformClass? .w2FullLinear = some .benchmarkFamilyTransformedCall))

/-- Paper-facing proposition for the finite canonical payload catalog. -/
abbrev CanonicalConstructionPayloadCatalog : Prop :=
  CanonicalW1SuccessPayloadCatalog ∧ CanonicalW2SuccessPayloadCatalog

/-- Paper-facing proposition for the four permitted W1 imports in the finite ledger. -/
abbrev CanonicalConstructionW1Imports : Prop :=
  PermittedW1Import mpo_w1_success.importClass ∧
    PermittedW1Import poly_w1_success.importClass ∧
    PermittedW1Import importedWhole_w1_success.importClass ∧
    PermittedW1Import transparency_w1_success.importClass

/-- Paper-facing proposition for the two permitted W2 transforms in the finite ledger. -/
abbrev CanonicalConstructionW2Transforms : Prop :=
  PermittedW2Transform fullDuplicating_w2_success.transformClass fullDuplicating_w2_success.target ∧
    PermittedW2Transform fullLinear_w2_success.transformClass fullLinear_w2_success.target

/-- Paper-facing proposition for the full-duplicating direct-search separation facts carried by the ledger. -/
abbrev FullDuplicatingRoutePayloadSeparation : Prop :=
  (canonicalWitnessW1Success? .w1ImportedWhole = some importedWhole_w1_success ∧
    importedWhole_w1_success.route ≠ .W0 ∧
    HasImportedWholeWitness fullDuplicating ∧
    ¬ HasDirectWitness fullDuplicating) ∧
    (canonicalWitnessW2Success? .w2FullDuplicating = some fullDuplicating_w2_success ∧
      fullDuplicating_w2_success.route ≠ .W0 ∧
      HasTransformedCallWitness fullDuplicating ∧
      ¬ HasDirectWitness fullDuplicating)

/-- Certificate packaging the finite route catalog and its theorem-backed payload layer. -/
structure CanonicalConstructionCertificate where
  routeCatalog : CanonicalConstructionRouteCatalog
  payloadCatalog : CanonicalConstructionPayloadCatalog
  w1Imports : CanonicalConstructionW1Imports
  w2Transforms : CanonicalConstructionW2Transforms
  fullDuplicatingSeparation : FullDuplicatingRoutePayloadSeparation

/-- The paper-facing M1 certificate is exactly the finite route and payload ledger already proved. -/
theorem canonical_construction_certificate : CanonicalConstructionCertificate := by
  exact {
    routeCatalog := canonical_construction_route_catalog
    payloadCatalog := canonical_route_payload_catalog
    w1Imports := canonical_w1_payloads_have_permitted_imports
    w2Transforms := canonical_w2_payloads_have_permitted_transforms
    fullDuplicatingSeparation := fullDuplicating_route_payloads_separate_from_direct_search
  }

/-- The certificate projects the finite route catalog. -/
theorem canonical_construction_certificate_projects_route_catalog :
    CanonicalConstructionRouteCatalog :=
  canonical_construction_certificate.routeCatalog

/-- The certificate projects the finite payload catalog. -/
theorem canonical_construction_certificate_projects_payload_catalog :
    CanonicalConstructionPayloadCatalog :=
  canonical_construction_certificate.payloadCatalog

/-- The certificate projects the four permitted W1 import facts. -/
theorem canonical_construction_certificate_projects_w1_imports :
    CanonicalConstructionW1Imports :=
  canonical_construction_certificate.w1Imports

/-- The certificate projects the two permitted W2 transform facts. -/
theorem canonical_construction_certificate_projects_w2_transforms :
    CanonicalConstructionW2Transforms :=
  canonical_construction_certificate.w2Transforms

/-- The certificate projects the full-duplicating direct-search separation facts. -/
theorem canonical_construction_certificate_projects_fullDuplicating_separation :
    FullDuplicatingRoutePayloadSeparation :=
  canonical_construction_certificate.fullDuplicatingSeparation

end OperatorKO7.ConstructionRouteCatalogCertificate
