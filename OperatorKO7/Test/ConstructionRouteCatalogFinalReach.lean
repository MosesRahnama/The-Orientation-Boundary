import OperatorKO7.Meta.ConstructionRouteCatalog_Partition

namespace ConstructionRouteCatalogFinalReach

open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogCertificate
open OperatorKO7.ConstructionRouteCatalogExactness
open OperatorKO7.ConstructionRouteCatalogPayload
open OperatorKO7.ConstructionRouteCatalogPartition
open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.TransformedCallClassification

#check CanonicalConstructionFinalCatalog
#check canonical_construction_final_catalog
#check canonical_construction_final_catalog_projects_certificate
#check canonical_construction_final_catalog_projects_exactness
#check canonical_construction_final_catalog_projects_audit
#check canonicalWitnessIsW1_exact
#check canonicalWitnessIsW2_exact
#check canonicalWitnessIsW1_iff_routeW1
#check canonicalWitnessIsW2_iff_routeW2
#check canonical_witness_no_unclassified_row
#check canonical_witness_no_overlap
#check canonical_w1_route_payload_agreement
#check canonical_w2_route_payload_agreement
#check canonical_construction_final_catalog_projects_w1MPO
#check canonical_construction_final_catalog_projects_w1Polynomial
#check canonical_construction_final_catalog_projects_w1ImportedWhole
#check canonical_construction_final_catalog_projects_w1Transparency
#check canonical_construction_final_catalog_projects_w2FullDuplicating
#check canonical_construction_final_catalog_projects_w2FullLinear

example : CanonicalConstructionFinalCatalog :=
  canonical_construction_final_catalog

example (w : CanonicalConstructionWitness) :
    CanonicalWitnessIsW1 w ↔
      w = .w1MPO
        ∨ w = .w1Polynomial
        ∨ w = .w1ImportedWhole
        ∨ w = .w1Transparency :=
  canonicalWitnessIsW1_exact w

example (w : CanonicalConstructionWitness) :
    CanonicalWitnessIsW2 w ↔ w = .w2FullDuplicating ∨ w = .w2FullLinear :=
  canonicalWitnessIsW2_exact w

example (w : CanonicalConstructionWitness) :
    CanonicalWitnessIsW1 w ↔ canonicalWitnessRoute w = .W1 :=
  canonicalWitnessIsW1_iff_routeW1 w

example (w : CanonicalConstructionWitness) :
    CanonicalWitnessIsW2 w ↔ canonicalWitnessRoute w = .W2 :=
  canonicalWitnessIsW2_iff_routeW2 w

example (w : CanonicalConstructionWitness) :
    CanonicalWitnessIsW1 w ∨ CanonicalWitnessIsW2 w :=
  canonical_witness_no_unclassified_row w

example (w : CanonicalConstructionWitness) :
    ¬ (CanonicalWitnessIsW1 w ∧ CanonicalWitnessIsW2 w) :=
  canonical_witness_no_overlap w

example : CanonicalWitnessIsW1 .w1MPO := by
  exact canonical_construction_final_catalog_projects_w1MPO.1

example : CanonicalWitnessIsW1 .w1Polynomial := by
  exact canonical_construction_final_catalog_projects_w1Polynomial.1

example : CanonicalWitnessIsW1 .w1ImportedWhole := by
  exact canonical_construction_final_catalog_projects_w1ImportedWhole.1

example : CanonicalWitnessIsW1 .w1Transparency := by
  exact canonical_construction_final_catalog_projects_w1Transparency.1

example : CanonicalWitnessIsW2 .w2FullDuplicating := by
  exact canonical_construction_final_catalog_projects_w2FullDuplicating.1

example : CanonicalWitnessIsW2 .w2FullLinear := by
  exact canonical_construction_final_catalog_projects_w2FullLinear.1

example : canonicalWitnessRoute .w1MPO = .W1 := by
  exact canonical_construction_final_catalog_projects_w1MPO.2.1

example : canonicalWitnessRoute .w1Polynomial = .W1 := by
  exact canonical_construction_final_catalog_projects_w1Polynomial.2.1

example : canonicalWitnessRoute .w1ImportedWhole = .W1 := by
  exact canonical_construction_final_catalog_projects_w1ImportedWhole.2.1

example : canonicalWitnessRoute .w1Transparency = .W1 := by
  exact canonical_construction_final_catalog_projects_w1Transparency.2.1

example : canonicalWitnessRoute .w2FullDuplicating = .W2 := by
  exact canonical_construction_final_catalog_projects_w2FullDuplicating.2.1

example : canonicalWitnessRoute .w2FullLinear = .W2 := by
  exact canonical_construction_final_catalog_projects_w2FullLinear.2.1

example : canonicalWitnessW1Success? .w1MPO = some mpo_w1_success := by
  exact canonical_construction_final_catalog_projects_w1MPO.2.2

example : canonicalWitnessW1Success? .w1Polynomial = some poly_w1_success := by
  exact canonical_construction_final_catalog_projects_w1Polynomial.2.2

example : canonicalWitnessW1Success? .w1Transparency = some transparency_w1_success := by
  exact canonical_construction_final_catalog_projects_w1Transparency.2.2

example : canonicalWitnessW1Success? .w1ImportedWhole = some importedWhole_w1_success := by
  exact canonical_construction_final_catalog_projects_w1ImportedWhole.2.2

example : canonicalWitnessW2Success? .w2FullLinear = some fullLinear_w2_success := by
  exact canonical_construction_final_catalog_projects_w2FullLinear.2.2

example : canonicalWitnessW2Success? .w2FullDuplicating = some fullDuplicating_w2_success := by
  exact canonical_construction_final_catalog_projects_w2FullDuplicating.2.2

example (w : CanonicalConstructionWitness) (hw : CanonicalWitnessIsW1 w) :
    ∃ S : W1ConstructionSuccess,
      canonicalWitnessW1Success? w = some S
        ∧ canonicalWitnessRoute w = S.route :=
  canonical_w1_route_payload_agreement w hw

example (w : CanonicalConstructionWitness) (hw : CanonicalWitnessIsW2 w) :
    ∃ S : W2ConstructionSuccess,
      canonicalWitnessW2Success? w = some S
        ∧ canonicalWitnessRoute w = S.route :=
  canonical_w2_route_payload_agreement w hw

example :
    ∃ S : W1ConstructionSuccess,
      canonicalWitnessW1Success? .w1Polynomial = some S
        ∧ canonicalWitnessRoute .w1Polynomial = S.route :=
  canonical_w1_route_payload_agreement .w1Polynomial (by simp [CanonicalWitnessIsW1])

example :
    ∃ S : W2ConstructionSuccess,
      canonicalWitnessW2Success? .w2FullDuplicating = some S
        ∧ canonicalWitnessRoute .w2FullDuplicating = S.route :=
  canonical_w2_route_payload_agreement .w2FullDuplicating (by simp [CanonicalWitnessIsW2])

example : CanonicalConstructionCertificate :=
  canonical_construction_final_catalog_projects_certificate

example : CanonicalConstructionExactnessCatalog :=
  canonical_construction_final_catalog_projects_exactness

end ConstructionRouteCatalogFinalReach
