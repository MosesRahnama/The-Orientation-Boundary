import OperatorKO7.Meta.ConstructionRouteCatalog_Exactness

namespace OperatorKO7.ConstructionRouteCatalogPartition

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogPayload
open OperatorKO7.ConstructionRouteCatalogCertificate
open OperatorKO7.ConstructionRouteCatalogAudit
open OperatorKO7.ConstructionRouteCatalogExactness
open OperatorKO7.TransformedCallClassification

/-- The four canonical W1 rows in the finite construction ledger. -/
def CanonicalWitnessIsW1 (w : CanonicalConstructionWitness) : Prop :=
  w = .w1MPO
    ∨ w = .w1Polynomial
    ∨ w = .w1ImportedWhole
    ∨ w = .w1Transparency

/-- The two canonical W2 rows in the finite construction ledger. -/
def CanonicalWitnessIsW2 (w : CanonicalConstructionWitness) : Prop :=
  w = .w2FullDuplicating ∨ w = .w2FullLinear

/-- Exact certificate-facing package for the six-row ledger: exactness,
audit, W1/W2 partition, and payload consistency. -/
abbrev CanonicalConstructionCertificateExactness : Prop :=
  CanonicalConstructionExactnessCatalog
    ∧ CanonicalConstructionAuditCatalog
    ∧ (∀ w : CanonicalConstructionWitness,
        CanonicalWitnessIsW1 w ∨ CanonicalWitnessIsW2 w)
    ∧ (∀ w : CanonicalConstructionWitness,
        ¬ (CanonicalWitnessIsW1 w ∧ CanonicalWitnessIsW2 w))
    ∧ ((∀ w : CanonicalConstructionWitness,
          CanonicalWitnessIsW1 w →
            canonicalWitnessRoute w = .W1
              ∧ ∃ S : W1ConstructionSuccess, canonicalWitnessW1Success? w = some S)
       ∧ (∀ w : CanonicalConstructionWitness,
          CanonicalWitnessIsW2 w →
            canonicalWitnessRoute w = .W2
              ∧ ∃ S : W2ConstructionSuccess, canonicalWitnessW2Success? w = some S))

/-- Every canonical row lies in the explicit W1/W2 partition. -/
theorem canonical_witness_w1_or_w2 (w : CanonicalConstructionWitness) :
    CanonicalWitnessIsW1 w ∨ CanonicalWitnessIsW2 w := by
  cases w <;> simp [CanonicalWitnessIsW1, CanonicalWitnessIsW2]

/-- No canonical row belongs to both sides of the explicit partition. -/
theorem canonical_witness_not_both_w1_w2 (w : CanonicalConstructionWitness) :
    ¬ (CanonicalWitnessIsW1 w ∧ CanonicalWitnessIsW2 w) := by
  cases w <;> simp [CanonicalWitnessIsW1, CanonicalWitnessIsW2]

/-- The explicit W1 partition identifies exactly the four W1 constructors. -/
theorem canonical_w1_partition_catalog :
    CanonicalWitnessIsW1 .w1MPO
      ∧ CanonicalWitnessIsW1 .w1Polynomial
      ∧ CanonicalWitnessIsW1 .w1ImportedWhole
      ∧ CanonicalWitnessIsW1 .w1Transparency
      ∧ ¬ CanonicalWitnessIsW1 .w2FullDuplicating
      ∧ ¬ CanonicalWitnessIsW1 .w2FullLinear := by
  simp [CanonicalWitnessIsW1]

/-- The explicit W2 partition identifies exactly the two W2 constructors. -/
theorem canonical_w2_partition_catalog :
    CanonicalWitnessIsW2 .w2FullDuplicating
      ∧ CanonicalWitnessIsW2 .w2FullLinear
      ∧ ¬ CanonicalWitnessIsW2 .w1MPO
      ∧ ¬ CanonicalWitnessIsW2 .w1Polynomial
      ∧ ¬ CanonicalWitnessIsW2 .w1ImportedWhole
      ∧ ¬ CanonicalWitnessIsW2 .w1Transparency := by
  simp [CanonicalWitnessIsW2]

/-- The explicit W1/W2 partition matches both the route tags and the payload
adapters already present in the finite ledger. -/
theorem canonical_partition_payload_consistency :
    (∀ w : CanonicalConstructionWitness,
      CanonicalWitnessIsW1 w →
        canonicalWitnessRoute w = .W1
          ∧ ∃ S : W1ConstructionSuccess, canonicalWitnessW1Success? w = some S)
      ∧ (∀ w : CanonicalConstructionWitness,
        CanonicalWitnessIsW2 w →
          canonicalWitnessRoute w = .W2
            ∧ ∃ S : W2ConstructionSuccess, canonicalWitnessW2Success? w = some S) := by
  constructor
  · intro w
    cases w with
    | w1MPO =>
        intro _
        exact ⟨rfl, ⟨mpo_w1_success, rfl⟩⟩
    | w1Polynomial =>
        intro _
        exact ⟨rfl, ⟨poly_w1_success, rfl⟩⟩
    | w1ImportedWhole =>
        intro _
        exact ⟨rfl, ⟨importedWhole_w1_success, rfl⟩⟩
    | w1Transparency =>
        intro _
        exact ⟨rfl, ⟨transparency_w1_success, rfl⟩⟩
    | w2FullDuplicating =>
        intro hw
        simp [CanonicalWitnessIsW1] at hw
    | w2FullLinear =>
        intro hw
        simp [CanonicalWitnessIsW1] at hw
  · intro w
    cases w with
    | w1MPO =>
        intro hw
        simp [CanonicalWitnessIsW2] at hw
    | w1Polynomial =>
        intro hw
        simp [CanonicalWitnessIsW2] at hw
    | w1ImportedWhole =>
        intro hw
        simp [CanonicalWitnessIsW2] at hw
    | w1Transparency =>
        intro hw
        simp [CanonicalWitnessIsW2] at hw
    | w2FullDuplicating =>
        intro _
        exact ⟨rfl, ⟨fullDuplicating_w2_success, rfl⟩⟩
    | w2FullLinear =>
        intro _
        exact ⟨rfl, ⟨fullLinear_w2_success, rfl⟩⟩

/-- The finite M1 certificate is exact at the six-row level: exactness, audit,
partition, and payload consistency all recover from the existing certificate. -/
theorem canonical_construction_certificate_exactness
    (h : CanonicalConstructionCertificate) :
    CanonicalConstructionCertificateExactness := by
  exact ⟨canonical_construction_exactness_catalog,
    canonical_construction_certificate_implies_audit_catalog h,
    canonical_witness_w1_or_w2,
    canonical_witness_not_both_w1_w2,
    canonical_partition_payload_consistency⟩

/-- Final theorem-facing bundle for the six-row construction catalog. -/
structure CanonicalConstructionFinalCatalog where
  certificate : CanonicalConstructionCertificate
  exactness : CanonicalConstructionExactnessCatalog
  audit : CanonicalConstructionAuditCatalog
  partition : ∀ w : CanonicalConstructionWitness,
    CanonicalWitnessIsW1 w ∨ CanonicalWitnessIsW2 w
  noOverlap : ∀ w : CanonicalConstructionWitness,
    ¬ (CanonicalWitnessIsW1 w ∧ CanonicalWitnessIsW2 w)
  w1PayloadConsistency : ∀ w : CanonicalConstructionWitness,
    CanonicalWitnessIsW1 w →
      canonicalWitnessRoute w = .W1
        ∧ ∃ S : W1ConstructionSuccess, canonicalWitnessW1Success? w = some S
  w2PayloadConsistency : ∀ w : CanonicalConstructionWitness,
    CanonicalWitnessIsW2 w →
      canonicalWitnessRoute w = .W2
        ∧ ∃ S : W2ConstructionSuccess, canonicalWitnessW2Success? w = some S

/-- Final bundled catalog for the current finite construction-route governance cluster. -/
theorem canonical_construction_final_catalog : CanonicalConstructionFinalCatalog := by
  refine {
    certificate := canonical_construction_certificate
    exactness := canonical_construction_exactness_catalog
    audit := canonical_construction_audit_catalog
    partition := canonical_witness_w1_or_w2
    noOverlap := canonical_witness_not_both_w1_w2
    w1PayloadConsistency := canonical_partition_payload_consistency.1
    w2PayloadConsistency := canonical_partition_payload_consistency.2
  }

/-- The final catalog projects the underlying finite certificate. -/
theorem canonical_construction_final_catalog_projects_certificate :
    CanonicalConstructionCertificate :=
  canonical_construction_final_catalog.certificate

/-- The final catalog projects the exact six-row witness ledger. -/
theorem canonical_construction_final_catalog_projects_exactness :
    CanonicalConstructionExactnessCatalog :=
  canonical_construction_final_catalog.exactness

/-- The final catalog projects the six-row audit ledger. -/
theorem canonical_construction_final_catalog_projects_audit :
    CanonicalConstructionAuditCatalog :=
  canonical_construction_final_catalog.audit

/-- Exact constructor-level classification of the W1 side of the partition. -/
theorem canonicalWitnessIsW1_exact (w : CanonicalConstructionWitness) :
    CanonicalWitnessIsW1 w ↔
      w = .w1MPO
        ∨ w = .w1Polynomial
        ∨ w = .w1ImportedWhole
        ∨ w = .w1Transparency := by
  cases w <;> simp [CanonicalWitnessIsW1]

/-- Exact constructor-level classification of the W2 side of the partition. -/
theorem canonicalWitnessIsW2_exact (w : CanonicalConstructionWitness) :
    CanonicalWitnessIsW2 w ↔ w = .w2FullDuplicating ∨ w = .w2FullLinear := by
  cases w <;> simp [CanonicalWitnessIsW2]

/-- Exact route-level classification of the W1 rows. -/
theorem canonicalWitnessIsW1_iff_routeW1 (w : CanonicalConstructionWitness) :
    CanonicalWitnessIsW1 w ↔ canonicalWitnessRoute w = .W1 := by
  cases w <;> simp [CanonicalWitnessIsW1, canonicalWitnessRoute]

/-- Exact route-level classification of the W2 rows. -/
theorem canonicalWitnessIsW2_iff_routeW2 (w : CanonicalConstructionWitness) :
    CanonicalWitnessIsW2 w ↔ canonicalWitnessRoute w = .W2 := by
  cases w <;> simp [CanonicalWitnessIsW2, canonicalWitnessRoute]

/-- No canonical row is left outside the explicit W1/W2 partition. -/
theorem canonical_witness_no_unclassified_row (w : CanonicalConstructionWitness) :
    CanonicalWitnessIsW1 w ∨ CanonicalWitnessIsW2 w :=
  canonical_construction_final_catalog.partition w

/-- No canonical row belongs to both sides of the explicit W1/W2 partition. -/
theorem canonical_witness_no_overlap (w : CanonicalConstructionWitness) :
    ¬ (CanonicalWitnessIsW1 w ∧ CanonicalWitnessIsW2 w) :=
  canonical_construction_final_catalog.noOverlap w

/-- Every W1 row in the final catalog agrees with a concrete W1 payload object. -/
theorem canonical_w1_route_payload_agreement
    (w : CanonicalConstructionWitness) (hw : CanonicalWitnessIsW1 w) :
    ∃ S : W1ConstructionSuccess,
      canonicalWitnessW1Success? w = some S ∧ canonicalWitnessRoute w = S.route := by
  obtain ⟨hRoute, S, hPayload⟩ :=
    canonical_construction_final_catalog.w1PayloadConsistency w hw
  exact ⟨S, hPayload, hRoute.trans S.route_is_w1.symm⟩

/-- Every W2 row in the final catalog agrees with a concrete W2 payload object. -/
theorem canonical_w2_route_payload_agreement
    (w : CanonicalConstructionWitness) (hw : CanonicalWitnessIsW2 w) :
    ∃ S : W2ConstructionSuccess,
      canonicalWitnessW2Success? w = some S ∧ canonicalWitnessRoute w = S.route := by
  obtain ⟨hRoute, S, hPayload⟩ :=
    canonical_construction_final_catalog.w2PayloadConsistency w hw
  exact ⟨S, hPayload, hRoute.trans S.route_is_w2.symm⟩

/-- The final catalog projects the MPO W1 row. -/
theorem canonical_construction_final_catalog_projects_w1MPO :
    CanonicalWitnessIsW1 .w1MPO
      ∧ canonicalWitnessRoute .w1MPO = .W1
      ∧ canonicalWitnessW1Success? .w1MPO = some mpo_w1_success := by
  exact ⟨by simp [CanonicalWitnessIsW1], rfl, rfl⟩

/-- The final catalog projects the polynomial W1 row. -/
theorem canonical_construction_final_catalog_projects_w1Polynomial :
    CanonicalWitnessIsW1 .w1Polynomial
      ∧ canonicalWitnessRoute .w1Polynomial = .W1
      ∧ canonicalWitnessW1Success? .w1Polynomial = some poly_w1_success := by
  exact ⟨by simp [CanonicalWitnessIsW1], rfl, rfl⟩

/-- The final catalog projects the imported-whole W1 row. -/
theorem canonical_construction_final_catalog_projects_w1ImportedWhole :
    CanonicalWitnessIsW1 .w1ImportedWhole
      ∧ canonicalWitnessRoute .w1ImportedWhole = .W1
      ∧ canonicalWitnessW1Success? .w1ImportedWhole = some importedWhole_w1_success := by
  exact ⟨by simp [CanonicalWitnessIsW1], rfl, rfl⟩

/-- The final catalog projects the transparency W1 row. -/
theorem canonical_construction_final_catalog_projects_w1Transparency :
    CanonicalWitnessIsW1 .w1Transparency
      ∧ canonicalWitnessRoute .w1Transparency = .W1
      ∧ canonicalWitnessW1Success? .w1Transparency = some transparency_w1_success := by
  exact ⟨by simp [CanonicalWitnessIsW1], rfl, rfl⟩

/-- The final catalog projects the full-duplicating W2 row. -/
theorem canonical_construction_final_catalog_projects_w2FullDuplicating :
    CanonicalWitnessIsW2 .w2FullDuplicating
      ∧ canonicalWitnessRoute .w2FullDuplicating = .W2
      ∧ canonicalWitnessW2Success? .w2FullDuplicating = some fullDuplicating_w2_success := by
  exact ⟨by simp [CanonicalWitnessIsW2], rfl, rfl⟩

/-- The final catalog projects the full-linear W2 row. -/
theorem canonical_construction_final_catalog_projects_w2FullLinear :
    CanonicalWitnessIsW2 .w2FullLinear
      ∧ canonicalWitnessRoute .w2FullLinear = .W2
      ∧ canonicalWitnessW2Success? .w2FullLinear = some fullLinear_w2_success := by
  exact ⟨by simp [CanonicalWitnessIsW2], rfl, rfl⟩

end OperatorKO7.ConstructionRouteCatalogPartition
