import OperatorKO7.Meta.ConstructionRouteCatalog_Certificate

namespace OperatorKO7.ConstructionRouteCatalogAudit

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogPayload
open OperatorKO7.ConstructionRouteCatalogCertificate
open OperatorKO7.TransformedCallClassification

/-- The finite canonical witness list audited by the paper-facing M1 layer. -/
def canonicalConstructionWitnesses : List CanonicalConstructionWitness :=
  [.w1MPO, .w1Polynomial, .w1ImportedWhole, .w1Transparency, .w2FullDuplicating, .w2FullLinear]

/-- A canonical row has payload exactly when it carries either a W1 or a W2 success object. -/
def CanonicalWitnessHasPayload (w : CanonicalConstructionWitness) : Prop :=
  (∃ S : W1ConstructionSuccess, canonicalWitnessW1Success? w = some S) ∨
    (∃ S : W2ConstructionSuccess, canonicalWitnessW2Success? w = some S)

/-- Paper-facing proposition for the finite witness audit catalog. -/
abbrev CanonicalConstructionAuditCatalog : Prop :=
  (∀ w : CanonicalConstructionWitness, w ∈ canonicalConstructionWitnesses) ∧
    (∀ w : CanonicalConstructionWitness,
      w ∈ canonicalConstructionWitnesses →
        CanonicalWitnessHasPayload w ∧ canonicalWitnessRoute w ≠ .W0)

/-- Every canonical witness appears in the finite audit list. -/
theorem canonicalConstructionWitnesses_complete :
    ∀ w : CanonicalConstructionWitness, w ∈ canonicalConstructionWitnesses := by
  intro w
  cases w <;> simp [canonicalConstructionWitnesses]

/-- Every row in the finite audit list carries an actual W1 or W2 payload object. -/
theorem canonical_witness_has_payload :
    ∀ w : CanonicalConstructionWitness,
      w ∈ canonicalConstructionWitnesses → CanonicalWitnessHasPayload w := by
  intro w _
  cases w with
  | w1MPO =>
      exact Or.inl ⟨mpo_w1_success, rfl⟩
  | w1Polynomial =>
      exact Or.inl ⟨poly_w1_success, rfl⟩
  | w1ImportedWhole =>
      exact Or.inl ⟨importedWhole_w1_success, rfl⟩
  | w1Transparency =>
      exact Or.inl ⟨transparency_w1_success, rfl⟩
  | w2FullDuplicating =>
      exact Or.inr ⟨fullDuplicating_w2_success, rfl⟩
  | w2FullLinear =>
      exact Or.inr ⟨fullLinear_w2_success, rfl⟩

/-- Every row in the finite audit list carries payload and stays outside W0. -/
theorem canonical_witness_has_payload_and_non_w0 :
    ∀ w : CanonicalConstructionWitness,
      w ∈ canonicalConstructionWitnesses →
        CanonicalWitnessHasPayload w ∧ canonicalWitnessRoute w ≠ .W0 := by
  intro w hw
  exact ⟨canonical_witness_has_payload w hw, canonical_witness_route_not_w0 w⟩

/-- Combined finite audit catalog for the six canonical construction witnesses. -/
theorem canonical_construction_audit_catalog : CanonicalConstructionAuditCatalog := by
  exact ⟨canonicalConstructionWitnesses_complete, canonical_witness_has_payload_and_non_w0⟩

/-- The paper-facing certificate is sufficient to recover the finite audit catalog. -/
theorem canonical_construction_certificate_implies_audit_catalog
    (_ : CanonicalConstructionCertificate) : CanonicalConstructionAuditCatalog := by
  exact canonical_construction_audit_catalog

end OperatorKO7.ConstructionRouteCatalogAudit
