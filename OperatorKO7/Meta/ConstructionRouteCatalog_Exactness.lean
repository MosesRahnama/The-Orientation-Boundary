import OperatorKO7.Meta.ConstructionRouteCatalog_Audit

namespace OperatorKO7.ConstructionRouteCatalogExactness

open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogAudit

/-- Paper-facing exactness package for the six-row canonical witness list. -/
abbrev CanonicalConstructionExactnessCatalog : Prop :=
  canonicalConstructionWitnesses.Nodup
    ∧ canonicalConstructionWitnesses.length = 6
    ∧ (∀ w : CanonicalConstructionWitness,
        w ∈ canonicalConstructionWitnesses ↔
          w = .w1MPO
            ∨ w = .w1Polynomial
            ∨ w = .w1ImportedWhole
            ∨ w = .w1Transparency
            ∨ w = .w2FullDuplicating
            ∨ w = .w2FullLinear)
    ∧ (∀ w : CanonicalConstructionWitness,
        w ∈ canonicalConstructionWitnesses → CanonicalWitnessHasPayload w)
    ∧ (∀ w : CanonicalConstructionWitness,
        w ∈ canonicalConstructionWitnesses → canonicalWitnessRoute w ≠ .W0)

/-- The six canonical witnesses form a duplicate-free finite list. -/
theorem canonicalConstructionWitnesses_nodup :
    canonicalConstructionWitnesses.Nodup := by
  decide

/-- The finite canonical witness list has exact size six. -/
theorem canonicalConstructionWitnesses_length :
    canonicalConstructionWitnesses.length = 6 := by
  rfl

/-- Iff-level membership characterization for the six canonical witness rows. -/
theorem canonicalConstructionWitnesses_complete_exact
    (w : CanonicalConstructionWitness) :
    w ∈ canonicalConstructionWitnesses ↔
      w = .w1MPO
        ∨ w = .w1Polynomial
        ∨ w = .w1ImportedWhole
        ∨ w = .w1Transparency
        ∨ w = .w2FullDuplicating
        ∨ w = .w2FullLinear := by
  cases w <;> simp [canonicalConstructionWitnesses]

/-- Every row in the exact witness list carries a payload object. -/
theorem canonicalConstructionWitnesses_all_have_payload :
    ∀ w : CanonicalConstructionWitness,
      w ∈ canonicalConstructionWitnesses → CanonicalWitnessHasPayload w :=
  canonical_witness_has_payload

/-- Every row in the exact witness list stays outside W0. -/
theorem canonicalConstructionWitnesses_all_non_w0 :
    ∀ w : CanonicalConstructionWitness,
      w ∈ canonicalConstructionWitnesses → canonicalWitnessRoute w ≠ .W0 := by
  intro w _
  exact canonical_witness_route_not_w0 w

/-- Combined exactness ledger for the finite canonical witness list. -/
theorem canonical_construction_exactness_catalog :
    CanonicalConstructionExactnessCatalog := by
  exact ⟨canonicalConstructionWitnesses_nodup,
    canonicalConstructionWitnesses_length,
    canonicalConstructionWitnesses_complete_exact,
    canonicalConstructionWitnesses_all_have_payload,
    canonicalConstructionWitnesses_all_non_w0⟩

end OperatorKO7.ConstructionRouteCatalogExactness
