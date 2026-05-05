import OperatorKO7.Meta.ConstructionMethodClassification
import OperatorKO7.Meta.TransformedCallClassification

/-!
# Construction Route Catalog

This module packages the currently formalized canonical construction routes into
one explicit ledger. It is intentionally finite and theorem-backed: four W1
witnesses and two W2 witnesses.
-/

namespace OperatorKO7.ConstructionRouteCatalog

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.TransformedCallClassification
open OperatorKO7.BenchmarkedPRCFamily

/-- Explicit catalog of the canonical construction witnesses currently formalized. -/
inductive CanonicalConstructionWitness where
  | w1MPO
  | w1Polynomial
  | w1ImportedWhole
  | w1Transparency
  | w2FullDuplicating
  | w2FullLinear
deriving DecidableEq, Repr

/-- Route tag attached to each canonical construction witness. -/
def canonicalWitnessRoute : CanonicalConstructionWitness → ConstructionRoute
  | .w1MPO => .W1
  | .w1Polynomial => .W1
  | .w1ImportedWhole => .W1
  | .w1Transparency => .W1
  | .w2FullDuplicating => .W2
  | .w2FullLinear => .W2

/-- W1 import class when the canonical witness is a W1 witness. -/
def canonicalWitnessW1ImportClass? : CanonicalConstructionWitness → Option W1ImportClass
  | .w1MPO => some .precedence
  | .w1Polynomial => some .globalPolynomial
  | .w1ImportedWhole => some .importedWholeWitness
  | .w1Transparency => some .transparencyEssentiality
  | .w2FullDuplicating => none
  | .w2FullLinear => none

/-- W2 transform class when the canonical witness is a W2 witness. -/
def canonicalWitnessW2TransformClass? : CanonicalConstructionWitness → Option W2TransformClass
  | .w1MPO => none
  | .w1Polynomial => none
  | .w1ImportedWhole => none
  | .w1Transparency => none
  | .w2FullDuplicating => some .ko7DPProjection
  | .w2FullLinear => some .benchmarkFamilyTransformedCall

/-- The W1 part of the explicit canonical route catalog. -/
theorem canonical_w1_route_catalog :
    (canonicalWitnessRoute .w1MPO = .W1 ∧ canonicalWitnessW1ImportClass? .w1MPO = some .precedence) ∧
      (canonicalWitnessRoute .w1Polynomial = .W1 ∧
        canonicalWitnessW1ImportClass? .w1Polynomial = some .globalPolynomial) ∧
      (canonicalWitnessRoute .w1ImportedWhole = .W1 ∧
        canonicalWitnessW1ImportClass? .w1ImportedWhole = some .importedWholeWitness) ∧
      (canonicalWitnessRoute .w1Transparency = .W1 ∧
        canonicalWitnessW1ImportClass? .w1Transparency = some .transparencyEssentiality) := by
  decide

/-- The W2 part of the explicit canonical route catalog. -/
theorem canonical_w2_route_catalog :
    (canonicalWitnessRoute .w2FullDuplicating = .W2 ∧
      canonicalWitnessW2TransformClass? .w2FullDuplicating = some .ko7DPProjection) ∧
      (canonicalWitnessRoute .w2FullLinear = .W2 ∧
        canonicalWitnessW2TransformClass? .w2FullLinear = some .benchmarkFamilyTransformedCall) := by
  decide

/-- Combined explicit route ledger for the currently formalized canonical witnesses. -/
theorem canonical_construction_route_catalog :
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
          canonicalWitnessW2TransformClass? .w2FullLinear = some .benchmarkFamilyTransformedCall)) := by
  exact ⟨canonical_w1_route_catalog, canonical_w2_route_catalog⟩

/-- Every canonical witness currently in the ledger is non-W0. -/
theorem canonical_witness_route_not_w0 (w : CanonicalConstructionWitness) :
    canonicalWitnessRoute w ≠ .W0 := by
  cases w <;> decide

/-- The full duplicating member has both a W1 imported-whole witness and a W2 transformed-call witness. -/
theorem fullDuplicating_has_w1_and_w2_non_w0_witnesses :
    canonicalWitnessRoute .w1ImportedWhole ≠ .W0 ∧
      canonicalWitnessRoute .w2FullDuplicating ≠ .W0 := by
  exact ⟨canonical_witness_route_not_w0 .w1ImportedWhole,
    canonical_witness_route_not_w0 .w2FullDuplicating⟩

/-- The full duplicating member is separated from direct search by both its canonical W1 and W2 routes. -/
theorem fullDuplicating_w1_w2_both_separate_from_direct_search :
    (importedWhole_w1_success.route ≠ .W0 ∧
      HasImportedWholeWitness fullDuplicating ∧
      ¬ HasDirectWitness fullDuplicating) ∧
      (fullDuplicating_w2_success.route ≠ .W0 ∧
        HasTransformedCallWitness fullDuplicating ∧
        ¬ HasDirectWitness fullDuplicating) := by
  exact ⟨importedWhole_w1_success_separates_from_w0,
    fullDuplicating_w2_separates_from_direct_search⟩

end OperatorKO7.ConstructionRouteCatalog
