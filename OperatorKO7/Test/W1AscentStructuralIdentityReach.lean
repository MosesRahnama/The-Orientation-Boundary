import OperatorKO7.Meta.W1AscentStructuralIdentity

/-!
# Reach test: W1AscentStructuralIdentity (Lane W)

Asserts that the headline theorem `w1_ascent_structural_identity`
and all supporting declarations resolve verbatim.
-/

namespace W1AscentStructuralIdentityReach

open OperatorKO7.W1AscentStructuralIdentity
open OperatorKO7.W1MethodCarrier
open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

#check W1AscentSixStepProfile
#check RealizesW1AscentProfile
#check W1AscentSlot
#check SlotHolds
#check w1AscentProfileFor
#check w1_ascent_structural_identity
#check w1_ascent_distinct_from_w2_confession
#check w1_ascent_construction_family_classification

/-- Sanity: every W1 carrier row satisfies its six-step ascent profile. -/
example : ∀ row : W1MethodRow,
    RealizesW1AscentProfile (w1AscentProfileFor row) :=
  w1_ascent_structural_identity

/-- Sanity: the precedence (MPO/path-order) row satisfies its profile. -/
example : RealizesW1AscentProfile (w1AscentProfileFor .canonicalPrecedence) :=
  w1_ascent_structural_identity .canonicalPrecedence

/-- Sanity: the polynomial row satisfies its profile. -/
example : RealizesW1AscentProfile (w1AscentProfileFor .canonicalGlobalPolynomial) :=
  w1_ascent_structural_identity .canonicalGlobalPolynomial

/-- Sanity: the imported-whole row satisfies its profile. -/
example : RealizesW1AscentProfile (w1AscentProfileFor .canonicalImportedWhole) :=
  w1_ascent_structural_identity .canonicalImportedWhole

/-- Sanity: the transparency-essentiality row satisfies its profile. -/
example : RealizesW1AscentProfile (w1AscentProfileFor .canonicalTransparency) :=
  w1_ascent_structural_identity .canonicalTransparency

/-- Sanity: construction and confession are structurally exclusive. -/
example {S : StepDuplicatingSchema} (C : ConstructionResponse S) (F : ForgettingWitness S)
    (hrank : C.rank = F.rank) : False :=
  w1_ascent_distinct_from_w2_confession C F hrank

/-- Sanity: classification part 1 — construction-confession exclusivity. -/
example : ∀ {S : StepDuplicatingSchema} (C : ConstructionResponse S) (F : ForgettingWitness S),
    C.rank = F.rank → False :=
  w1_ascent_construction_family_classification.1

/-- Sanity: classification part 2 — every W1 row is in the construction family. -/
example : ∀ row : W1MethodRow,
    PermittedW1Import (w1MethodRowImportClass row) ∧
    w1MethodRowStatus row = .licensedEscape .W1 ∧
    w1MethodRowRoute row ≠ .W0 ∧
    w1MethodRowRoute row ≠ .W2 :=
  w1_ascent_construction_family_classification.2

end W1AscentStructuralIdentityReach
