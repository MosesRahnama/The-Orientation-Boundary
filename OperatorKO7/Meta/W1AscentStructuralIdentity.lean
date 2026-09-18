import OperatorKO7.Meta.W1MethodCarrier
import OperatorKO7.Meta.SchemaOperationalIncompleteness

/-!
# W1 Ascent Structural Identity

Paper C §9.b: the W₁ ascent shape is a parallel six-step profile to the W₂
DP confession schema, but categorically distinct in orientation.

W₁ ascent **adds objects** to the proof language (construction family): it
imports a global comparison structure (path order, polynomial, or matrix
interpretation) and verifies the system under the extended language. W₂
confession **subtracts a dimension**: it projects to a descent coordinate and
licenses forgetting the payload under an external soundness metatheorem.

This module:

1. (`W1AscentSixStepProfile`, W.1) — Defines the six propositional slots of
   the W₁ ascent shape, parallel to `LCELSlotProfile`.
2. (`w1_ascent_structural_identity`, W.2) — Proves every W₁ method-carrier
   row realizes its six-step ascent profile.
3. (`w1_ascent_distinct_from_w2_confession`, W.3) — Proves the ascent shape
   and confession shape are structurally exclusive.
4. (`w1_ascent_construction_family_classification`, W.4) — Classifies every
   W₁ row into the construction family (not projection-transaction), citing
   `construction_confession_exclusive`.

No `sorry`, no `admit`, no top-level `axiom`.
-/

namespace OperatorKO7.W1AscentStructuralIdentity

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.W1MethodCarrier
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-! ## Six-step ascent profile (W.1) -/

/-- Six propositional slots of the W₁ ascent shape, parallel to the six LCEL
clauses of the W₂ confession schema (`LCELSlotProfile` in `Meta/LCELSchema.lean`).

The dual orientation of W₁ vs W₂ at step (iii):
- W₁ step (iii): imports a global comparison structure — **adds** an object.
- W₂ step (iii): issues an external license to forget — **removes** a dimension. -/
structure W1AscentSixStepProfile where
  /-- (i)  The method belongs to a named construction family with a
      whole-term measure on the original system. -/
  hasBaseWitnessLanguage    : Prop
  /-- (ii) The method is separated from W0: the 12-class barrier package
      blocks any direct witness, forcing W₁ import. -/
  hasBarrierWitness         : Prop
  /-- (iii) The method imports a global comparison structure (path order,
      polynomial, or matrix interpretation) into the proof language. -/
  hasImportedComparison     : Prop
  /-- (iv) The extended proof language verifies the step on the extended
      system under the imported comparison. -/
  hasExtendedLanguageVerify : Prop
  /-- (v)  A soundness lift carries the extended-language verdict back to the
      original rules (KBO variable condition, polynomial monotone
      preconditions, etc.). -/
  hasSoundnessLift          : Prop
  /-- (vi) The verdict is transferred to the original termination question
      via the licensed escape route. -/
  hasVerdictTransfer        : Prop

/-- All six ascent slots hold. -/
def RealizesW1AscentProfile (P : W1AscentSixStepProfile) : Prop :=
  P.hasBaseWitnessLanguage
    ∧ P.hasBarrierWitness
    ∧ P.hasImportedComparison
    ∧ P.hasExtendedLanguageVerify
    ∧ P.hasSoundnessLift
    ∧ P.hasVerdictTransfer

/-- Named W₁ ascent slot, parallel to `LCELClause`. -/
inductive W1AscentSlot
  | baseWitnessLanguage
  | barrierWitness
  | importedComparison
  | extendedLanguageVerify
  | soundnessLift
  | verdictTransfer
  deriving DecidableEq, Repr

/-- Slot truth predicate for a `W1AscentSixStepProfile`. -/
def SlotHolds (P : W1AscentSixStepProfile) : W1AscentSlot → Prop
  | .baseWitnessLanguage    => P.hasBaseWitnessLanguage
  | .barrierWitness         => P.hasBarrierWitness
  | .importedComparison     => P.hasImportedComparison
  | .extendedLanguageVerify => P.hasExtendedLanguageVerify
  | .soundnessLift          => P.hasSoundnessLift
  | .verdictTransfer        => P.hasVerdictTransfer

/-- The canonical six-step ascent profile for a given W₁ method-carrier row.

Slot mapping against the carrier lemmas:
- (i)  `hasBaseWitnessLanguage`    ← `W1MethodRowSupported`
- (ii) `hasBarrierWitness`         ← route ≠ .W0
- (iii)`hasImportedComparison`     ← `PermittedW1Import (importClass row)`
- (iv) `hasExtendedLanguageVerify` ← status = `.licensedEscape .W1`
- (v)  `hasSoundnessLift`          ← `W1MethodRowSupported` (theorem backing)
- (vi) `hasVerdictTransfer`        ← `row ∈ w1MethodRows` (finite catalog) -/
def w1AscentProfileFor (row : W1MethodRow) : W1AscentSixStepProfile where
  hasBaseWitnessLanguage    := W1MethodRowSupported row
  hasBarrierWitness         := w1MethodRowRoute row ≠ .W0
  hasImportedComparison     := PermittedW1Import (w1MethodRowImportClass row)
  hasExtendedLanguageVerify := w1MethodRowStatus row = .licensedEscape .W1
  hasSoundnessLift          := W1MethodRowSupported row
  hasVerdictTransfer        := row ∈ w1MethodRows

/-! ## Headline theorems -/

/-- **W.2 (Lane W) — headline theorem.**

Every W₁ method-carrier row (path-order / polynomial / matrix / imported-whole)
realizes its six-step ascent profile.

Proof: case analysis on `W1MethodRow`, with each slot discharged by the
corresponding carrier lemma from `Meta/W1MethodCarrier.lean`. -/
theorem w1_ascent_structural_identity (row : W1MethodRow) :
    RealizesW1AscentProfile (w1AscentProfileFor row) :=
  ⟨w1MethodRowSupported_holds row,
   w1MethodRowRoute_ne_w0 row,
   w1MethodRowSupported_implies_permitted_import (w1MethodRowSupported_holds row),
   w1MethodRowStatus_exact row,
   w1MethodRowSupported_holds row,
   (w1MethodRows_complete_exact row).mpr (by cases row <;> decide)⟩

/-- **W.3 (Lane W).**

W₁ ascent and W₂ confession are structurally exclusive.

W₁ ascent step (iii) imports a global comparison structure and is
**wrapper-sensitive**: `rank (wrap x y) > rank x` and `rank (wrap x y) > rank y`
for all `x, y`. W₂ confession step (iii) is an external license to **forget**
the payload dimension: the rank explicitly violates wrapper sensitivity.

No rank function can simultaneously be a W₁ construction witness
(`ConstructionResponse`, wrapper-sensitive) and a W₂ forgetting witness
(`ForgettingWitness`, wrapper-insensitive). -/
theorem w1_ascent_distinct_from_w2_confession
    {S : StepDuplicatingSchema}
    (C : ConstructionResponse S)
    (F : ForgettingWitness S)
    (hrank : C.rank = F.rank) : False :=
  construction_confession_exclusive C F hrank

/-- **W.4 (Lane W).**

Every W₁ ascent instance lies in the construction-family schema, NOT in the
projection-transaction schema.

Proved in two parts:

1. Construction and confession are structurally exclusive (cites
   `construction_confession_exclusive` from `Meta/SchemaOperationalIncompleteness`).
2. Every W₁ carrier row's import class is permitted, its status is
   `.licensedEscape .W1`, and it is separated from both W0 and W2. -/
theorem w1_ascent_construction_family_classification :
    (∀ {S : StepDuplicatingSchema} (C : ConstructionResponse S) (F : ForgettingWitness S),
        C.rank = F.rank → False) ∧
    (∀ row : W1MethodRow,
        PermittedW1Import (w1MethodRowImportClass row) ∧
        w1MethodRowStatus row = .licensedEscape .W1 ∧
        w1MethodRowRoute row ≠ .W0 ∧
        w1MethodRowRoute row ≠ .W2) := by
  constructor
  · intro _ C F hrank
    exact construction_confession_exclusive C F hrank
  · intro row
    exact ⟨w1MethodRowSupported_implies_permitted_import (w1MethodRowSupported_holds row),
           w1MethodRowStatus_exact row,
           w1MethodRowRoute_ne_w0 row,
           w1MethodRowRoute_ne_w2 row⟩

end OperatorKO7.W1AscentStructuralIdentity
