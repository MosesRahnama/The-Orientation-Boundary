import OperatorKO7.Meta.DistinctionBoundary.GodelObserverCollision

set_option autoImplicit false

/-!
# A side symbol at the Gödel pair

The side-symbol equivalence identifies the exact extra observation required to
license standard-model truth on the Gödel sentence and its negation.

The proof uses the existing provability collision and the retained-set lifting
criterion. It adds no incompleteness or arithmetic axioms.
-/

namespace OperatorKO7.Meta.BoundaryObserver.GodelPairSideSymbol

open OperatorKO7.Meta.DistinctionBoundary.GodelArith
open OperatorKO7.Meta.DistinctionBoundary.GodelObserverCollision
open OperatorKO7.Meta.OperationalInexpressibility

-- The imported declarations are checked at their full explicit types.

/-- The checker-undecided pair containing the Gödel sentence and its negation. -/
def godelPair : Set Formula :=
  {arithGodelSentence, Formula.not arithGodelSentence}

/--
The augmented provability observer licenses standard-model truth on the two
Gödel sentences exactly if its side coordinate distinguishes the sentences.
-/
theorem godel_pair_side_symbol_iff {C : Type} (s : Formula → C) :
    LiftOrRefuse.LicensedOn godelPair
        (Confusability.augmentObserver provabilityObserver s) truthTarget ↔
      s arithGodelSentence ≠ s (Formula.not arithGodelSentence) := by
  constructor
  · intro hlic
    rcases godel_lift_or_refuse s hlic with hleft | hright | hsep
    · exact False.elim (hleft (by simp [godelPair]))
    · exact False.elim (hright (by simp [godelPair]))
    · exact hsep
  · intro hsep x hx y hy hObs
    simp only [godelPair, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl
      · rfl
      · have hside :
            s arithGodelSentence = s (Formula.not arithGodelSentence) :=
          congrArg Prod.snd hObs
        exact False.elim (hsep hside)
    · rcases hy with rfl | rfl
      · have hside :
            s (Formula.not arithGodelSentence) = s arithGodelSentence :=
          congrArg Prod.snd hObs
        exact False.elim (hsep hside.symm)
      · rfl

/--
The Gödel pair has a provability collision, maximal refusals, the exact
side-symbol licensing criterion, and a provability-preserving transposition.
-/
theorem godel_pair_corollary :
    DirectGrammarBoundary.OperationallyInexpressibleAt provabilityObserver truthTarget
      arithGodelSentence (Formula.not arithGodelSentence) ∧
    (((∃ S : Set Formula,
          LiftOrRefuse.MaximalLicensedOn S provabilityObserver truthTarget ∧
          arithGodelSentence ∈ S ∧ Formula.not arithGodelSentence ∉ S) ∧
      ∃ T : Set Formula,
          LiftOrRefuse.MaximalLicensedOn T provabilityObserver truthTarget ∧
          Formula.not arithGodelSentence ∈ T ∧ arithGodelSentence ∉ T) ∧
      ¬ ∃ G : Set Formula,
          LiftOrRefuse.LicensedOn G provabilityObserver truthTarget ∧
          ∀ S : Set Formula, LiftOrRefuse.LicensedOn S provabilityObserver truthTarget → S ⊆ G) ∧
    (∀ (C : Type) (s : Formula → C),
      LiftOrRefuse.LicensedOn godelPair
        (Confusability.augmentObserver provabilityObserver s) truthTarget ↔
      s arithGodelSentence ≠ s (Formula.not arithGodelSentence)) ∧
    Equiv.swap arithGodelSentence (Formula.not arithGodelSentence) ∈
      LicenseStabilizer.licenseStabilizer provabilityObserver := by
  exact ⟨godel_provability_collision, godel_refusals,
    (fun C s => godel_pair_side_symbol_iff s), godel_swap_keeps_provability⟩


end OperatorKO7.Meta.BoundaryObserver.GodelPairSideSymbol
