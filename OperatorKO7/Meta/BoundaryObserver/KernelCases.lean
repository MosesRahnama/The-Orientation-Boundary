import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.DistinctionBoundary.GodelFixedPointSemantics

set_option autoImplicit false

/-!
# KernelCases: mathematical Gödel provability pair

Corollary 9.2 retains the original exact Gödel sentence, its negation,
its provability observer and all unconditional incompleteness assumptions.
The Trace and rewriting sections now live in Instances/KernelCases.lean.
-/

namespace OperatorKO7.Meta.BoundaryObserver.KernelCases

open OperatorKO7.Meta.BoundaryObserver.MergedPair

/-! ## Corollary 9.2: the provability pair -/

open OperatorKO7.Meta.DistinctionBoundary.GodelArith in
/-- No formula equals its own negation. The proof is by induction on the formula and unfolds no
particular formula. -/
theorem formula_ne_not (φ : Formula) : φ ≠ Formula.not φ := by
  induction φ with
  | eq t u => exact fun h => Formula.noConfusion h
  | not ψ ih => exact fun h => ih (Formula.not.inj h)
  | imp a b _ _ => exact fun h => Formula.noConfusion h
  | all n ψ _ => exact fun h => Formula.noConfusion h

open OperatorKO7.Meta.DistinctionBoundary.GodelArith in
/--
Corollary 9.2(i), the pair.

Proves: the sentence `arithGodelSentence` and its negation are distinct and have one record
under the observer "is provable by the checker".
Does not prove: the same for other proof systems.
Relation: none. Trust: kernel-only; the two unprovability facts are
`godel_first_incompleteness_Q_unconditional`.
-/
theorem godel_merged_pair :
    IsMergedPair (fun φ : Formula => Provable φ) arithGodelSentence
      (Formula.not arithGodelSentence) :=
  ⟨formula_ne_not arithGodelSentence,
    propext ⟨fun h => absurd h godel_first_incompleteness_Q_unconditional.1,
      fun h => absurd h godel_first_incompleteness_Q_unconditional.2⟩⟩

open OperatorKO7.Meta.DistinctionBoundary.GodelArith in
/-- Corollary 9.2(iii), both directions: on the sentence and its negation, provability together
with a side map `s` is injective if and only if `s` takes two values on the pair. -/
theorem godel_side_symbol_iff {S : Type*} (s : Formula → S) :
    Set.InjOn (fun φ : Formula => (Provable φ, s φ))
        ({arithGodelSentence, Formula.not arithGodelSentence} : Set Formula) ↔
      s arithGodelSentence ≠ s (Formula.not arithGodelSentence) :=
  mergedPair_side_symbol godel_merged_pair s

open OperatorKO7.Meta.DistinctionBoundary.GodelArith in
/-- Corollary 9.2(ii): a set of the two sentences carries an injective restriction of
provability if and only if it omits one of them. -/
theorem godel_restriction (T : Set Formula)
    (hT : T ⊆ ({arithGodelSentence, Formula.not arithGodelSentence} : Set Formula)) :
    Set.InjOn (fun φ : Formula => Provable φ) T ↔
      ¬ (arithGodelSentence ∈ T ∧ Formula.not arithGodelSentence ∈ T) :=
  mergedPair_restriction godel_merged_pair T hT

end OperatorKO7.Meta.BoundaryObserver.KernelCases
