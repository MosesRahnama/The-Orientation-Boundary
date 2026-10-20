import OperatorKO7.Meta.DistinctionBoundary.GodelFixedPointSemantics
import OperatorKO7.Meta.BoundaryGeneral.TwoVoidBoundary

set_option autoImplicit false

/-!
# The Gödel sentence as a collision of provability against truth

Observer: whether the compiled arithmetic checker proves a sentence. Target: truth of the
sentence in the standard model at the zero environment. The Gödel sentence and its negation have
one observation and two target values, so the lift-or-refuse theorems apply to them.

The collision is the first incompleteness theorem of `GodelFixedPointSemantics.lean` restated;
this module adds no new proof of incompleteness. It applies the observer calculus to that
collision.

Proof graph: `Audit/ledgers/operational-inexpressibility/TWO-VOIDS-PROOF-GRAPH.md`, node G2.

Relation: `Provable` of the checker in `GodelRobinsonQ.lean`; no rewriting relation.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelObserverCollision

open OperatorKO7.Meta.DistinctionBoundary.GodelArith
open OperatorKO7.Meta.OperationalInexpressibility

/-- The observer: whether the checker proves the sentence. -/
def provabilityObserver (φ : Formula) : Prop := Provable φ

/-- The target: truth in the standard model at the zero environment. -/
def truthTarget (φ : Formula) : Prop := evalForm env0 φ

/-- The Gödel sentence is true. -/
theorem godel_sentence_true : truthTarget arithGodelSentence :=
  eval_arithGodelSentence_iff_not_provable.2 godel_first_incompleteness_Q_unconditional.1

/-- The negation of the Gödel sentence is false. -/
theorem godel_negation_false : ¬ truthTarget (Formula.not arithGodelSentence) := by
  intro h
  exact h godel_sentence_true

/--
**The Gödel collision.** The checker proves neither the Gödel sentence nor its negation, so the
provability observer gives them one observation; truth gives them two values.

Proves: one observation and two target values on this pair.
Does not prove: incompleteness by a new route; the two unprovability facts are imported.
-/
theorem godel_provability_collision :
    DirectGrammarBoundary.OperationallyInexpressibleAt provabilityObserver truthTarget
      arithGodelSentence (Formula.not arithGodelSentence) := by
  refine ⟨?_, ?_⟩
  · exact propext
      ⟨fun h => absurd h godel_first_incompleteness_Q_unconditional.1,
        fun h => absurd h godel_first_incompleteness_Q_unconditional.2⟩
  · intro h
    exact godel_negation_false (Eq.mp h godel_sentence_true)

/-- Truth has no licence through provability. -/
theorem truth_not_licensed_by_provability :
    ¬ LicenseCriterion.Licensed provabilityObserver truthTarget := fun h =>
  godel_provability_collision.2 (h _ _ godel_provability_collision.1)

/-- Refusal: each of the two sentences lies in a largest kept set that leaves the other out, and
no kept set is the greatest. -/
theorem godel_refusals :
    ((∃ S : Set Formula, LiftOrRefuse.MaximalLicensedOn S provabilityObserver truthTarget ∧
          arithGodelSentence ∈ S ∧ Formula.not arithGodelSentence ∉ S) ∧
        ∃ T : Set Formula, LiftOrRefuse.MaximalLicensedOn T provabilityObserver truthTarget ∧
          Formula.not arithGodelSentence ∈ T ∧ arithGodelSentence ∉ T) ∧
      ¬ ∃ G : Set Formula, LiftOrRefuse.LicensedOn G provabilityObserver truthTarget ∧
          ∀ S : Set Formula, LiftOrRefuse.LicensedOn S provabilityObserver truthTarget → S ⊆ G :=
  ⟨LiftOrRefuse.maximal_refusals_of_collision godel_provability_collision,
    LiftUniversalProperty.no_greatest_licensedOn_of_collision godel_provability_collision⟩

/-- Lift: a kept set under any side symbol leaves out one of the two sentences, or the symbol
separates them. -/
theorem godel_lift_or_refuse {C : Type} (s : Formula → C) {S : Set Formula}
    (h : LiftOrRefuse.LicensedOn S (Confusability.augmentObserver provabilityObserver s)
      truthTarget) :
    arithGodelSentence ∉ S ∨ Formula.not arithGodelSentence ∉ S ∨
      s arithGodelSentence ≠ s (Formula.not arithGodelSentence) :=
  LiftOrRefuse.collision_lifted_or_refused godel_provability_collision s h

/-- The swap of the Gödel sentence and its negation keeps every provability observation. -/
theorem godel_swap_keeps_provability :
    Equiv.swap arithGodelSentence (Formula.not arithGodelSentence) ∈
      LicenseStabilizer.licenseStabilizer provabilityObserver :=
  OperatorKO7.Meta.BoundaryGeneral.TwoVoidBoundary.swap_mem_licenseStabilizer provabilityObserver
    godel_provability_collision.1

end OperatorKO7.Meta.DistinctionBoundary.GodelObserverCollision
