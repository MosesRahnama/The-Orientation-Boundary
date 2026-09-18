import OperatorKO7.Meta.LinearRec_Ablation
import OperatorKO7.Meta.TypedBarrierSurvival
import OperatorKO7.Meta.SharingBarrierLift

/-!
# Boundary Factorization

This module packages four ablation facts about the KO7 orientation barrier:

* removing step duplication dissolves the direct barrier;
* simple typing preserves the barrier in the stated typed variants;
* sharing-aware semantics can dissolve the tree-specific obstruction.

Their conjunction compares step-payload duplication under tree semantics within
the displayed variants. The result is an ablation package for these four
constructions rather than a universal causal classification.
-/

namespace OperatorKO7.BarrierFactorization

open OperatorKO7
open Trace

/-- Removing step duplication dissolves the direct barrier on the linearized
recursor variant. -/
theorem recursion_alone_not_sufficient_for_barrier :
    ∃ μ : Trace → Nat,
      ∀ {a b : Trace}, LinearStep a b → μ b < μ a := by
  refine ⟨simpleSize, ?_⟩
  intro a b h
  exact simpleSize_orients_linearStep h

/-- Simple typing preserves the additive direct-measure barrier in this typed
variant. -/
theorem simple_typing_not_escape_mechanism_additive :
    ∀ M : TypedBarrierSurvival.AdditiveMeasure,
      ¬ (∀ (b : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.res)
           (s : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.step)
           (n : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.cnt),
        M.evalRes (TypedBarrierSurvival.Term.wrap s (TypedBarrierSurvival.Term.recur b s n)) <
          M.evalRes (TypedBarrierSurvival.Term.recur b s (TypedBarrierSurvival.Term.succ n))) := by
  intro M
  exact TypedBarrierSurvival.no_additive_orients_typed_recSucc M

/-- The affine typed fragment also preserves the barrier once the step sort
admits an unbounded typed pump family. -/
theorem simple_typing_not_escape_mechanism_affine :
    ∀ M : TypedBarrierSurvival.AffineMeasure,
      TypedBarrierSurvival.HasTypedStepPump M →
        ¬ (∀ (b : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.res)
             (s : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.step)
             (n : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.cnt),
          M.evalRes (TypedBarrierSurvival.Term.wrap s (TypedBarrierSurvival.Term.recur b s n)) <
            M.evalRes (TypedBarrierSurvival.Term.recur b s (TypedBarrierSurvival.Term.succ n))) := by
  intro M hpump
  exact TypedBarrierSurvival.no_affine_orients_typed_recSucc_of_stepPump M hpump

/-- The `SharedTerm` surrogate supplies a sharing-aware witness whose direct
counter orients the displayed step. -/
theorem sharing_can_break_tree_barrier :
    ∀ b s n : SharingBarrierLift.SharedTerm,
      SharingBarrierLift.sharedCounter (SharingBarrierLift.SharedTerm.shareApp s
        (SharingBarrierLift.SharedTerm.recur b s n)) <
      SharingBarrierLift.sharedCounter (SharingBarrierLift.SharedTerm.recur b s
        (SharingBarrierLift.SharedTerm.succ n)) := by
  intro b s n
  exact SharingBarrierLift.sharing_breaks_tree_barrier b s n

/-- Conjunction of the linear-recursion witness, the two typed impossibility
results, and the `SharedTerm` surrogate witness. The proposition records these
four displayed variants as an ablation package. -/
theorem ko7_barrier_ablation_facts :
    (∃ μ : Trace → Nat,
        ∀ {a b : Trace}, LinearStep a b → μ b < μ a) ∧
      (∀ M : TypedBarrierSurvival.AdditiveMeasure,
        ¬ (∀ (b : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.res)
             (s : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.step)
             (n : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.cnt),
          M.evalRes (TypedBarrierSurvival.Term.wrap s (TypedBarrierSurvival.Term.recur b s n)) <
            M.evalRes (TypedBarrierSurvival.Term.recur b s (TypedBarrierSurvival.Term.succ n)))) ∧
      (∀ M : TypedBarrierSurvival.AffineMeasure,
        TypedBarrierSurvival.HasTypedStepPump M →
          ¬ (∀ (b : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.res)
               (s : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.step)
               (n : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.cnt),
            M.evalRes (TypedBarrierSurvival.Term.wrap s (TypedBarrierSurvival.Term.recur b s n)) <
              M.evalRes (TypedBarrierSurvival.Term.recur b s (TypedBarrierSurvival.Term.succ n)))) ∧
      (∀ b s n : SharingBarrierLift.SharedTerm,
        SharingBarrierLift.sharedCounter (SharingBarrierLift.SharedTerm.shareApp s
          (SharingBarrierLift.SharedTerm.recur b s n)) <
        SharingBarrierLift.sharedCounter (SharingBarrierLift.SharedTerm.recur b s
          (SharingBarrierLift.SharedTerm.succ n))) := by
  exact ⟨recursion_alone_not_sufficient_for_barrier,
    simple_typing_not_escape_mechanism_additive,
    simple_typing_not_escape_mechanism_affine,
    sharing_can_break_tree_barrier⟩

end OperatorKO7.BarrierFactorization
