import OperatorKO7.Meta.DistinctionBoundary.EqualizerObstruction
import OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.CopyDiscardDeterminism

open OperatorKO7 Trace
open MetaSN_KO7
open MetaSN_DM

structure CopyDiscardComparator where
  compare : Trace -> Trace -> Trace
  diagonalLaw : Prop

def rawEqWComparator : CopyDiscardComparator where
  compare := eqW
  diagonalLaw := ∀ a, Step (eqW a a) void ∧
    Step (eqW a a) (integrate (merge a a))

def safeEqWComparator : CopyDiscardComparator where
  compare := eqW
  diagonalLaw := ∀ a, kappaM a = 0 -> SafeStep (eqW a a) void ∧
    ¬ SafeStep (eqW a a) (integrate (merge a a))

theorem raw_comparator_violates_copy_discard_at_void :
    Step (eqW void void) void ∧
      Step (eqW void void) (integrate (merge void void)) ∧
      ¬ EqualizerObstruction.SquareCommutes
        (EqualizerObstruction.rawDiagonalSquare void) :=
  ⟨Step.R_eq_refl void, Step.R_eq_diff void void,
    EqualizerObstruction.raw_diagonal_square_fails void⟩

theorem safe_comparator_satisfies_diagonal_copy_discard :
    ∀ a : Trace, kappaM a = 0 -> SafeStep (eqW a a) void ∧
      ¬ SafeStep (eqW a a) (integrate (merge a a)) := by
  intro a h0
  refine ⟨SafeStep.R_eq_refl a h0, ?_⟩
  exact OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy.safeStep_refuses_false_formal_legitimacy
    a (integrate (merge a a)) ⟨rfl, fun h => h rfl⟩

#print axioms raw_comparator_violates_copy_discard_at_void
#print axioms safe_comparator_satisfies_diagonal_copy_discard

end OperatorKO7.Meta.DistinctionBoundary.CopyDiscardDeterminism
