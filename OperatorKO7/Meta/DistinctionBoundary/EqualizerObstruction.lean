import OperatorKO7.Meta.DistinctionBoundary.SemanticsPreservingMaximality
import OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.EqualizerObstruction

open OperatorKO7 Trace
open MetaSN_KO7
open OperatorKO7.Meta.DistinctionBoundary

structure ComparisonSquare where
  src : Trace
  leftVerdict : Trace
  rightVerdict : Trace
  leftStep : Step src leftVerdict
  rightStep : Step src rightVerdict

def SquareCommutes (S : ComparisonSquare) : Prop :=
  ∃ d, StepStar S.leftVerdict d ∧ StepStar S.rightVerdict d

def rawDiagonalSquare (a : Trace) : ComparisonSquare where
  src := eqW a a
  leftVerdict := void
  rightVerdict := integrate (merge a a)
  leftStep := Step.R_eq_refl a
  rightStep := Step.R_eq_diff a a

theorem raw_diagonal_square_fails (a : Trace) :
    ¬ SquareCommutes (rawDiagonalSquare a) :=
  void_integrate_merge_self_not_joinable a

structure GuardedSquare where
  src : Trace
  verdict : Trace
  step : SafeStep src verdict

def guardedDiagonalSquare : GuardedSquare where
  src := eqW void void
  verdict := void
  step := SafeStep.R_eq_refl void (by simp)

theorem guarded_diagonal_square_commutes :
    ∃ d, SafeStepStar guardedDiagonalSquare.verdict d ∧
      SafeStepStar guardedDiagonalSquare.verdict d :=
  ⟨void, SafeStepStar.refl void, SafeStepStar.refl void⟩

#print axioms raw_diagonal_square_fails
#print axioms guarded_diagonal_square_commutes

end OperatorKO7.Meta.DistinctionBoundary.EqualizerObstruction
