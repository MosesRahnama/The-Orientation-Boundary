import OperatorKO7.Meta.DistinctionBoundary.SemanticsPreservingMaximality

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.FiniteGluingObstruction

open OperatorKO7 Trace
open OperatorKO7.Meta.DistinctionBoundary

structure BranchCover where
  left : Trace
  right : Trace

structure LocalVerdictSection (C : BranchCover) where
  leftVerdict : Trace
  rightVerdict : Trace

def Glues {C : BranchCover} (S : LocalVerdictSection C) : Prop :=
  ∃ d, StepStar S.leftVerdict d ∧ StepStar S.rightVerdict d

def rawDiagonalSection (a : Trace) :
    LocalVerdictSection { left := void, right := integrate (merge a a) } where
  leftVerdict := void
  rightVerdict := integrate (merge a a)

def guardedDiagonalSection :
    LocalVerdictSection { left := void, right := void } where
  leftVerdict := void
  rightVerdict := void

theorem raw_diagonal_sections_fail_to_glue (a : Trace) :
    ¬ Glues (rawDiagonalSection a) :=
  void_integrate_merge_self_not_joinable a

theorem guarded_diagonal_sections_glue :
    Glues guardedDiagonalSection :=
  ⟨void, StepStar.refl void, StepStar.refl void⟩

#print axioms raw_diagonal_sections_fail_to_glue
#print axioms guarded_diagonal_sections_glue

end OperatorKO7.Meta.DistinctionBoundary.FiniteGluingObstruction
