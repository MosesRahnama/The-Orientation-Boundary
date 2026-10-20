import OperatorKO7.Meta.Conjecture_Boundary

/-!
# Pure Head-Precedence Barrier

The family is deliberately narrow: its measure depends only on the outermost
constructor. The collapsing `merge_cancel` rule supplies the obstruction to a
global orientation.
-/

namespace OperatorKO7.PrecedenceBarrier

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.MetaConjectureBoundary

/-- Pure head-precedence measures: a term is ranked solely by its outermost constructor. -/
structure HeadPrecedenceFamily where
  rank : OpHead → Nat

/-- Evaluation for the pure head-precedence family. -/
def HeadPrecedenceFamily.eval (M : HeadPrecedenceFamily) : Trace → Nat :=
  headPrecedenceMeasure M.rank

/-- The collapsing `merge_cancel` branch prevents global orientation by this head-only family. -/
theorem no_global_step_orientation_headPrecedenceFamily (M : HeadPrecedenceFamily) :
    ¬ GlobalOrients M.eval (· < ·) := by
  simpa [HeadPrecedenceFamily.eval] using
    no_global_step_orientation_headPrecedence M.rank

end OperatorKO7.PrecedenceBarrier
