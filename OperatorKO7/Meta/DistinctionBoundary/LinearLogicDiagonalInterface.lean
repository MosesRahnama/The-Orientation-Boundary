import OperatorKO7.Meta.DistinctionBoundary.CopyDiscardDeterminism
import OperatorKO7.Meta.ComparatorNecessity

/-!
# Finite copy/contraction interface for the diagonal comparison

This is the Lean-facing finite interface behind the paper's copy/contraction
reading. It proves only the finite copy-and-compare facts used by KO7; any
external linear-logic or Markov-category citation remains manuscript-side
background rather than an imported theorem.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.LinearLogicDiagonalInterface

open OperatorKO7 Trace
open MetaSN_KO7

/-- A finite contraction/copy surface with a discard map. -/
structure FiniteCopyContraction (X : Type) where
  copy : X -> X × X
  counit : X -> Unit
  copy_diag : forall x, copy x = (x, x)

/-- A comparison interface that first copies the input and then compares the two
copies. -/
structure CopyThenCompare (X : Type) where
  copySurface : FiniteCopyContraction X
  cmp : X × X -> Bool
  sound_diag : forall x, cmp (copySurface.copy x) = true

def traceContraction : FiniteCopyContraction Trace where
  copy := fun x => (x, x)
  counit := fun _ => ()
  copy_diag := fun _ => rfl

def traceCopyThenCompare : CopyThenCompare Trace where
  copySurface := traceContraction
  cmp := fun p => decide (p.1 = p.2)
  sound_diag := by
    intro x
    simp [traceContraction]

/-- The raw `eqW` diagonal violates copy-then-compare discipline: the copied
diagonal compares equal, yet the raw difference branch still emits a non-null
verdict. -/
theorem ko7_raw_difference_violates_copy_then_compare :
    traceCopyThenCompare.cmp (traceContraction.copy void) = true ∧
      Step (eqW void void) (integrate (merge void void)) ∧
      integrate (merge void void) ≠ void := by
  refine ⟨by rfl, Step.R_eq_diff void void, ?_⟩
  intro h
  cases h

/-- The guarded relation respects the copied diagonal: the positive comparison
is paired with refusal of the raw false-difference branch. -/
theorem safeStep_respects_copy_then_compare_diagonal :
    traceCopyThenCompare.cmp (traceContraction.copy void) = true ∧
      ¬ SafeStep (eqW void void) (integrate (merge void void)) := by
  refine ⟨by rfl, ?_⟩
  exact
    _root_.OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy.diagonal_false_formal_legitimacy_refused_at_void

/-- The copy-then-compare surface is backed by the already proven exact
comparator over the KO7 trace carrier. -/
theorem trace_copy_compare_matches_exact_comparator (a b : Trace) :
    traceCopyThenCompare.cmp (a, b) =
      (OperatorKO7.Meta.ComparatorNecessity.decidableEq_exactComparator Trace).cmp a b := by
  rfl

#print axioms ko7_raw_difference_violates_copy_then_compare
#print axioms safeStep_respects_copy_then_compare_diagonal
#print axioms trace_copy_compare_matches_exact_comparator

end OperatorKO7.Meta.DistinctionBoundary.LinearLogicDiagonalInterface
