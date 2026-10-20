import OperatorKO7.Meta.DistinctionBoundary.Quantitative.Core

/-!
# Canonical three-state distinction fork

This file defines the cardinality-minimal *shape* of a nonjoinable one-step peak.
It contains no KO7 syntax and no equality-witness assumptions.

Relation: `Fork3Step`.
Closure: `Quantitative.Reach Fork3Step`.
Strategy: the complete two-edge root relation on `Fork3`.
Trust: kernel checked; no external artifact or added axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- The canonical three-state carrier of a nonjoinable one-step peak. -/
inductive Fork3 where
  | source
  | equal
  | different
  deriving DecidableEq, Fintype, Repr

/-- Exactly the two outgoing edges of the canonical fork. -/
inductive Fork3Step : Fork3 → Fork3 → Prop where
  | toEqual : Fork3Step .source .equal
  | toDifferent : Fork3Step .source .different

/-- The equal verdict is terminal for `Fork3Step`. -/
theorem fork3_equal_normal : NormalForm Fork3Step .equal := by
  intro y h
  cases h

/-- The different verdict is terminal for `Fork3Step`. -/
theorem fork3_different_normal : NormalForm Fork3Step .different := by
  intro y h
  cases h

/-- The two terminal verdicts of `Fork3` are unjoinable in the exact closure. -/
theorem fork3_verdicts_unjoinable :
    ¬ Joinable Fork3Step .equal .different := by
  rintro ⟨z, hzEq, hzDiff⟩
  have hEq : z = .equal := eq_of_normalForm_reach fork3_equal_normal hzEq
  have hDiff : z = .different :=
    eq_of_normalForm_reach fork3_different_normal hzDiff
  exact Fork3.noConfusion (hEq.symm.trans hDiff)

/-- The source has both canonical one-step exits. -/
theorem fork3_source_peak :
    Fork3Step .source .equal ∧ Fork3Step .source .different :=
  ⟨Fork3Step.toEqual, Fork3Step.toDifferent⟩

/-- `Fork3` fails source confluence at its unique branching state. -/
theorem fork3_not_confluentAt_source :
    ¬ ConfluentAt Fork3Step .source := by
  intro hconf
  exact fork3_verdicts_unjoinable
    (hconf .equal .different
      (reach_step Fork3Step.toEqual)
      (reach_step Fork3Step.toDifferent))

/-- `Fork3` has exactly three carrier states. This uses kernel `decide`, not native evaluation. -/
theorem fork3_card_eq_three : Fintype.card Fork3 = 3 := by
  decide

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
