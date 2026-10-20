import OperatorKO7.Meta.BoundaryObserver.FourTestTables

set_option autoImplicit false

/-!
# Random access code bounds

The average success of two answers is expressed through the refused weights of a four-test
table. Its score gives an equivalent inequality, and a shared observer enforces the
three-quarter bound.

Proof graph: `Audit/ledgers/boundary-theorem/BOUNDARY-THEOREM-MATH-COMPLETION-PROOF-GRAPH.md`, node N10.
Relation: finite four-test tables. Trust: kernel-only.
-/

namespace OperatorKO7.Meta.BoundaryObserver.RandomAccessCode

open OperatorKO7.Meta.BoundaryObserver.FourTestTables

/-- The mean success rate of the two answers is one minus half their total refused weight. -/
noncomputable def racSuccess (d : Table) : ℝ :=
  1 - (FourTestTables.refused0 d + FourTestTables.refused1 d) / 2

/-- The mean success rate equals one half plus one eighth of the four-test score. -/
theorem rac_success_eq_score (d : Table) :
    racSuccess d = (1 : ℝ) / 2 + FourTestTables.score d / 8 := by
  rw [FourTestTables.score_eq_refused]
  unfold racSuccess
  ring

/-- A table with a shared observer has mean answer success at most three quarters. -/
theorem rac_success_le_three_quarters {d : Table}
    (h : FourTestTables.HasObserver d) : racSuccess d ≤ (3 : ℝ) / 4 := by
  have hrefused : (1 : ℝ) / 2 ≤ FourTestTables.refused0 d + FourTestTables.refused1 d :=
    FourTestTables.observer_refused_ge_half h
  unfold racSuccess
  linarith

/-- The three-quarter success bound and score at most two are the same inequality for every table. -/
theorem rac_bound_iff_score_bound (d : Table) :
    racSuccess d ≤ (3 : ℝ) / 4 ↔ FourTestTables.score d ≤ 2 := by
  rw [rac_success_eq_score]
  constructor <;> intro h <;> linarith

end OperatorKO7.Meta.BoundaryObserver.RandomAccessCode

namespace OperatorKO7.Meta.BoundaryObserver.FourTestTables

/-- The two-answer random access code has mean success one half plus one eighth of the four-test score. -/
theorem rac_success_eq_half_add_score_div_eight (d : Table) :
    OperatorKO7.Meta.BoundaryObserver.RandomAccessCode.racSuccess d =
      (1 : ℝ) / 2 + score d / 8 := by
  exact OperatorKO7.Meta.BoundaryObserver.RandomAccessCode.rac_success_eq_score d

end OperatorKO7.Meta.BoundaryObserver.FourTestTables
