import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.ExactDiagonalForkSchema

/-!
# Terminal verdicts force the exact diagonal break

Relation: `S.R`.
Closure: `Quantitative.Reach S.R`.
Property: terminal verdict unjoinability and exact local-confluence failure.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u
variable {T : Type u}

/-- Distinct normal diagonal verdicts are unjoinable in the exact closure. -/
theorem terminalDiagonal_verdicts_unjoinable
    (S : ExactDiagonalForkSchema T) (a : T) (h : TerminalDiagonal S a) :
    ¬ DiagonalVerdictsJoin S a := by
  rintro ⟨z, hzEq, hzDiff⟩
  have heq : z = S.Z := eq_of_normalForm_reach h.equal_normal hzEq
  have hdiff : z = S.D a a :=
    eq_of_normalForm_reach h.different_normal hzDiff
  exact h.verdicts_distinct (heq.symm.trans hdiff)

/-- Main exact breaker: terminal, distinct diagonal verdicts force failure of
local one-step joinability. No caller-supplied nonjoinability premise remains. -/
theorem localConfluence_fails_of_terminal_distinct
    (S : ExactDiagonalForkSchema T) (a : T) (h : TerminalDiagonal S a) :
    ¬ LocalJoinAt S (S.E a a) := by
  intro hlocal
  exact terminalDiagonal_verdicts_unjoinable S a h
    (hlocal (S.refl_rule a) (S.diff_rule a a))

/-- At a determined diagonal, local joinability is exactly verdict joinability. -/
theorem localJoin_iff_verdictsJoin_of_determined
    (S : ExactDiagonalForkSchema T) (a : T)
    (hdet : DiagonalDetermined S a) :
    LocalJoinAt S (S.E a a) ↔ DiagonalVerdictsJoin S a := by
  constructor
  · intro hlocal
    exact hlocal (S.refl_rule a) (S.diff_rule a a)
  · intro hj l r hl hr
    rcases hdet hl with hlEq | hlDiff
    · rcases hdet hr with hrEq | hrDiff
      · subst l; subst r
        exact exact_joinable_refl S.R S.Z
      · subst l; subst r
        exact hj
    · rcases hdet hr with hrEq | hrDiff
      · subst l; subst r
        exact exact_joinable_symm hj
      · subst l; subst r
        exact exact_joinable_refl S.R (S.D a a)

/-- A terminal determined diagonal is non-locally-confluent exactly because its
two verdicts are distinct terminal forms. -/
theorem determined_terminal_diagonal_not_localJoin
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a)
    (_hdet : DiagonalDetermined S a) :
    ¬ LocalJoinAt S (S.E a a) :=
  localConfluence_fails_of_terminal_distinct S a hterm

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
