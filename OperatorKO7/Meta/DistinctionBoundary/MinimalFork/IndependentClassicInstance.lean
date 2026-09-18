import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.UniversalEmbedding
import OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance

/-!
# Exact independent five-role comparator instance

This file reuses only the standalone comparator carrier/relation from
`DiagonalForkClassicInstance`; it does not reuse that file's legacy closure
claim. The exact schema below fixes joinability to `Quantitative.Reach Rel`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance

open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- Exact schema for the independent role-separated comparator. -/
def exactClassicFork : ExactDiagonalForkSchema OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm where
  R := OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Rel
  E := OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.cmp
  Z := OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.eq
  D := fun _ _ => OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.diff
  refl_rule := OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Rel.cmpRefl
  diff_rule := OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Rel.cmpDiff

/-- Equal verdict is normal in the exact one-step relation. -/
theorem classic_eq_normal :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm
      OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Rel
      OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.eq := by
  intro y h
  cases h

/-- Difference verdict is normal in the exact one-step relation. -/
theorem classic_diff_normal :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm
      OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Rel
      OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.diff := by
  intro y h
  cases h

/-- Exact terminal diagonal certificate at `base0`. -/
theorem classic_terminalDiagonal : TerminalDiagonal exactClassicFork OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 where
  equal_normal := classic_eq_normal
  different_normal := classic_diff_normal
  verdicts_distinct := by intro h; cases h

/-- The independent comparator has no third one-step output on its diagonal. -/
theorem classic_diagonalDetermined :
    DiagonalDetermined exactClassicFork OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 := by
  intro t h
  cases h with
  | cmpRefl _ => exact Or.inl rfl
  | cmpDiff _ _ => exact Or.inr rfl

/-- Exact nonconfluence of the independent comparator, obtained from the schema crown. -/
theorem classic_exact_localJoin_fails :
    ¬ LocalJoinAt exactClassicFork (OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.cmp OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0) :=
  localConfluence_fails_of_terminal_distinct
    exactClassicFork OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 classic_terminalDiagonal

/-- Canonical `Fork3` embedding into the independent comparator. -/
def classicFork3Embedding :=
  fork3Embedding exactClassicFork OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 classic_terminalDiagonal

/-- The embedding is injective. -/
theorem classicFork3Embedding_injective :
    Function.Injective classicFork3Embedding.toFun :=
  fork3Embedding_injective exactClassicFork OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 classic_terminalDiagonal

/-- The exact marked local cone is relation-isomorphic to `Fork3`. -/
noncomputable def classicLocalConeIso :
    RelIso Fork3Step (LocalConeStep exactClassicFork OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 classic_terminalDiagonal) :=
  determined_terminal_diagonal_localCone_equiv_fork3
    exactClassicFork OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 classic_terminalDiagonal classic_diagonalDetermined

/-- Concrete nonvacuity witness. -/
theorem classic_exact_peak_nonempty :
    OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Rel (OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.cmp OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0) OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.eq ∧
    OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Rel (OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.cmp OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0) OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.diff :=
  ⟨OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Rel.cmpRefl _, OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Rel.cmpDiff _ _⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance

