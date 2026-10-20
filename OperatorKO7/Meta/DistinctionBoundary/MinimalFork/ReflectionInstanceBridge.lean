import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.UniversalEmbedding
import OperatorKO7.Meta.SafeStep.EqualityReflectionInstance

/-!
# Exact equality-reflection comparator instance

A second independent carrier realizes the same exact diagonal obstruction. The
legacy closure stored by the old instance is not used for the exact theorem.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork.ReflectionInstanceBridge

open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- Exact schema for the equality-reflection carrier. -/
def exactReflectionFork : ExactDiagonalForkSchema OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm where
  R := OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.EqReflectionRel
  E := OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.idQuery
  Z := OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.reflVerdict
  D := fun _ _ => OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.impossibleDiseqVerdict
  refl_rule := OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.EqReflectionRel.idRefl
  diff_rule := OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.EqReflectionRel.reflectedDiseq

/-- Equal verdict is exact-normal. -/
theorem reflection_equal_normal :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm
      OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.EqReflectionRel
      OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.reflVerdict := by
  intro y h
  cases h

/-- Difference verdict is exact-normal. -/
theorem reflection_diff_normal :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm
      OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.EqReflectionRel
      OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.impossibleDiseqVerdict := by
  intro y h
  cases h

/-- Terminal diagonal certificate. -/
theorem reflection_terminalDiagonal :
    TerminalDiagonal exactReflectionFork OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0 where
  equal_normal := reflection_equal_normal
  different_normal := reflection_diff_normal
  verdicts_distinct := by intro h; cases h

/-- The reflection diagonal has exactly the two declared one-step verdicts. -/
theorem reflection_diagonalDetermined :
    DiagonalDetermined exactReflectionFork OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0 := by
  intro t h
  cases h with
  | idRefl _ => exact Or.inl rfl
  | reflectedDiseq _ _ => exact Or.inr rfl

/-- Exact nonconfluence follows from terminal verdict separation. -/
theorem reflection_exact_localJoin_fails :
    ¬ LocalJoinAt exactReflectionFork
      (OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.idQuery OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0 OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0) :=
  localConfluence_fails_of_terminal_distinct
    exactReflectionFork OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0 reflection_terminalDiagonal

/-- Canonical `Fork3` embedding into equality reflection. -/
def reflectionFork3Embedding :=
  fork3Embedding exactReflectionFork OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0 reflection_terminalDiagonal

/-- The embedding is injective. -/
theorem reflectionFork3Embedding_injective :
    Function.Injective reflectionFork3Embedding.toFun :=
  fork3Embedding_injective exactReflectionFork OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0 reflection_terminalDiagonal

/-- Exact marked local cone relation isomorphism. -/
noncomputable def reflectionLocalConeIso :
    RelIso Fork3Step
      (LocalConeStep exactReflectionFork OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0 reflection_terminalDiagonal) :=
  determined_terminal_diagonal_localCone_equiv_fork3
    exactReflectionFork OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0 reflection_terminalDiagonal
    reflection_diagonalDetermined

/-- Concrete one-step peak witness. -/
theorem reflection_exact_peak_nonempty :
    OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.EqReflectionRel
      (OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.idQuery OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0 OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0)
      OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.reflVerdict ∧
    OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.EqReflectionRel
      (OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.idQuery OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0 OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.base0)
      OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.TyTerm.impossibleDiseqVerdict :=
  ⟨OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.EqReflectionRel.idRefl _, OperatorKO7.Meta.SafeStep.EqualityReflectionInstance.EqReflectionRel.reflectedDiseq _ _⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork.ReflectionInstanceBridge

