import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance

/-!
# Roadmap-stable bridge for the standalone five-role comparator

This is a thin public front over `IndependentClassicInstance`; it introduces no
second comparator relation or closure.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- Exact standalone comparator schema. -/
def classicPointedForkSchema := OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.exactClassicFork

/-- Terminal certificate at the concrete `base0` diagonal. -/
theorem classicPointedFork_terminal :
    TerminalDiagonal classicPointedForkSchema
      OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0 :=
  OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.classic_terminalDiagonal

/-- Marked pointed fork at the concrete standalone comparator diagonal. The
ambient recursive carrier is not claimed to be finite. -/
def classicPointedFork : PointedFork :=
  schemaPointedFork classicPointedForkSchema
    OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0
    classicPointedFork_terminal

/-- Canonical Fork3 embedding into the standalone comparator. -/
def classic_contains_fork3 := OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.classicFork3Embedding

/-- The embedding is injective. -/
theorem classic_contains_fork3_injective :
    Function.Injective classic_contains_fork3.toFun :=
  OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.classicFork3Embedding_injective

/-- Exact marked local-cone relation isomorphism. -/
noncomputable def classic_localCone_equiv_fork3 := OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.classicLocalConeIso

/-- Roadmap-stable nonvacuity witness. -/
theorem classicPointedFork_peak :
    OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Rel
      (OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.cmp
        OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0
        OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0)
      OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.eq ∧
    OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Rel
      (OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.cmp
        OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0
        OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.base0)
      OperatorKO7.Meta.SafeStep.DiagonalForkClassicInstance.Tm.diff :=
  OperatorKO7.Meta.DistinctionBoundary.MinimalFork.IndependentClassicInstance.classic_exact_peak_nonempty

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork

