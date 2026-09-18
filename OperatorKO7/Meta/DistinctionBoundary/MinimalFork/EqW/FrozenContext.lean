import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.GuardedRoot

/-!
# Context-stable repair I: freeze below the comparison constructor

In the minimal grammar every proper context is beneath an `eqW`. The frozen
strategy therefore admits guarded root comparison steps but no descent into
either comparison argument. This is deliberately *not* advertised as full
context rewriting.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Guarded comparison with both argument positions frozen. -/
inductive FrozenCtxStep : MiniEqWTerm → MiniEqWTerm → Prop where
  | root {s t : MiniEqWTerm} : MiniEqWGuardedRootStep s t → FrozenCtxStep s t

/-- Frozen-context steps are exactly guarded root steps. -/
theorem frozenCtxStep_iff_guardedRoot {s t : MiniEqWTerm} :
    FrozenCtxStep s t ↔ MiniEqWGuardedRootStep s t := by
  constructor
  · intro h
    cases h with
    | root hr => exact hr
  · exact FrozenCtxStep.root

/-- The frozen strategy is included in the unrestricted guarded context relation. -/
theorem frozenCtx_sub_guardedCtx {s t : MiniEqWTerm}
    (h : FrozenCtxStep s t) : MiniEqWGuardedCtxStep s t := by
  cases h with
  | root hr => exact MiniEqWGuardedCtxStep.root hr

/-- Frozen comparison is strongly normalizing. -/
theorem frozen_comparison_context_SN : WellFounded (flip FrozenCtxStep) := by
  apply wf_flip_of_nat_decrease miniEqWCount
  intro s t h
  exact miniEqW_guardedRoot_count_decreases ((frozenCtxStep_iff_guardedRoot).mp h)

/-- Frozen comparison is confluent at every source because it is relation-identical
to the already proved guarded root relation. -/
theorem frozen_comparison_context_confluent (source : MiniEqWTerm) :
    ConfluentAt FrozenCtxStep source := by
  apply confluentAt_of_functional
  intro s l r hl hr
  exact miniEqW_guardedRoot_functional
    ((frozenCtxStep_iff_guardedRoot).mp hl)
    ((frozenCtxStep_iff_guardedRoot).mp hr)

/-- The frozen strategy preserves all legal off-diagonal root verdicts. -/
theorem frozen_context_offDiagonal_preserved {a b : MiniEqWTerm}
    (hne : a ≠ b) : FrozenCtxStep (.eqW a b) .different :=
  FrozenCtxStep.root (MiniEqWGuardedRootStep.diff a b hne)

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
