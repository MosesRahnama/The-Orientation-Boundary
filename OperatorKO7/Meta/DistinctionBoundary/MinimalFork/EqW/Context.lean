import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.Root

/-!
# Unrestricted contextual closures of the minimal equality-witness relations

Both argument positions beneath every `eqW` are active. These inductive
relations are the explicit contextual closures used by the scope-wall theorem;
no root theorem is silently promoted to context rewriting.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- Full contextual closure of the raw two-rule root relation. -/
inductive MiniEqWCtxStep : MiniEqWTerm → MiniEqWTerm → Prop where
  | root {s t : MiniEqWTerm} : MiniEqWRootStep s t → MiniEqWCtxStep s t
  | left {a a' b : MiniEqWTerm} : MiniEqWCtxStep a a' →
      MiniEqWCtxStep (.eqW a b) (.eqW a' b)
  | right {a b b' : MiniEqWTerm} : MiniEqWCtxStep b b' →
      MiniEqWCtxStep (.eqW a b) (.eqW a b')

/-- Full contextual closure of the guarded root relation. -/
inductive MiniEqWGuardedCtxStep : MiniEqWTerm → MiniEqWTerm → Prop where
  | root {s t : MiniEqWTerm} : MiniEqWGuardedRootStep s t →
      MiniEqWGuardedCtxStep s t
  | left {a a' b : MiniEqWTerm} : MiniEqWGuardedCtxStep a a' →
      MiniEqWGuardedCtxStep (.eqW a b) (.eqW a' b)
  | right {a b b' : MiniEqWTerm} : MiniEqWGuardedCtxStep b b' →
      MiniEqWGuardedCtxStep (.eqW a b) (.eqW a b')

/-- Raw root steps embed into raw context rewriting. -/
theorem miniEqW_root_to_context {s t : MiniEqWTerm}
    (h : MiniEqWRootStep s t) : MiniEqWCtxStep s t :=
  MiniEqWCtxStep.root h

/-- Guarded root steps embed into guarded context rewriting. -/
theorem miniEqW_guardedRoot_to_context {s t : MiniEqWTerm}
    (h : MiniEqWGuardedRootStep s t) : MiniEqWGuardedCtxStep s t :=
  MiniEqWGuardedCtxStep.root h

/-- The guarded context relation remains a subrelation of raw context rewriting. -/
theorem miniEqW_guardedCtx_sub_rawCtx
    {s t : MiniEqWTerm} (h : MiniEqWGuardedCtxStep s t) :
    MiniEqWCtxStep s t := by
  induction h with
  | root hr => exact MiniEqWCtxStep.root (miniEqW_guardedRoot_sub_raw hr)
  | left _ ih => exact MiniEqWCtxStep.left ih
  | right _ ih => exact MiniEqWCtxStep.right ih

/-- Congruence in the left argument for one raw context step. -/
theorem miniEqW_ctx_left {a a' b : MiniEqWTerm}
    (h : MiniEqWCtxStep a a') :
    MiniEqWCtxStep (.eqW a b) (.eqW a' b) :=
  MiniEqWCtxStep.left h

/-- Congruence in the right argument for one raw context step. -/
theorem miniEqW_ctx_right {a b b' : MiniEqWTerm}
    (h : MiniEqWCtxStep b b') :
    MiniEqWCtxStep (.eqW a b) (.eqW a b') :=
  MiniEqWCtxStep.right h

/-- Congruence in the left argument for one guarded context step. -/
theorem miniEqW_guardedCtx_left {a a' b : MiniEqWTerm}
    (h : MiniEqWGuardedCtxStep a a') :
    MiniEqWGuardedCtxStep (.eqW a b) (.eqW a' b) :=
  MiniEqWGuardedCtxStep.left h

/-- Congruence in the right argument for one guarded context step. -/
theorem miniEqW_guardedCtx_right {a b b' : MiniEqWTerm}
    (h : MiniEqWGuardedCtxStep b b') :
    MiniEqWGuardedCtxStep (.eqW a b) (.eqW a b') :=
  MiniEqWGuardedCtxStep.right h

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
