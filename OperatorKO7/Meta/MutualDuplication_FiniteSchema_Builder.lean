import OperatorKO7.Meta.MutualDuplication_FiniteSchema

/-!
# Arbitrary Finite-Cycle Builder Interface

This module exposes the missing constructor-side hypothesis for arbitrary finite-cycle
mutual-recursion systems as a standalone builder record. The builder surface is then
transported into the existing first-class finite-cycle theorem stack.
-/

namespace OperatorKO7.MutualDuplicationFiniteSchema

open OperatorKO7.StepDuplicating

namespace FiniteCycleBuilder

/-- One-step advancement on the finite cycle index. -/
def advance {k : Nat} (i : Fin (k + 1)) : Fin (k + 1) where
  val := (i.1 + 1) % (k + 1)
  isLt := Nat.mod_lt _ (Nat.succ_pos _)

/-- Constructor-side interface for an arbitrary finite-cycle mutual-recursion witness. -/
structure Builder (k : Nat) where
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recur : Fin (k + 1) → T → T → T → T
  Step : T → T → Prop
  step_succ :
    ∀ (i : Fin (k + 1)) b s n,
      Step (recur i b s (succ n)) (wrap s (recur (advance i) b s n))

/-- Forget the builder witnesses and expose the first-class finite-cycle schema. -/
def Builder.toKCycleSchema {k : Nat} (B : Builder k) : KCycleSchema k where
  T := B.T
  base := B.base
  succ := B.succ
  wrap := B.wrap
  recur := B.recur

/-- Realize the builder as a first-class finite-cycle system. -/
def Builder.toKCycleSystem {k : Nat} (B : Builder k) : KCycleSystem k where
  T := B.T
  base := B.base
  succ := B.succ
  wrap := B.wrap
  recur := B.recur
  Step := B.Step
  step_succ := by
    intro i b s n
    simpa [Builder.toKCycleSchema, advance,
      OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.advance] using B.step_succ i b s n

/-- Contextual reachability relation carried by the realized finite-cycle system. -/
abbrev Builder.StepCtx {k : Nat} (B : Builder k) : B.T → B.T → Prop :=
  KCycleSystem.StepCtx B.toKCycleSystem

/-- Contextual strict-orientation predicate carried by the realized finite-cycle system. -/
def Builder.GlobalOrientsCtx {k : Nat} {α : Type} (B : Builder k) (m : B.T → α)
    (lt : α → α → Prop) : Prop :=
  KCycleSystem.GlobalOrientsCtx B.toKCycleSystem m lt

/-- The affine one-cycle witness at node `i` induced by the builder realization. -/
abbrev Builder.KCycleAffineAt {k : Nat} {B : Builder k}
    (i : Fin (k + 1)) (M : KCycleSchema.AffineMeasure B.toKCycleSystem.toKCycleSchema) :=
  KCycleSystem.KCycleAffineAt i M

/-- The affine one-cycle witness at node `0` induced by the builder realization. -/
abbrev Builder.KCycleAffineAtZero {k : Nat} {B : Builder k}
    (M : KCycleSchema.AffineMeasure B.toKCycleSystem.toKCycleSchema) :=
  KCycleSystem.KCycleAffineAtZero M

/-- Every builder instance realizes its finite-cycle path at every node. -/
theorem Builder.cycle_realized_at
    {k : Nat} (B : Builder k) (i : Fin (k + 1)) (b s n : B.T) :
    Relation.TransGen (B.StepCtx)
      (KCycleSchema.cycleSource B.toKCycleSystem.toKCycleSchema i b s n)
      (KCycleSchema.cycleTarget B.toKCycleSystem.toKCycleSchema i b s n) := by
  exact KCycleSystem.cycle_realized_via_kNode B.toKCycleSystem i b s n

/-- The additive contextual barrier holds for every builder realization. -/
theorem Builder.no_global_orients_ctx_additive
    {k : Nat} {B : Builder k}
    (M : KCycleSchema.AdditiveMeasure B.toKCycleSystem.toKCycleSchema) :
    ¬ B.GlobalOrientsCtx M.eval (· < ·) := by
  exact KCycleSystem.no_global_orients_ctx_additive M

/-- The arbitrary-node affine contextual barrier holds for every builder realization once the
corresponding one-cycle affine witness is unbounded. -/
theorem Builder.no_global_orients_ctx_affine_of_unbounded_at
    {k : Nat} {B : Builder k}
    (M : KCycleSchema.AffineMeasure B.toKCycleSystem.toKCycleSchema)
    (i : Fin (k + 1))
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange (B.KCycleAffineAt i M)) :
    ¬ B.GlobalOrientsCtx M.eval (· < ·) := by
  exact KCycleSystem.no_global_orients_ctx_affine_of_unbounded_at M i hunbounded

/-- Node-`0` compatibility wrapper for the builder-side affine contextual barrier. -/
theorem Builder.no_global_orients_ctx_affine_of_unbounded
    {k : Nat} {B : Builder k}
    (M : KCycleSchema.AffineMeasure B.toKCycleSystem.toKCycleSchema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange (B.KCycleAffineAtZero M)) :
    ¬ B.GlobalOrientsCtx M.eval (· < ·) := by
  exact KCycleSystem.no_global_orients_ctx_affine_of_unbounded M hunbounded

end FiniteCycleBuilder

end OperatorKO7.MutualDuplicationFiniteSchema
