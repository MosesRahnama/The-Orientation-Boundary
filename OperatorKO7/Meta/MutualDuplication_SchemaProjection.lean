import OperatorKO7.Meta.MutualDuplication_FiniteSchema

/-!
# Projection and Transparent Continuations for First-Class Mutual Schemas

This module lifts the existing delayed-cycle transparent-compositional and scalar-projection
continuations to the first-class finite-cycle mutual layer, then specializes those lifts back
to the first-class two-rule mutual schema.
-/

namespace OperatorKO7.MutualDuplicationFiniteSchema

open OperatorKO7.StepDuplicating

namespace KCycleSchema

/-- Transparent-compositional measures on the first-class finite-cycle mutual schema. -/
abbrev CompositionalMeasure {k : Nat} (S : KCycleSchema k) :=
  OperatorKO7.MutualDuplicationKNodeAbstract.CyclicDupSchema.CompositionalMeasure S

end KCycleSchema

namespace KCycleSystem

/-- The derived cycle-flow schema at the base node used by the finite-cycle projection lift. -/
def projectionSchemaAtZero {k : Nat} (Sys : KCycleSystem k) : StepDuplicatingSchema :=
  OperatorKO7.MutualDuplicationCycleFlow.toDupSchema
    (KCycleSchema.toNodeSchema Sys.toKCycleSchema (0 : Fin (k + 1))) (k + 1)

/-- The first-class finite-cycle contextual relation inherits the transparent-compositional
barrier from the abstract delayed-cycle layer. -/
theorem no_global_orients_ctx_transparent_compositional
    {k : Nat} {Sys : KCycleSystem k}
    (M : KCycleSchema.CompositionalMeasure Sys.toKCycleSchema)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  intro h
  exact
    (OperatorKO7.MutualDuplicationKNodeAbstract.CyclicDupSystem.no_global_orients_ctx_compositional_transparent_via_cycleFlow
      Sys.toKNodeWitness M htrans)
      (by
        intro a b hstep
        exact h hstep)

/-- The first-class finite-cycle contextual relation inherits the scalar-projection affine
continuation from the abstract delayed-cycle layer. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded
    {k : Nat} {Sys : KCycleSystem k} {α : Type}
    (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (A : StepDuplicatingSchema.AffineMeasure (projectionSchemaAtZero Sys))
    (hπ : ∀ t : Sys.T, π (μ t) = A.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ GlobalOrientsCtx Sys μ R := by
  intro h
  exact
    (OperatorKO7.MutualDuplicationKNodeAbstract.CyclicDupSystem.no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_via_cycleFlow
      (Sys := Sys.toKNodeWitness) (μ := μ) (R := R) (π := π)
      (hproj := hproj) (A := A) (hπ := hπ) (hunbounded := hunbounded))
      (by
        intro a b hstep
        exact h hstep)

end KCycleSystem

end OperatorKO7.MutualDuplicationFiniteSchema

namespace OperatorKO7.MutualDuplicationSchema

open OperatorKO7.StepDuplicating

namespace Schema

/-- The two-step derived cycle-flow schema attached to the first-class two-rule mutual schema. -/
def projectionSchema (S : Schema) : StepDuplicatingSchema :=
  OperatorKO7.MutualDuplicationCycleFlow.toDupSchema (toPrimarySchema S) 2

/-- Transparent-compositional measures on the first-class two-rule mutual schema. -/
structure CompositionalMeasure (S : Schema) where
  eval : S.T → Nat
  c_base : Nat
  c_succ : Nat → Nat
  c_wrap : Nat → Nat → Nat
  c_recur : Nat → Nat → Nat → Nat
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = c_succ (eval t)
  eval_wrap : ∀ x y, eval (S.wrap x y) = c_wrap (eval x) (eval y)
  eval_recurA : ∀ b s n, eval (S.recurA b s n) = c_recur (eval b) (eval s) (eval n)
  eval_recurB : ∀ b s n, eval (S.recurB b s n) = c_recur (eval b) (eval s) (eval n)
  wrap_subterm1 : ∀ x y, c_wrap x y > x
  wrap_subterm2 : ∀ x y, c_wrap x y > y

/-- Forget the second recursor and expose the primary compositional profile used by the
abstract delayed-cycle layer. -/
def CompositionalMeasure.toPrimaryMeasure {S : Schema} (M : CompositionalMeasure S) :
    StepDuplicatingSchema.CompositionalMeasure (toPrimarySchema S) where
  eval := M.eval
  c_base := M.c_base
  c_succ := M.c_succ
  c_wrap := M.c_wrap
  c_recur := M.c_recur
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recurA
  wrap_subterm1 := M.wrap_subterm1
  wrap_subterm2 := M.wrap_subterm2

end Schema

namespace System

/-- The first-class two-rule mutual contextual relation inherits the transparent-compositional
continuation directly from the abstract delayed-cycle layer. -/
theorem no_global_orients_ctx_transparent_compositional
    {Sys : System} (M : Schema.CompositionalMeasure Sys.toSchema)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  exact
    OperatorKO7.MutualDuplicationCycleFlow.no_global_orients_ctx_compositional_transparent
      (W := Sys.toCycleWitness) (CM := M.toPrimaryMeasure)
      (hcopies := by decide) (htrans := htrans)

/-- The first-class two-rule mutual contextual relation inherits the scalar-projection affine
continuation directly from the abstract delayed-cycle layer. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded
    {Sys : System} {α : Type}
    (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (A : StepDuplicatingSchema.AffineMeasure (Schema.projectionSchema Sys.toSchema))
    (hπ : ∀ t : Sys.T, π (μ t) = A.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ GlobalOrientsCtx Sys μ R := by
  exact
    OperatorKO7.MutualDuplicationCycleFlow.no_global_orients_ctx_of_scalar_projection_affine_of_unbounded
      (W := Sys.toCycleWitness) (μ := μ) (R := R) (π := π)
      (hproj := hproj) (A := A) (hπ := hπ) (hunbounded := hunbounded)

end System

end OperatorKO7.MutualDuplicationSchema
