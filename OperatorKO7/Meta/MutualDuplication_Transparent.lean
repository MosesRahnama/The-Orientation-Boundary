import OperatorKO7.Meta.MutualDuplication_General
import OperatorKO7.Meta.ScalarProjectionBarrier

/-!
# Transparent-compositional and projected SCC barriers

This module proves a transparent-compositional barrier for an alternating SCC
and a matrix-functional corollary obtained through a weighted scalar projection.
The matrix result applies to measures carrying the declared projection and
unbounded weighted-range hypotheses.
-/

namespace OperatorKO7.MutualDuplicationTransparent

open OperatorKO7.DependencyPairsFragment
open OperatorKO7.StepDuplicating
open OperatorKO7.MutualDuplicationGeneral

namespace AlternatingDupSchema

/-- Transparent-compositional measures on the alternating SCC schema. Both recursors share one
abstract compositional profile. -/
structure CompositionalMeasure (S : AlternatingDupSchema) where
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

/-- View the alternating transparent-compositional profile as a compositional measure for the
derived two-step schema. -/
def CompositionalMeasure.toDup2Measure {S : AlternatingDupSchema}
    (CM : CompositionalMeasure S) :
    StepDuplicatingSchema.CompositionalMeasure S.toDup2Schema where
  eval := CM.eval
  c_base := CM.c_base
  c_succ := fun x => CM.c_succ (CM.c_succ x)
  c_wrap := fun x y => CM.c_wrap x (CM.c_wrap x y)
  c_recur := CM.c_recur
  eval_base := CM.eval_base
  eval_succ := by
    intro t
    rw [show S.toDup2Schema.succ t = S.succ (S.succ t) by rfl]
    rw [CM.eval_succ, CM.eval_succ]
  eval_wrap := by
    intro x y
    rw [show S.toDup2Schema.wrap x y = S.wrap x (S.wrap x y) by rfl]
    rw [CM.eval_wrap, CM.eval_wrap]
  eval_recur := by
    intro b s n
    simpa [AlternatingDupSchema.toDup2Schema] using CM.eval_recurA b s n
  wrap_subterm1 := by
    intro x y
    exact CM.wrap_subterm1 x (CM.c_wrap x y)
  wrap_subterm2 := by
    intro x y
    exact lt_trans (CM.wrap_subterm2 x y) (CM.wrap_subterm2 x (CM.c_wrap x y))

/-- The derived two-step schema preserves transparency at the base point. -/
lemma succ_transparent_at_base_twice {S : AlternatingDupSchema}
    (CM : CompositionalMeasure S)
    (htrans : CM.c_succ CM.c_base = CM.c_base) :
    CM.toDup2Measure.c_succ CM.toDup2Measure.c_base = CM.toDup2Measure.c_base := by
  simp [CompositionalMeasure.toDup2Measure, htrans]

/-- Uniform orientation of the bounded SCC composites by a
transparent-successor compositional measure leads to a contradiction. -/
theorem no_compositional_orients_alternating_dup2_composite_transparent
    {S : AlternatingDupSchema} (CM : CompositionalMeasure S)
    (htrans : CM.c_succ CM.c_base = CM.c_base) :
    ¬ (∀ (b s n : S.T),
      CM.eval (S.wrap s (S.wrap s (S.recurA b s n))) <
        CM.eval (S.recurA b s (S.succ (S.succ n)))) := by
  simpa [AlternatingDupSchema.toDup2Schema, CompositionalMeasure.toDup2Measure] using
    (StepDuplicatingSchema.no_compositional_orients_dup_step_transparent_succ
      (S := S.toDup2Schema) (CM := CM.toDup2Measure)
      (succ_transparent_at_base_twice CM htrans))

/-- Global orientation of the minimal SCC context relation leads to a
contradiction when successor is transparent at the base point. -/
theorem no_global_orients_ctx_compositional_transparent
    {Sys : AlternatingDupSchema.AlternatingDupSystem}
    (CM : CompositionalMeasure (AlternatingDupSchema.AlternatingDupSystem.toAlternatingDupSchema Sys))
    (htrans : CM.c_succ CM.c_base = CM.c_base) :
    ¬ AlternatingDupSchema.GlobalOrientsCtx Sys CM.eval (· < ·) := by
  intro h
  have hcomp :
      ∀ (b s n : Sys.T),
        CM.eval (Sys.wrap s (Sys.wrap s (Sys.recurA b s n))) <
          CM.eval (Sys.recurA b s (Sys.succ (Sys.succ n))) := by
    intro b s n
    rcases AlternatingDupSchema.alternating_dup2_realized Sys b s n with ⟨u, h₁, h₂⟩
    have horient : DependencyPairsFragment.GlobalOrients (AlternatingDupSchema.StepCtx Sys) CM.eval (· < ·) := by
      intro a b hstep
      exact h hstep
    have hpath :
        Relation.TransGen (AlternatingDupSchema.StepCtx Sys)
          (Sys.recurA b s (Sys.succ (Sys.succ n)))
          (Sys.wrap s (Sys.wrap s (Sys.recurA b s n))) :=
      Relation.TransGen.tail (Relation.TransGen.single h₁) h₂
    exact
      DependencyPairsFragment.transGen_drop
        (R := AlternatingDupSchema.StepCtx Sys) (m := CM.eval) horient hpath
  exact
    no_compositional_orients_alternating_dup2_composite_transparent
      (S := AlternatingDupSchema.AlternatingDupSystem.toAlternatingDupSchema Sys) CM htrans hcomp

/-- Matrix-functional barrier obtained by applying the affine obstruction to
the supplied weighted scalar projection and unbounded-range witness. -/
theorem no_global_orients_ctx_matrixFunctional_of_projected_unbounded
    {Sys : AlternatingDupSchema.AlternatingDupSystem} {d : Nat}
    (M : StepDuplicatingSchema.MatrixFunctionalMeasure
      (AlternatingDupSchema.toDup2Schema
        (AlternatingDupSchema.AlternatingDupSystem.toAlternatingDupSchema Sys)) d)
    (hunbounded : StepDuplicatingSchema.HasUnboundedWeightedRange M) :
    ¬ DependencyPairsFragment.GlobalOrients
        (AlternatingDupSchema.StepCtx Sys) M.eval (fun u v => StepDuplicatingSchema.VecLt u v) := by
  intro h
  have hcomp :
      ∀ (b s n : Sys.T),
        StepDuplicatingSchema.weightedSum M.weight
            (M.eval (Sys.wrap s (Sys.wrap s (Sys.recurA b s n)))) <
          StepDuplicatingSchema.weightedSum M.weight
            (M.eval (Sys.recurA b s (Sys.succ (Sys.succ n)))) := by
    intro b s n
    rcases AlternatingDupSchema.alternating_dup2_realized Sys b s n with ⟨u, h₁, h₂⟩
    have horientScalar :
        DependencyPairsFragment.GlobalOrients
          (AlternatingDupSchema.StepCtx Sys)
          (fun t => StepDuplicatingSchema.weightedSum M.weight (M.eval t))
          (· < ·) := by
      intro x y hxy
      exact
        StepDuplicatingSchema.weightedSum_lt_of_vecLt
          M.h_weight_support (h hxy)
    have hpath :
        Relation.TransGen (AlternatingDupSchema.StepCtx Sys)
          (Sys.recurA b s (Sys.succ (Sys.succ n)))
          (Sys.wrap s (Sys.wrap s (Sys.recurA b s n))) :=
      Relation.TransGen.tail (Relation.TransGen.single h₁) h₂
    exact
      DependencyPairsFragment.transGen_drop
        (R := AlternatingDupSchema.StepCtx Sys)
        (m := fun t => StepDuplicatingSchema.weightedSum M.weight (M.eval t))
        horientScalar hpath
  exact
    StepDuplicatingSchema.no_affine_orients_dup_step_of_unbounded
      (S := AlternatingDupSchema.toDup2Schema
        (AlternatingDupSchema.AlternatingDupSystem.toAlternatingDupSchema Sys))
      (M := M.projectedAffine) hunbounded hcomp

end AlternatingDupSchema

end OperatorKO7.MutualDuplicationTransparent
