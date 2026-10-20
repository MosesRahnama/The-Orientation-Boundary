import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.FreeStepDuplicatingSyntax

/-!
This module proves a conditional barrier for finite-dimensional affine measures through one
tracked natural-number coordinate. Every projection, dominance, and pump hypothesis appears in
the theorem types. The last section inhabits the class `MatrixMeasureD` on the free
step-duplicating schema in dimension two and discharges every hypothesis of the three
conditional barriers at that inhabitant.








-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Strict componentwise order on `Fin d → Nat` vectors. -/
def VecLt {d : Nat} (u v : Fin d → Nat) : Prop :=
  ∀ i : Fin d, u i < v i

/-- Data record whose requirements are the fields displayed below. -/
structure MatrixMeasureD (S : StepDuplicatingSchema) (d : Nat) (tracked : Fin d) where
  eval : S.T → Fin d → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  eval_base : eval S.base tracked = c_base
  eval_succ :
    ∀ t, eval (S.succ t) tracked = succ_bias + succ_scale * eval t tracked
  eval_wrap :
    ∀ x y,
      eval (S.wrap x y) tracked =
        wrap_const + wrap_left * eval x tracked + wrap_right * eval y tracked
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) tracked =
        recur_const + recur_base * eval b tracked +
          recur_step * eval s tracked + recur_counter * eval n tracked
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Definition with formal content given by the displayed type and body. -/
def MatrixMeasureD.trackedAffine
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked) : AffineMeasure S where
  eval := fun t => M.eval t tracked
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := M.h_wrap_right_pos

/-- Definition with formal content given by the displayed type and body. -/
def HasUnboundedRangeTracked
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ M.eval t tracked

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem no_matrixD_orients_dup_step_of_componentwise_pump
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked)
    (hunbounded : HasUnboundedRangeTracked M) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have htracked :
      ∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) tracked <
          M.eval (S.recur b s (S.succ n)) tracked := by
    intro b s n
    exact h b s n tracked
  have hunbounded' : HasUnboundedRange M.trackedAffine := by
    intro k
    rcases hunbounded k with ⟨t, ht⟩
    exact ⟨t, ht⟩
  exact
    no_affine_orients_dup_step_of_unbounded
      (S := S) M.trackedAffine hunbounded' htracked

/-- The displayed proposition follows from the stated hypotheses. -/
theorem no_matrixD_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have htracked :
      ∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) tracked <
          M.eval (S.recur b s (S.succ n)) tracked := by
    intro b s n
    exact h b s n tracked
  exact
    no_affine_orients_dup_step_of_succ_pump
      (S := S) M.trackedAffine h_succ_bias h_succ_scale htracked

/-- The displayed proposition follows from the stated hypotheses. -/
theorem no_matrixD_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have htracked :
      ∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) tracked <
          M.eval (S.recur b s (S.succ n)) tracked := by
    intro b s n
    exact h b s n tracked
  exact
    no_affine_orients_dup_step_of_wrap_pump
      (S := S) M.trackedAffine h_wrap_bias htracked

/-- The displayed proposition follows from the stated hypotheses. -/
theorem no_global_orients_matrixD_of_componentwise_pump
    {Sys : StepDuplicatingSystem} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD Sys.toStepDuplicatingSchema d tracked)
    (hunbounded : HasUnboundedRangeTracked M) :
    ¬ GlobalOrients Sys M.eval VecLt := by
  intro h
  exact
    no_matrixD_orients_dup_step_of_componentwise_pump
      (S := Sys.toStepDuplicatingSchema) M hunbounded
      (fun b s n => h (Sys.dup_step b s n))

/-! ## An inhabitant on the free schema

Gate R5 witness for `MatrixMeasureD`. On the free step-duplicating syntax, coordinate `0` is the
structural size, an affine measure with every coefficient equal to one, and coordinate `1` is the
counter depth, which satisfies no affine wrapper equation. The untracked coordinate decreases at
every instance of the duplicating step, and the barrier excludes componentwise orientation through
the tracked coordinate alone. -/

/-- Structural size of a free term: one for each constructor occurrence.
Proves: nothing; a definition.
Scope: the free step-duplicating syntax `FreeTerm`. -/
def matrixDFreeSize : FreeTerm → Nat
  | .base => 1
  | .succ t => 1 + matrixDFreeSize t
  | .wrap x y => 1 + matrixDFreeSize x + matrixDFreeSize y
  | .recur b s n => 1 + matrixDFreeSize b + matrixDFreeSize s + matrixDFreeSize n

/-- Two-coordinate valuation of the free syntax: the size at coordinate `0` and the counter depth
`freeCounterDepth` at coordinate `1`.
Proves: nothing; a definition.
Scope: the free step-duplicating syntax, dimension two. -/
def matrixDFreeEval (t : FreeTerm) : Fin 2 → Nat :=
  fun i => if i = 0 then matrixDFreeSize t else freeCounterDepth t

/-- Inhabitant of `MatrixMeasureD freeSchema 2 0`.
Proves: the class of the tracked componentwise barrier is inhabited on the free schema; the
tracked coordinate is the size with every affine coefficient equal to one, and both wrapper
coefficients are positive.
Does not prove: any orientation of the duplicating step; `freeSizeMatrixMeasureD_not_orients`
excludes it.
Relation: none; a data record.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: the free step-duplicating schema, dimension two, tracked coordinate `0`; the untracked
coordinate is the counter depth and obeys no affine law. -/
def freeSizeMatrixMeasureD : MatrixMeasureD freeSchema 2 0 where
  eval := matrixDFreeEval
  c_base := 1
  succ_bias := 1
  succ_scale := 1
  wrap_const := 1
  wrap_left := 1
  wrap_right := 1
  recur_const := 1
  recur_base := 1
  recur_step := 1
  recur_counter := 1
  eval_base := rfl
  eval_succ := fun t => by simp [matrixDFreeEval, matrixDFreeSize, freeSchema]
  eval_wrap := fun x y => by simp [matrixDFreeEval, matrixDFreeSize, freeSchema]
  eval_recur := fun b s n => by simp [matrixDFreeEval, matrixDFreeSize, freeSchema]
  h_wrap_left_pos := le_refl 1
  h_wrap_right_pos := le_refl 1

/-- Proves: the tracked coordinate of `freeSizeMatrixMeasureD` is unbounded; the successor chain
`succIter freeSchema k` has tracked value at least `k`.
Does not prove: unboundedness of the untracked coordinate on a fixed chain.
Relation: none; a range statement.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: the inhabitant `freeSizeMatrixMeasureD`. -/
theorem freeSizeMatrixMeasureD_unboundedTracked :
    HasUnboundedRangeTracked freeSizeMatrixMeasureD :=
  fun k => ⟨succIter freeSchema k,
    eval_succIter_ge freeSizeMatrixMeasureD.trackedAffine (le_refl 1) (le_refl 1) k⟩

/-- Proves: every hypothesis of the three conditional barriers of this module holds at
`freeSizeMatrixMeasureD`: successor bias and scale at least one, wrapper bias at least one, and an
unbounded tracked coordinate. The hypotheses are therefore jointly satisfiable on the free schema.
Does not prove: any orientation.
Relation: none; hypothesis satisfiability.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: the inhabitant `freeSizeMatrixMeasureD`. -/
theorem freeSizeMatrixMeasureD_barrier_premises :
    1 ≤ freeSizeMatrixMeasureD.succ_bias ∧ 1 ≤ freeSizeMatrixMeasureD.succ_scale ∧
      1 ≤ freeSizeMatrixMeasureD.wrap_const +
        freeSizeMatrixMeasureD.wrap_right * freeSizeMatrixMeasureD.c_base ∧
      HasUnboundedRangeTracked freeSizeMatrixMeasureD :=
  ⟨le_refl 1, le_refl 1, show (1 : Nat) ≤ 1 + 1 * 1 by decide,
    freeSizeMatrixMeasureD_unboundedTracked⟩

/-- Proves: the untracked coordinate of `freeSizeMatrixMeasureD` (the counter depth) strictly
decreases at every instance of the duplicating step `recur b s (succ n) → wrap s (recur b s n)`.
Does not prove: componentwise orientation; the tracked coordinate blocks it.
Relation: the schema duplicating step at the root.
Closure: root. Strategy: not applicable.
Trust: kernel only.
Scope: the inhabitant `freeSizeMatrixMeasureD`, coordinate `1`. -/
theorem freeSizeMatrixMeasureD_untracked_decreases (b s n : freeSchema.T) :
    freeSizeMatrixMeasureD.eval (freeSchema.wrap s (freeSchema.recur b s n)) 1 <
      freeSizeMatrixMeasureD.eval (freeSchema.recur b s (freeSchema.succ n)) 1 := by
  show freeCounterDepth (FreeTerm.wrap s (FreeTerm.recur b s n)) <
    freeCounterDepth (FreeTerm.recur b s (FreeTerm.succ n))
  simp [freeCounterDepth]

/-- Proves: `freeSizeMatrixMeasureD` fails strict componentwise orientation of the duplicating
step, by `no_matrixD_orients_dup_step_of_componentwise_pump` with its unboundedness hypothesis
discharged at the inhabitant.
Does not prove: failure of the untracked coordinate; it decreases at every instance.
Relation: the schema duplicating step at the root, compared by `VecLt`.
Closure: root. Strategy: not applicable.
Trust: kernel only.
Scope: the inhabitant `freeSizeMatrixMeasureD`. -/
theorem freeSizeMatrixMeasureD_not_orients :
    ¬ (∀ (b s n : freeSchema.T),
      VecLt (freeSizeMatrixMeasureD.eval (freeSchema.wrap s (freeSchema.recur b s n)))
        (freeSizeMatrixMeasureD.eval (freeSchema.recur b s (freeSchema.succ n)))) :=
  no_matrixD_orients_dup_step_of_componentwise_pump freeSizeMatrixMeasureD
    freeSizeMatrixMeasureD_unboundedTracked

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
