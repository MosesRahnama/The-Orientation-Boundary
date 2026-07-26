import OperatorKO7.Meta.StepDuplicatingSchema

/-!
This module proves a conditional barrier for finite-dimensional affine measures through one
tracked natural-number coordinate. Every projection, dominance, and pump hypothesis appears in
the theorem types.








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

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
