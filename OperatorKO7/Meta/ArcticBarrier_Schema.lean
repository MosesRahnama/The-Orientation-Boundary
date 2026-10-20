import OperatorKO7.Meta.MaxBarrier_Schema

/-!
# Arctic projection barrier

`ArcticPrimaryMeasure` embeds a `MaxMeasure` into the finite `ArcticNat` carrier. The results below transfer the max-barrier obstruction to `ArcticLt` under unbounded-range, successor-pump, and wrap-pump hypotheses.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Minimal finite/bottom carrier for arctic-style projections. -/
inductive ArcticNat where
  | bot
  | fin : Nat → ArcticNat
deriving DecidableEq, Repr

/-- Comparison on a distinguished finite arctic coordinate. -/
def ArcticLt : ArcticNat → ArcticNat → Prop
  | ArcticNat.fin x, ArcticNat.fin y => x < y
  | _, _ => False

/-- An arctic measure whose values equal the finite projection of a `MaxMeasure`. -/
structure ArcticPrimaryMeasure (S : StepDuplicatingSchema) where
  eval : S.T → ArcticNat
  projectedMax : MaxMeasure S
  eval_eq_fin : ∀ t, eval t = ArcticNat.fin (projectedMax.eval t)

/-- An unbounded range for the max projection rules out strict orientation in `ArcticLt`. -/
theorem no_arctic_primary_orients_dup_step_of_unbounded
    {S : StepDuplicatingSchema} (M : ArcticPrimaryMeasure S)
    (hunbounded : HasUnboundedRangeMax M.projectedMax) :
    ¬ (∀ (b s n : S.T),
      ArcticLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hmax :
      ∀ b s n : S.T,
        M.projectedMax.eval (S.wrap s (S.recur b s n)) <
          M.projectedMax.eval (S.recur b s (S.succ n)) := by
    intro b s n
    simpa [ArcticLt, M.eval_eq_fin] using h b s n
  exact no_max_orients_dup_step_of_unbounded (S := S) M.projectedMax hunbounded hmax

/-- A successor constant of at least one rules out strict orientation in `ArcticLt`. -/
theorem no_arctic_primary_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} (M : ArcticPrimaryMeasure S)
    (h_succ_const : 1 ≤ M.projectedMax.succ_const) :
    ¬ (∀ (b s n : S.T),
      ArcticLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hmax :
      ∀ b s n : S.T,
        M.projectedMax.eval (S.wrap s (S.recur b s n)) <
          M.projectedMax.eval (S.recur b s (S.succ n)) := by
    intro b s n
    simpa [ArcticLt, M.eval_eq_fin] using h b s n
  exact no_max_orients_dup_step_of_succ_pump (S := S) M.projectedMax h_succ_const hmax

/-- The stated wrap drift rules out strict orientation in `ArcticLt`. -/
theorem no_arctic_primary_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} (M : ArcticPrimaryMeasure S)
    (h_wrap_drift : 1 ≤ M.projectedMax.wrap_const + M.projectedMax.wrap_left) :
    ¬ (∀ (b s n : S.T),
      ArcticLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hmax :
      ∀ b s n : S.T,
        M.projectedMax.eval (S.wrap s (S.recur b s n)) <
          M.projectedMax.eval (S.recur b s (S.succ n)) := by
    intro b s n
    simpa [ArcticLt, M.eval_eq_fin] using h b s n
  exact no_max_orients_dup_step_of_wrap_pump (S := S) M.projectedMax h_wrap_drift hmax

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
