import OperatorKO7.Meta.MaxBarrier_Schema

/-!
This module proves barriers for an abstract carrier equipped with a strict natural-number
primary projection identified with a supplied MaxMeasure. Tropical algebra is motivational; the
formal results use only the displayed projection and max-barrier hypotheses.










-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Data record whose requirements are the fields displayed below.
-/
structure TropicalPrimaryMeasure (S : StepDuplicatingSchema) (β : Type) where
  eval : S.T → β
  lt : β → β → Prop
  primary : β → Nat
  projectedMax : MaxMeasure S
  primary_eq : ∀ t, primary (eval t) = projectedMax.eval t
  lt_strict_primary : ∀ {x y : β}, lt x y → primary x < primary y

/-- The displayed proposition follows from the stated hypotheses. -/
theorem no_tropical_primary_orients_dup_step_of_unbounded
    {S : StepDuplicatingSchema} {β : Type}
    (M : TropicalPrimaryMeasure S β)
    (hunbounded : HasUnboundedRangeMax M.projectedMax) :
    ¬ (∀ (b s n : S.T),
      M.lt (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hmax :
      ∀ b s n : S.T,
        M.projectedMax.eval (S.wrap s (S.recur b s n)) <
          M.projectedMax.eval (S.recur b s (S.succ n)) := by
    intro b s n
    have hlt := h b s n
    have hproj := M.lt_strict_primary hlt
    simpa [M.primary_eq] using hproj
  exact no_max_orients_dup_step_of_unbounded (S := S) M.projectedMax hunbounded hmax

/-- The displayed proposition follows from the stated hypotheses. -/
theorem no_tropical_primary_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} {β : Type}
    (M : TropicalPrimaryMeasure S β)
    (h_succ_const : 1 ≤ M.projectedMax.succ_const) :
    ¬ (∀ (b s n : S.T),
      M.lt (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hmax :
      ∀ b s n : S.T,
        M.projectedMax.eval (S.wrap s (S.recur b s n)) <
          M.projectedMax.eval (S.recur b s (S.succ n)) := by
    intro b s n
    have hlt := h b s n
    have hproj := M.lt_strict_primary hlt
    simpa [M.primary_eq] using hproj
  exact no_max_orients_dup_step_of_succ_pump (S := S) M.projectedMax h_succ_const hmax

/-- The displayed proposition follows from the stated hypotheses. -/
theorem no_tropical_primary_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} {β : Type}
    (M : TropicalPrimaryMeasure S β)
    (h_wrap_drift : 1 ≤ M.projectedMax.wrap_const + M.projectedMax.wrap_left) :
    ¬ (∀ (b s n : S.T),
      M.lt (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hmax :
      ∀ b s n : S.T,
        M.projectedMax.eval (S.wrap s (S.recur b s n)) <
          M.projectedMax.eval (S.recur b s (S.succ n)) := by
    intro b s n
    have hlt := h b s n
    have hproj := M.lt_strict_primary hlt
    simpa [M.primary_eq] using hproj
  exact no_max_orients_dup_step_of_wrap_pump (S := S) M.projectedMax h_wrap_drift hmax

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
