import OperatorKO7.Meta.MaxBarrier_Schema

/-!
# The max-plus barrier at every offset

`no_max_orients_dup_step` in `BarrierPumpDischarge_Schema` blocks the class `MaxMeasure`, whose
right-wrapper offset is at least one. Theorem `thm:max-barrier` of the Orientation Boundary paper
states the barrier for the constructor-local max-plus equations alone, at `γ_w = 0` and with every
offset zero. This file proves that statement. The argument splits on the successor offset: at
offset zero the counter step leaves the measure unchanged, and a positive offset pumps the step
argument along the successor chain until its branch dominates; in both cases the wrapper returns at
least the value of its recursive argument.
-/

set_option autoImplicit false

namespace OperatorKO7.StepDuplicating
namespace StepDuplicatingSchema

/-- Theorem `thm:max-barrier`: no measure with the constructor-local max-plus equations orients the
duplicating step strictly at every argument, for every choice of offsets, `γ_w = 0` and every
offset zero included. -/
theorem no_maxPlus_orients_dup_step {S : StepDuplicatingSchema} (eval : S.T → Nat)
    (aS aW bW gW aR bR gR dR : Nat)
    (h_succ : ∀ t, eval (S.succ t) = aS + eval t)
    (h_wrap : ∀ x y, eval (S.wrap x y) = aW + max (bW + eval x) (gW + eval y))
    (h_recur : ∀ b s n,
      eval (S.recur b s n) = aR + max (bR + eval b) (max (gR + eval s) (dR + eval n))) :
    ¬ (∀ b s n : S.T, eval (S.wrap s (S.recur b s n)) < eval (S.recur b s (S.succ n))) := by
  intro h
  have hwrap : ∀ s r : S.T, eval r ≤ eval (S.wrap s r) := by
    intro s r
    rw [h_wrap s r]
    exact le_trans (Nat.le_add_left (eval r) gW)
      (le_trans (le_max_right (bW + eval s) (gW + eval r)) (Nat.le_add_left _ aW))
  have hstep : ∃ s : S.T,
      eval (S.recur S.base s (S.succ S.base)) ≤ eval (S.recur S.base s S.base) := by
    by_cases haS : aS = 0
    · have hsb : eval (S.succ S.base) = eval S.base := by
        rw [h_succ, haS, Nat.zero_add]
      refine ⟨S.base, le_of_eq ?_⟩
      simp only [h_recur, hsb]
    · have hk : ∀ k, k ≤ eval (succIter S k) := by
        intro k
        induction k with
        | zero => exact Nat.zero_le _
        | succ k ih =>
            simp only [succIter, h_succ]
            omega
      refine ⟨succIter S (max (bR + eval S.base) (dR + eval (S.succ S.base))), ?_⟩
      have hs := hk (max (bR + eval S.base) (dR + eval (S.succ S.base)))
      have h1 : bR + eval S.base ≤
          gR + eval (succIter S (max (bR + eval S.base) (dR + eval (S.succ S.base)))) :=
        le_trans (le_max_left _ _) (le_trans hs (Nat.le_add_left _ _))
      have h2 : dR + eval (S.succ S.base) ≤
          gR + eval (succIter S (max (bR + eval S.base) (dR + eval (S.succ S.base)))) :=
        le_trans (le_max_right _ _) (le_trans hs (Nat.le_add_left _ _))
      rw [h_recur, h_recur]
      apply Nat.add_le_add_left
      rw [max_eq_left h2, max_eq_right h1]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
  obtain ⟨s, hs⟩ := hstep
  have h1 := h S.base s S.base
  have h2 := hwrap s (S.recur S.base s S.base)
  omega

end StepDuplicatingSchema
end OperatorKO7.StepDuplicating
