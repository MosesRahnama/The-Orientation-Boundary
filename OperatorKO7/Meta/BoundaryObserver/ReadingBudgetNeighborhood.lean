import OperatorKO7.Meta.BoundaryObserver.StochasticGraph

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.ReadingBudgetNeighborhood

/-- Every finite budget and positive information target determine a positive explicit signal radius. -/
theorem budget_radius_pos (B : ℕ) (c : ℝ) (hc : 0 < c) :
    0 < min (1 / 2 : ℝ) (c / (4 * ((B : ℝ) + 1))) := by
  have hd : (0 : ℝ) < 4 * ((B : ℝ) + 1) := by positivity
  exact lt_min (by norm_num) (div_pos hc hd)

/-- Every reading count within a finite budget falls below a positive information target
inside the explicit radius, including a zero reading count and a zero signal. -/
theorem bounded_budget_fails_explicit (B : ℕ) (c ε : ℝ) (h0 : 0 ≤ ε)
    (hε : ε < min (1 / 2 : ℝ) (c / (4 * ((B : ℝ) + 1)))) :
    ∀ N ≤ B, StochasticGraph.readingsInformation N ε < c := by
  have hd : (0 : ℝ) < 4 * ((B : ℝ) + 1) := by positivity
  intro N hN
  have hhalf : ε < 1 / 2 := hε.trans_le (min_le_left _ _)
  have hsmall : ε < c / (4 * ((B : ℝ) + 1)) :=
    hε.trans_le (min_le_right _ _)
  have hscaled := (lt_div_iff₀ hd).mp hsmall
  have hn : (N : ℝ) ≤ B := by exact_mod_cast hN
  have heps : ε ^ 2 ≤ ε := by nlinarith
  calc
    StochasticGraph.readingsInformation N ε ≤ 4 * N * ε ^ 2 :=
      StochasticGraph.readingsInformation_le_quadratic N ε h0 hhalf.le
    _ ≤ 4 * B * ε ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sq_nonneg ε)]
    _ ≤ 4 * B * ε := mul_le_mul_of_nonneg_left heps (by positivity)
    _ ≤ 4 * ((B : ℝ) + 1) * ε := by nlinarith
    _ < c := by nlinarith

/-- Theorem 5.1 gives the quadratic ceiling on reading information, the inverse-square
minimum reading count for a reached target at positive signal, and failure of every
bounded reading count inside an explicit neighborhood of zero signal. -/
theorem resolution_cost_statement (N B : ℕ) (ε c : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) :
    StochasticGraph.readingsInformation N ε ≤ 4 * N * ε ^ 2 ∧
      (0 < ε → c ≤ StochasticGraph.readingsInformation N ε → c / (4 * ε ^ 2) ≤ N) ∧
      (ε < min (1 / 2 : ℝ) (c / (4 * ((B : ℝ) + 1))) →
        ∀ M ≤ B, StochasticGraph.readingsInformation M ε < c) := by
  refine ⟨StochasticGraph.readingsInformation_le_quadratic N ε h0 h1, ?_, ?_⟩
  · intro hε hc
    exact StochasticGraph.information_target_cost N ε c hε h1 hc
  · intro hε
    exact bounded_budget_fails_explicit B c ε h0 hε

end OperatorKO7.Meta.BoundaryObserver.ReadingBudgetNeighborhood

