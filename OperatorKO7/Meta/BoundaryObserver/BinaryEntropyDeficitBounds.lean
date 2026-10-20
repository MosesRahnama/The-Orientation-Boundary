import OperatorKO7.Meta.BoundaryObserver.FairReadingBound

set_option autoImplicit false

/-!
# Two-sided bound on the binary entropy deficit

`prop:deficit-two-sided`. The deficit
`κ_ε = 1 - h(1/2 + ε)` of a binary symmetric reading of bias `ε`, in bits, lies between
`(2 / ln 2) ε²` and `4 ε²` for `|ε| ≤ 1/2`. The lower end is the binary Pinsker inequality
`FairReadingBound.sq_div_two_le_log_two_sub_binEntropy`; the upper end is
`FourTestTables.one_sub_binEntropy_le_sq`. The count `c / κ_ε` of readings for `c` bits therefore
lies between `c / (4 ε²)` and `c ln 2 / (2 ε²)`, and the quotient of the two end counts is `2 ln 2`.
The lower constant `2 / ln 2` is the least possible: every larger constant fails at some positive
bias, by the expansion `BitDivision.one_sub_binEntropy_expansion`.


Relation: none. Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BinaryEntropyDeficitBounds

/-- The deficit `1 - h(1/2 + ε)` in bits of a binary symmetric reading of bias `ε`. -/
noncomputable def binaryEntropyDeficit (ε : ℝ) : ℝ :=
  1 - Real.binEntropy (1 / 2 + ε) / Real.log 2

/-- Unfolding lemma of `binaryEntropyDeficit`. -/
theorem binaryEntropyDeficit_def (ε : ℝ) :
    binaryEntropyDeficit ε = 1 - Real.binEntropy (1 / 2 + ε) / Real.log 2 := rfl

/--
Proves: for `|t| ≤ 1`, `t² / (2 ln 2) ≤ 1 - h((1 + t)/2)` with `h` in bits.
Does not prove: the matching upper bound; that is `FourTestTables.one_sub_binEntropy_le_sq`.
Scope: `prop:deficit-two-sided`, lower end in the variable `t`.
Trust: kernel-only.
-/
theorem sq_div_two_log_two_le_one_sub_binEntropy (t : ℝ) (ht : |t| ≤ 1) :
    t ^ 2 / (2 * Real.log 2) ≤ 1 - Real.binEntropy ((1 + t) / 2) / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL : Real.log 2 ≠ 0 := ne_of_gt hlog
  have h := FairReadingBound.sq_div_two_le_log_two_sub_binEntropy t ht
  have e1 : (Real.log 2 - Real.binEntropy ((1 + t) / 2)) / Real.log 2 =
      1 - Real.binEntropy ((1 + t) / 2) / Real.log 2 := by
    rw [sub_div, div_self hL]
  have e2 : t ^ 2 / (2 * Real.log 2) = (t ^ 2 / 2) / Real.log 2 := by
    rw [div_div]
  rw [← e1, e2]
  exact div_le_div_of_nonneg_right h hlog.le

/--
Proves: the lower end of `prop:deficit-two-sided`: `(2 / ln 2) ε² ≤ 1 - h(1/2 + ε)` for
`|ε| ≤ 1/2`.
Scope: `|ε| ≤ 1/2`.
Trust: kernel-only.
-/
theorem binaryEntropyDeficit_ge_two_div_log_two_mul_sq (ε : ℝ) (hε : |ε| ≤ 1 / 2) :
    2 / Real.log 2 * ε ^ 2 ≤ binaryEntropyDeficit ε := by
  have ht : |2 * ε| ≤ 1 := by
    rw [abs_mul, abs_two]
    linarith
  have h := sq_div_two_log_two_le_one_sub_binEntropy (2 * ε) ht
  have e1 : (1 + 2 * ε) / 2 = 1 / 2 + ε := by ring
  have e2 : (2 * ε) ^ 2 / (2 * Real.log 2) = 2 / Real.log 2 * ε ^ 2 := by
    field_simp
    ring
  rw [e1, e2] at h
  exact h

/--
Proves: the upper end of `prop:deficit-two-sided`: `1 - h(1/2 + ε) ≤ 4 ε²` for `|ε| ≤ 1/2`.
Scope: `|ε| ≤ 1/2`.
Trust: kernel-only.
-/
theorem binaryEntropyDeficit_le_four_mul_sq (ε : ℝ) (hε : |ε| ≤ 1 / 2) :
    binaryEntropyDeficit ε ≤ 4 * ε ^ 2 := by
  have ht : |2 * ε| ≤ 1 := by
    rw [abs_mul, abs_two]
    linarith
  have h := FourTestTables.one_sub_binEntropy_le_sq (2 * ε) ht
  have e1 : (1 + 2 * ε) / 2 = 1 / 2 + ε := by ring
  rw [e1] at h
  unfold binaryEntropyDeficit
  nlinarith [h]

/--
Proves: `prop:deficit-two-sided` in one statement: `(2 / ln 2) ε² ≤ κ_ε ≤ 4 ε²` for `|ε| ≤ 1/2`.
Scope: `|ε| ≤ 1/2`.
Trust: kernel-only.
-/
theorem binaryEntropyDeficit_two_sided (ε : ℝ) (hε : |ε| ≤ 1 / 2) :
    2 / Real.log 2 * ε ^ 2 ≤ binaryEntropyDeficit ε ∧ binaryEntropyDeficit ε ≤ 4 * ε ^ 2 :=
  ⟨binaryEntropyDeficit_ge_two_div_log_two_mul_sq ε hε,
    binaryEntropyDeficit_le_four_mul_sq ε hε⟩

/-- The deficit is positive at every nonzero bias with `|ε| ≤ 1/2`. -/
theorem binaryEntropyDeficit_pos (ε : ℝ) (hε0 : ε ≠ 0) (hε : |ε| ≤ 1 / 2) :
    0 < binaryEntropyDeficit ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hsq : 0 < ε ^ 2 := by positivity
  have hpos : 0 < 2 / Real.log 2 * ε ^ 2 := mul_pos (div_pos two_pos hlog) hsq
  exact lt_of_lt_of_le hpos (binaryEntropyDeficit_ge_two_div_log_two_mul_sq ε hε)

/--
Proves: for `c ≥ 0` and a nonzero bias with `|ε| ≤ 1/2`, the count `c / κ_ε` of readings for `c`
bits lies between `c / (4 ε²)` and `c ln 2 / (2 ε²)`.
Scope: the count statement of `prop:deficit-two-sided`.
Trust: kernel-only.
-/
theorem readings_count_two_sided (c ε : ℝ) (hc : 0 ≤ c) (hε0 : ε ≠ 0) (hε : |ε| ≤ 1 / 2) :
    c / (4 * ε ^ 2) ≤ c / binaryEntropyDeficit ε ∧
      c / binaryEntropyDeficit ε ≤ c * Real.log 2 / (2 * ε ^ 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hsq : 0 < ε ^ 2 := by positivity
  have hk := binaryEntropyDeficit_pos ε hε0 hε
  have hlo := binaryEntropyDeficit_ge_two_div_log_two_mul_sq ε hε
  have hhi := binaryEntropyDeficit_le_four_mul_sq ε hε
  constructor
  · rw [div_le_div_iff₀ (by positivity) hk]
    exact mul_le_mul_of_nonneg_left hhi hc
  · rw [div_le_div_iff₀ hk (by positivity)]
    have hlo' : 2 * ε ^ 2 ≤ binaryEntropyDeficit ε * Real.log 2 := by
      have e : 2 / Real.log 2 * ε ^ 2 * Real.log 2 = 2 * ε ^ 2 := by
        field_simp
      have := mul_le_mul_of_nonneg_right hlo hlog.le
      linarith
    have := mul_le_mul_of_nonneg_left hlo' hc
    linarith

/--
Proves: the quotient of the count `ln 2 / (2 ε²)` of a one-bit gate and the count `1 / (4 ε²)` of
the Fisher information at zero bias is `2 ln 2`.
Scope: the last sentence of `prop:deficit-two-sided`.
Trust: kernel-only.
-/
theorem gate_count_eq_two_log_two_mul_fisher_count (ε : ℝ) (hε0 : ε ≠ 0) :
    Real.log 2 / (2 * ε ^ 2) = 2 * Real.log 2 * (1 / (4 * ε ^ 2)) := by
  have hsq : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε0
  field_simp
  ring

/--
Proves: the lower constant `2 / ln 2` is the least possible: for every `C > 2 / ln 2` some bias
`0 < ε ≤ 1/2` has `κ_ε < C ε²`.
Does not prove: a value of that bias; the proof takes one inside the ball of bounded fourth-order
remainder of `BitDivision.one_sub_binEntropy_expansion`.
Scope: sharpness of the lower end of `prop:deficit-two-sided`.
Trust: kernel-only.
-/
theorem two_div_log_two_sharp (C : ℝ) (hC : 2 / Real.log 2 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ binaryEntropyDeficit ε < C * ε ^ 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨K, hK, hKw⟩ := BitDivision.one_sub_binEntropy_expansion.exists_pos
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hKw.bound
  have hgap : 0 < C * Real.log 2 - 2 := by
    have h2 : 2 < C * Real.log 2 := (div_lt_iff₀ hlog).mp hC
    linarith
  set ε : ℝ := min (min (δ / 2) (1 / 4)) ((C * Real.log 2 - 2) / (2 * K)) with hεdef
  have hε0 : 0 < ε := by
    refine lt_min (lt_min (by linarith) (by norm_num)) (div_pos hgap (by linarith))
  have hεδ : ε < δ := by
    have : ε ≤ δ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hε14 : ε ≤ 1 / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hεK : ε ≤ (C * Real.log 2 - 2) / (2 * K) := min_le_right _ _
  have hdist : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε0]
    exact hεδ
  have hb := hball hdist
  have hε4 : (0 : ℝ) ≤ ε ^ 4 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hε4] at hb
  have hf : Real.log 2 - Real.binEntropy (1 / 2 + ε) - 2 * ε ^ 2 ≤ K * ε ^ 4 :=
    le_trans (le_abs_self _) hb
  have hKε : K * ε ≤ (C * Real.log 2 - 2) / 2 := by
    have := mul_le_mul_of_nonneg_left hεK hK.le
    have e : K * ((C * Real.log 2 - 2) / (2 * K)) = (C * Real.log 2 - 2) / 2 := by
      field_simp
      ring
    linarith
  have hε1 : ε ≤ 1 := by linarith
  have hKε2 : K * ε ^ 2 ≤ K * ε := by
    have : ε ^ 2 ≤ ε := by nlinarith
    exact mul_le_mul_of_nonneg_left this hK.le
  have hsq : 0 < ε ^ 2 := by positivity
  have hnat : Real.log 2 - Real.binEntropy (1 / 2 + ε) < C * Real.log 2 * ε ^ 2 := by
    have e : K * ε ^ 4 = (K * ε ^ 2) * ε ^ 2 := by ring
    have h1 : K * ε ^ 2 < C * Real.log 2 - 2 := by linarith
    have h2 : K * ε ^ 2 * ε ^ 2 < (C * Real.log 2 - 2) * ε ^ 2 :=
      mul_lt_mul_of_pos_right h1 hsq
    nlinarith
  refine ⟨ε, hε0, by linarith, ?_⟩
  have hL : Real.log 2 ≠ 0 := ne_of_gt hlog
  have e1 : binaryEntropyDeficit ε =
      (Real.log 2 - Real.binEntropy (1 / 2 + ε)) / Real.log 2 := by
    rw [binaryEntropyDeficit_def, sub_div, div_self hL]
  rw [e1, div_lt_iff₀ hlog]
  linarith

/-- Non-vacuity: at bias `1/4` the two-sided bound reads `1/(8 ln 2) ≤ κ ≤ 1/4`. -/
example : 2 / Real.log 2 * (1 / 4 : ℝ) ^ 2 ≤ binaryEntropyDeficit (1 / 4) ∧
    binaryEntropyDeficit (1 / 4) ≤ 4 * (1 / 4 : ℝ) ^ 2 :=
  binaryEntropyDeficit_two_sided (1 / 4) (by rw [abs_of_pos (by norm_num)]; norm_num)

end OperatorKO7.Meta.BoundaryObserver.BinaryEntropyDeficitBounds
