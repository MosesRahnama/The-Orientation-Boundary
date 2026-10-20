import Mathlib
namespace OperatorKO7.Meta.LiteratureReview
/-!
Manuscript label: cor:estimator-floor.
A finite differentiable probability model passed through a fixed stochastic
channel obeys the record Cramer-Rao bound, the reciprocal Fisher-information
gap formula, and strict loss exactly at a shared output with different scores.
The deterministic specialization identifies shared outputs with record fibers.
The parameter lies in an open neighborhood, every input mass at the parameter
is positive, and the output alphabet is restricted to its attained support.
The derivative-one condition suffices without a value-unbiasedness assumption.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter
namespace EstimatorFloor

structure Experiment (n k : ℕ) (θ : ℝ) where
  law : ℝ → Fin n → ℝ
  speed : Fin n → ℝ
  laws : ∀ᶠ t in nhds θ, (∀ x, 0 ≤ law t x) ∧ ∑ x, law t x = 1
  positive : ∀ x, 0 < law θ x
  slope : ∀ x, HasDerivAt (fun t => law t x) (speed x) θ
  channel : Fin n → Fin k → ℝ
  channel_nonneg : ∀ x y, 0 ≤ channel x y
  channel_total : ∀ x, ∑ y, channel x y = 1
  attained : ∀ y, 0 < ∑ x, law θ x * channel x y

variable {n k : ℕ} {θ : ℝ}

def input (M : Experiment n k θ) : Fin n → ℝ := M.law θ
def recordLaw (M : Experiment n k θ) (t : ℝ) (y : Fin k) : ℝ :=
  ∑ x, M.law t x * M.channel x y
def q (M : Experiment n k θ) : Fin k → ℝ := recordLaw M θ
def dq (M : Experiment n k θ) (y : Fin k) : ℝ :=
  ∑ x, M.speed x * M.channel x y
def u (M : Experiment n k θ) (x : Fin n) : ℝ := M.speed x / input M x
def v (M : Experiment n k θ) (y : Fin k) : ℝ := dq M y / q M y
def weight (M : Experiment n k θ) (x : Fin n) (y : Fin k) : ℝ :=
  input M x * M.channel x y
def stateInfo (M : Experiment n k θ) : ℝ := ∑ x, input M x * u M x ^ 2
def recordInfo (M : Experiment n k θ) : ℝ := ∑ y, q M y * v M y ^ 2
def expectation (M : Experiment n k θ) (a : Fin k → ℝ) (t : ℝ) : ℝ :=
  ∑ y, recordLaw M t y * a y
def variance (M : Experiment n k θ) (a : Fin k → ℝ) : ℝ :=
  ∑ y, q M y * (a y - expectation M a θ) ^ 2
def residual (M : Experiment n k θ) : ℝ :=
  ∑ y, ∑ x, weight M x y * (u M x - v M y) ^ 2
def conditionalVariance (M : Experiment n k θ) (y : Fin k) : ℝ :=
  ∑ x, (weight M x y / q M y) * (u M x - v M y) ^ 2
def SplitScores (M : Experiment n k θ) : Prop :=
  ∃ x x' y, 0 < M.channel x y ∧ 0 < M.channel x' y ∧ u M x ≠ u M x'

lemma normalized (M : Experiment n k θ) :
    (fun t => ∑ x, M.law t x) =ᶠ[nhds θ] (fun _ => 1) := by
  filter_upwards [M.laws] with t ht
  exact ht.2

lemma input_total (M : Experiment n k θ) : ∑ x, input M x = 1 :=
  (normalized M).self_of_nhds

lemma record_total (M : Experiment n k θ) : ∑ y, q M y = 1 := by
  dsimp [q, recordLaw]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.channel_total, mul_one]
  exact input_total M

lemma total_speed (M : Experiment n k θ) : ∑ x, M.speed x = 0 := by
  have h : HasDerivAt (fun t => ∑ x, M.law t x) (∑ x, M.speed x) θ :=
    HasDerivAt.fun_sum (fun x _ => M.slope x)
  exact h.unique ((hasDerivAt_const θ (1 : ℝ)).congr_of_eventuallyEq (normalized M))

lemma record_slope (M : Experiment n k θ) (y : Fin k) :
    HasDerivAt (fun t => recordLaw M t y) (dq M y) θ :=
  HasDerivAt.fun_sum (fun x _ => (M.slope x).mul_const (M.channel x y))

lemma input_weight (M : Experiment n k θ) (x : Fin n) :
    input M x * u M x = M.speed x := by
  have h : input M x ≠ 0 := (M.positive x).ne'
  dsimp [u]
  field_simp [h]

lemma output_weight (M : Experiment n k θ) (y : Fin k) :
    q M y * v M y = dq M y := by
  have h : q M y ≠ 0 := (M.attained y).ne'
  dsimp [v]
  field_simp [h]

lemma column_score (M : Experiment n k θ) (y : Fin k) :
    ∑ x, weight M x y * u M x = q M y * v M y := by
  calc
    _ = ∑ x, (input M x * u M x) * M.channel x y := by
      apply Finset.sum_congr rfl
      intro x _
      dsimp [weight]
      ring
    _ = dq M y := by
      unfold dq
      apply Finset.sum_congr rfl
      intro x _
      rw [input_weight]
    _ = _ := (output_weight M y).symm

lemma score_mean_zero (M : Experiment n k θ) : ∑ y, q M y * v M y = 0 := by
  calc
    _ = ∑ y, dq M y := Finset.sum_congr rfl fun y _ => output_weight M y
    _ = ∑ x, M.speed x := by
      dsimp [dq]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, M.channel_total, mul_one]
    _ = 0 := total_speed M

lemma weight_nonneg (M : Experiment n k θ) (x : Fin n) (y : Fin k) :
    0 ≤ weight M x y :=
  mul_nonneg (M.positive x).le (M.channel_nonneg x y)

lemma residual_nonneg (M : Experiment n k θ) : 0 ≤ residual M :=
  Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun x _ =>
    mul_nonneg (weight_nonneg M x y) (sq_nonneg _)

lemma recordInfo_nonneg (M : Experiment n k θ) : 0 ≤ recordInfo M :=
  Finset.sum_nonneg fun y _ => mul_nonneg (M.attained y).le (sq_nonneg _)

lemma variance_nonneg (M : Experiment n k θ) (a : Fin k → ℝ) :
    0 ≤ variance M a :=
  Finset.sum_nonneg fun y _ => mul_nonneg (M.attained y).le (sq_nonneg _)

lemma fisher_loss (M : Experiment n k θ) :
    residual M = stateInfo M - recordInfo M := by
  have hrow : (∑ y, ∑ x, weight M x y * u M x ^ 2) = stateInfo M := by
    rw [Finset.sum_comm]
    unfold stateInfo
    apply Finset.sum_congr rfl
    intro x _
    calc
      _ = (input M x * u M x ^ 2) * ∑ y, M.channel x y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        dsimp [weight]
        ring
      _ = _ := by rw [M.channel_total, mul_one]
  have hcol (y : Fin k) :
      (∑ x, weight M x y * v M y ^ 2) = q M y * v M y ^ 2 := by
    rw [← Finset.sum_mul]
    rfl
  have hcross (y : Fin k) :
      (∑ x, weight M x y * u M x * v M y) = q M y * v M y ^ 2 := by
    rw [← Finset.sum_mul, column_score]
    ring
  have hexpand (x : Fin n) (y : Fin k) :
      weight M x y * (u M x - v M y) ^ 2 =
        weight M x y * u M x ^ 2 - 2 * (weight M x y * u M x * v M y) +
          weight M x y * v M y ^ 2 := by ring
  calc
    residual M =
        (∑ y, ∑ x, weight M x y * u M x ^ 2) -
          2 * (∑ y, ∑ x, weight M x y * u M x * v M y) +
          (∑ y, ∑ x, weight M x y * v M y ^ 2) := by
      simp only [residual, hexpand, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = stateInfo M - recordInfo M := by
      rw [hrow]
      simp only [hcross, hcol]
      change stateInfo M - 2 * recordInfo M + recordInfo M =
        stateInfo M - recordInfo M
      ring

lemma information_order (M : Experiment n k θ) : recordInfo M ≤ stateInfo M := by
  have h := fisher_loss M
  have hn := residual_nonneg M
  linarith

lemma conditional_score_mean (M : Experiment n k θ) (y : Fin k) :
    (∑ x, (weight M x y / q M y) * u M x) = v M y := by
  have hq : q M y ≠ 0 := (M.attained y).ne'
  apply mul_left_cancel₀ hq
  calc
    q M y * (∑ x, (weight M x y / q M y) * u M x) =
        ∑ x, weight M x y * u M x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      field_simp [hq]
    _ = q M y * v M y := column_score M y

lemma conditional_weight_total (M : Experiment n k θ) (y : Fin k) :
    (∑ x, weight M x y / q M y) = 1 := by
  rw [← Finset.sum_div]
  change q M y / q M y = 1
  exact div_self (M.attained y).ne'

lemma record_score_variance (M : Experiment n k θ) :
    variance M (v M) = recordInfo M := by
  have hm : expectation M (v M) θ = 0 := score_mean_zero M
  simp only [variance, hm, sub_zero, recordInfo]

lemma conditional_decomposition (M : Experiment n k θ) :
    residual M = ∑ y, q M y * conditionalVariance M y := by
  unfold residual conditionalVariance
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hq : q M y ≠ 0 := (M.attained y).ne'
  field_simp [hq]

lemma residual_zero_iff (M : Experiment n k θ) :
    residual M = 0 ↔ ∀ x y, 0 < M.channel x y → u M x = v M y := by
  classical
  constructor
  · intro hz x y hxy
    let summand : Fin k → Fin n → ℝ :=
      fun z t => weight M t z * (u M t - v M z) ^ 2
    have hterm (z : Fin k) (t : Fin n) : 0 ≤ summand z t :=
      mul_nonneg (weight_nonneg M t z)
        (sq_nonneg (u M t - v M z))
    have hcol_nonneg (z : Fin k) :
        0 ≤ ∑ t : Fin n, summand z t :=
      Finset.sum_nonneg (fun t _ => hterm z t)
    change (∑ z : Fin k, ∑ t : Fin n, summand z t) = 0 at hz
    have hcolumn : (∑ t : Fin n, summand y t) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin k)))
        (f := fun z : Fin k => ∑ t : Fin n, summand z t)
        (fun z _ => hcol_nonneg z)).mp hz y (Finset.mem_univ y)
    have hentry : summand y x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin n)))
        (f := summand y)
        (fun t _ => hterm y t)).mp hcolumn x (Finset.mem_univ x)
    change weight M x y * (u M x - v M y) ^ 2 = 0 at hentry
    have hw : weight M x y ≠ 0 :=
      ne_of_gt (mul_pos (M.positive x) hxy)
    have hsq : (u M x - v M y) ^ 2 = 0 :=
      (mul_eq_zero.mp hentry).resolve_left hw
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro h
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro x _
    by_cases hz : M.channel x y = 0
    · simp [weight, hz]
    · have hp : 0 < M.channel x y :=
        lt_of_le_of_ne (M.channel_nonneg x y) (Ne.symm hz)
      simp [h x y hp]

lemma edge_agreement_of_no_split (M : Experiment n k θ) (h : ¬ SplitScores M) :
    ∀ x y, 0 < M.channel x y → u M x = v M y := by
  classical
  intro x y hx
  have hq : q M y ≠ 0 := (M.attained y).ne'
  apply mul_left_cancel₀ hq
  calc
    q M y * u M x = ∑ z, weight M z y * u M x := by
      rw [← Finset.sum_mul]
      rfl
    _ = ∑ z, weight M z y * u M z := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : M.channel z y = 0
      · simp [weight, hz]
      · have hp : 0 < M.channel z y :=
          lt_of_le_of_ne (M.channel_nonneg z y) (Ne.symm hz)
        have he : u M x = u M z := by
          by_contra hn
          exact h ⟨x, z, y, hx, hp, hn⟩
        rw [he]
    _ = q M y * v M y := column_score M y

lemma residual_pos_iff (M : Experiment n k θ) :
    0 < residual M ↔ SplitScores M := by
  classical
  constructor
  · intro hp
    by_contra h
    have hz := (residual_zero_iff M).mpr (edge_agreement_of_no_split M h)
    linarith
  · rintro ⟨x, x', y, hx, hx', hn⟩
    have hz : residual M ≠ 0 := by
      intro h
      have he := (residual_zero_iff M).mp h
      exact hn ((he x y hx).trans (he x' y hx').symm)
    exact lt_of_le_of_ne (residual_nonneg M) (Ne.symm hz)

lemma split_deterministic_iff (M : Experiment n k θ) (f : Fin n → Fin k)
    (hf : ∀ x y, M.channel x y = if f x = y then 1 else 0) :
    SplitScores M ↔ ∃ x x', f x = f x' ∧ u M x ≠ u M x' := by
  classical
  constructor
  · rintro ⟨x, x', y, hx, hx', hn⟩
    have hxy : f x = y := by
      by_contra h
      simp [hf, h] at hx
    have hx'y : f x' = y := by
      by_contra h
      simp [hf, h] at hx'
    exact ⟨x, x', hxy.trans hx'y.symm, hn⟩
  · rintro ⟨x, x', hxx', hn⟩
    exact ⟨x, x', f x, by simp [hf], by simp [hf, hxx'], hn⟩

lemma centered_score_moment (M : Experiment n k θ) (a : Fin k → ℝ)
    (ha : HasDerivAt (expectation M a) 1 θ) :
    ∑ y, q M y * v M y * (a y - expectation M a θ) = 1 := by
  have hd : HasDerivAt (expectation M a) (∑ y, dq M y * a y) θ :=
    HasDerivAt.fun_sum (fun y _ => (record_slope M y).mul_const (a y))
  have hm : ∑ y, q M y * v M y * a y = 1 := by
    calc
      _ = ∑ y, dq M y * a y := by
        apply Finset.sum_congr rfl
        intro y _
        rw [output_weight]
      _ = 1 := hd.unique ha
  calc
    _ = (∑ y, q M y * v M y * a y) -
        (∑ y, q M y * v M y) * expectation M a θ := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    _ = 1 := by rw [hm, score_mean_zero]; ring

lemma cramer_rao_product (M : Experiment n k θ) (a : Fin k → ℝ)
    (ha : HasDerivAt (expectation M a) 1 θ) :
    1 ≤ recordInfo M * variance M a := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (r := fun y => q M y * v M y * (a y - expectation M a θ))
    (f := fun y => q M y * v M y ^ 2)
    (g := fun y => q M y * (a y - expectation M a θ) ^ 2)
    (fun y _ => mul_nonneg (M.attained y).le (sq_nonneg _))
    (fun y _ => mul_nonneg (M.attained y).le (sq_nonneg _))
    (fun y _ => by ring)
  change 1 ≤ (∑ y, q M y * v M y ^ 2) *
    ∑ y, q M y * (a y - expectation M a θ) ^ 2
  simpa only [centered_score_moment M a ha, one_pow] using h

lemma recordInfo_pos (M : Experiment n k θ) (a : Fin k → ℝ)
    (ha : HasDerivAt (expectation M a) 1 θ) : 0 < recordInfo M := by
  have hp := cramer_rao_product M a ha
  by_contra h
  have hz : recordInfo M = 0 :=
    le_antisymm (le_of_not_gt h) (recordInfo_nonneg M)
  rw [hz, zero_mul] at hp
  norm_num at hp

lemma strict_floor_iff (M : Experiment n k θ) (hq : 0 < recordInfo M) :
    1 / stateInfo M < 1 / recordInfo M ↔ SplitScores M := by
  have hp : 0 < stateInfo M := hq.trans_le (information_order M)
  constructor
  · intro h
    have hi : recordInfo M < stateInfo M := by
      simpa only [one_mul] using (div_lt_div_iff₀ hp hq).mp h
    apply (residual_pos_iff M).mp
    rw [fisher_loss]
    exact sub_pos.mpr hi
  · intro h
    have hr := (residual_pos_iff M).mpr h
    rw [fisher_loss] at hr
    apply (div_lt_div_iff₀ hp hq).mpr
    simpa only [one_mul] using sub_pos.mp hr

end EstimatorFloor
open EstimatorFloor

/-- cor:estimator-floor, including the stochastic and deterministic strictness criteria. -/
theorem estimator_floor {n k : ℕ} {θ : ℝ}
    (M : Experiment n k θ) (a : Fin k → ℝ)
    (ha : HasDerivAt (expectation M a) 1 θ) :
    0 < recordInfo M ∧ 0 < stateInfo M ∧
    1 / recordInfo M ≤ variance M a ∧
    1 / stateInfo M ≤ 1 / recordInfo M ∧
    1 / recordInfo M - 1 / stateInfo M =
      (stateInfo M - recordInfo M) / (stateInfo M * recordInfo M) ∧
    1 / recordInfo M - 1 / stateInfo M =
      (∑ y, q M y * conditionalVariance M y) / (stateInfo M * recordInfo M) ∧
    (1 / stateInfo M < 1 / recordInfo M ↔ SplitScores M) ∧
    ∀ f : Fin n → Fin k,
      (∀ x y, M.channel x y = if f x = y then 1 else 0) →
      (1 / stateInfo M < 1 / recordInfo M ↔
        ∃ x x', f x = f x' ∧ u M x ≠ u M x') := by
  have hq := recordInfo_pos M a ha
  have hp : 0 < stateInfo M := hq.trans_le (information_order M)
  have hvar : 1 / recordInfo M ≤ variance M a :=
    (div_le_iff₀ hq).mpr (by nlinarith [cramer_rao_product M a ha])
  have horder : 1 / stateInfo M ≤ 1 / recordInfo M :=
    (div_le_div_iff₀ hp hq).mpr (by simpa only [one_mul] using information_order M)
  have hgap : 1 / recordInfo M - 1 / stateInfo M =
      (stateInfo M - recordInfo M) / (stateInfo M * recordInfo M) := by
    simpa only [one_mul, mul_one, mul_comm] using
      (div_sub_div (1 : ℝ) 1 (ne_of_gt hq) (ne_of_gt hp))
  have hvariance : 1 / recordInfo M - 1 / stateInfo M =
      (∑ y, q M y * conditionalVariance M y) / (stateInfo M * recordInfo M) := by
    rw [hgap, ← fisher_loss, conditional_decomposition]
  exact ⟨hq, hp, hvar, horder, hgap, hvariance, strict_floor_iff M hq,
    fun f hf => (strict_floor_iff M hq).trans (split_deterministic_iff M f hf)⟩

#print axioms estimator_floor
end
end OperatorKO7.Meta.LiteratureReview
