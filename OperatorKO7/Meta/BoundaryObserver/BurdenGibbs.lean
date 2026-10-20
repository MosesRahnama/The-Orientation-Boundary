import OperatorKO7.Meta.BoundaryGeneral.CountableRoleExchange
import OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden

set_option autoImplicit false

/-!
# Finite divergence inequality

The relative entropy of two finite probability laws is nonnegative
(`finite_divergence_nonneg`) and vanishes only at the positive reference law
(`finite_divergence_eq_zero_iff`). Both follow from the termwise inequality of the
role-exchange module, with strictness in `neg_divergence_term_lt`.
Trust: kernel-only.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BurdenGibbs

open OperatorKO7.Meta.BoundaryGeneral.CountableRoleExchange
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden

noncomputable section

/-- The finite divergence inequality is inherited from the existing role-exchange theorem. -/
theorem finite_divergence_nonneg {K : Type} [Fintype K] (p q : K → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 < q k)
    (hp1 : ∑ k, p k = 1) (hq1 : ∑ k, q k = 1) :
    0 ≤ countableRoleDivergence p q := by
  have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset K)) =>
    neg_divergence_term_le p q hp hq k)
  rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib, hp1, hq1] at h
  rw [countableRoleDivergence_fintype]
  linarith

/-- Strictness of the inherited termwise inequality when two probabilities differ. -/
theorem neg_divergence_term_lt {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hne : p ≠ q) :
    -(p * Real.log (p / q)) < q - p := by
  rcases hp.eq_or_lt with hp0 | hp0
  · simp only [← hp0, zero_mul, neg_zero, sub_zero]
    exact hq
  · have hratio : q / p ≠ 1 := by
      intro h
      exact hne ((div_eq_one_iff_eq hp0.ne').mp h).symm
    have hl := Real.log_lt_sub_one_of_pos (div_pos hq hp0) hratio
    rw [Real.log_div hq.ne' hp0.ne'] at hl
    have hm := mul_lt_mul_of_pos_left hl hp0
    have hc : p * (q / p - 1) = q - p := by field_simp
    rw [hc] at hm
    rw [Real.log_div hp0.ne' hq.ne']
    nlinarith

/-- The finite relative entropy vanishes exactly at the positive reference law. -/
theorem finite_divergence_eq_zero_iff {K : Type} [Fintype K] (p q : K → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 < q k)
    (hp1 : ∑ k, p k = 1) (hq1 : ∑ k, q k = 1) :
    countableRoleDivergence p q = 0 ↔ p = q := by
  classical
  constructor
  · intro hz
    by_contra hn
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hn
    have hlt := Finset.sum_lt_sum
      (fun i (_ : i ∈ (Finset.univ : Finset K)) => neg_divergence_term_le p q hp hq i)
      ⟨k, Finset.mem_univ _, neg_divergence_term_lt (hp k) (hq k) hk⟩
    rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib, hp1, hq1] at hlt
    rw [countableRoleDivergence_fintype] at hz
    linarith
  · intro h
    rw [h]
    exact countableRoleDivergence_self q

end

end OperatorKO7.Meta.BoundaryObserver.BurdenGibbs
