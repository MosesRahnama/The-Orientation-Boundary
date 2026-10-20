import Mathlib

namespace OperatorKO7.Meta.LiteratureReview

/-!
Example `ex:gcd-kernel` states that the normalized squared-gcd kernel on
positive integers has the finitely supported Jordan-totient Gram
realization, all its finite quadratic forms are sums of squared absolute
values, and subtracting the feature at one realizes the based kernel
with base point zero.

The Jordan totient is the cardinality of the stated set of positive
integer pairs. The real features are embedded in complex square-summable
sequences, with coordinate zero identically zero.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace GCDKernel

def square (m : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 m).product (Icc 1 m)

lemma mem_square {m : ℕ} {p : ℕ × ℕ} :
    p ∈ square m ↔
      (0 < p.1 ∧ p.1 ≤ m) ∧ (0 < p.2 ∧ p.2 ≤ m) := by
  simp [square, Nat.succ_le_iff]

lemma square_card (m : ℕ) : (square m).card = m ^ 2 := by
  simp [square, Nat.card_Icc, pow_two]

def jordan2 (m : ℕ) : ℕ :=
  ((square m).filter fun p => Nat.gcd (Nat.gcd p.1 p.2) m = 1).card

lemma jordan2_divisor_fiber {m d : ℕ} (hm : 0 < m) (hdm : d ∣ m) :
    jordan2 (m / d) =
      ((square m).filter fun p => Nat.gcd (Nat.gcd p.1 p.2) m = d).card := by
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    exact hm.ne' (Nat.eq_zero_of_zero_dvd hdm)
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  rcases hdm with ⟨q, rfl⟩
  rw [Nat.mul_div_cancel_left q hd]
  unfold jordan2
  apply Finset.card_bij (fun (p : ℕ × ℕ) _ => (d * p.1, d * p.2))
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hg⟩
    have h := mem_square.mp hp
    apply Finset.mem_filter.mpr
    constructor
    · apply mem_square.mpr
      exact ⟨⟨Nat.mul_pos hd h.1.1, Nat.mul_le_mul_left d h.1.2⟩,
        ⟨Nat.mul_pos hd h.2.1, Nat.mul_le_mul_left d h.2.2⟩⟩
    · change Nat.gcd (Nat.gcd (d * p.1) (d * p.2)) (d * q) = d
      rw [Nat.gcd_mul_left, Nat.gcd_mul_left, hg, mul_one]
  · intro p _ r _ h
    apply Prod.ext
    · exact Nat.eq_of_mul_eq_mul_left hd (congrArg Prod.fst h)
    · exact Nat.eq_of_mul_eq_mul_left hd (congrArg Prod.snd h)
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hg⟩
    have h := mem_square.mp hp
    have hdg : d ∣ Nat.gcd p.1 p.2 := by
      rw [← hg]
      exact Nat.gcd_dvd_left _ _
    have hda : d ∣ p.1 := hdg.trans (Nat.gcd_dvd_left _ _)
    have hdb : d ∣ p.2 := hdg.trans (Nat.gcd_dvd_right _ _)
    rcases hda with ⟨a, ha⟩
    rcases hdb with ⟨b, hb⟩
    rw [ha, hb] at h hg
    have ha0 : 0 < a := by
      apply (mul_lt_mul_left hd).mp
      simpa only [mul_zero] using h.1.1
    have hb0 : 0 < b := by
      apply (mul_lt_mul_left hd).mp
      simpa only [mul_zero] using h.2.1
    have haq : a ≤ q := (mul_le_mul_left hd).mp h.1.2
    have hbq : b ≤ q := (mul_le_mul_left hd).mp h.2.2
    have hab : Nat.gcd (Nat.gcd a b) q = 1 := by
      apply Nat.eq_of_mul_eq_mul_left hd
      simpa only [Nat.gcd_mul_left, mul_one] using hg
    have hmem :
        (a, b) ∈ (square q).filter
          (fun p => Nat.gcd (Nat.gcd p.1 p.2) q = 1) :=
      Finset.mem_filter.mpr
        ⟨mem_square.mpr ⟨⟨ha0, haq⟩, ⟨hb0, hbq⟩⟩, hab⟩
    exact ⟨(a, b), hmem, Prod.ext ha.symm hb.symm⟩

lemma jordan2_sum (m : ℕ) :
    ∑ d ∈ m.divisors, jordan2 d = m ^ 2 := by
  by_cases hm : m = 0
  · subst m
    simp
  rw [← Nat.sum_div_divisors m jordan2]
  calc
    _ = ∑ d ∈ m.divisors,
        ((square m).filter fun p => Nat.gcd (Nat.gcd p.1 p.2) m = d).card := by
      apply Finset.sum_congr rfl
      intro d hd
      exact jordan2_divisor_fiber (Nat.pos_of_ne_zero hm) (Nat.dvd_of_mem_divisors hd)
    _ = (square m).card := by
      symm
      apply Finset.card_eq_sum_card_fiberwise
      intro p _
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hm⟩
    _ = m ^ 2 := square_card m

abbrev H := lp (fun _ : ℕ => ℂ) 2

def coefficient (j : ℕ+) (d : ℕ) : ℝ :=
  Real.sqrt (jordan2 d : ℝ) / (j : ℕ)

def kernel (j k : ℕ+) : ℝ :=
  (Nat.gcd (j : ℕ) (k : ℕ) : ℝ) ^ 2 /
    (((j : ℕ) : ℝ) * ((k : ℕ) : ℝ))

def vector (j : ℕ+) : H :=
  ∑ d ∈ (j : ℕ).divisors, lp.single 2 d (coefficient j d : ℂ)

lemma vector_apply (j : ℕ+) (d : ℕ) :
    vector j d =
      if d ∈ (j : ℕ).divisors then (coefficient j d : ℂ) else 0 := by
  simp only [vector, lp.coeFn_sum, lp.coeFn_single,
    Finset.sum_apply, Finset.sum_pi_single]

lemma vector_apply_dvd (j : ℕ+) (d : ℕ) :
    vector j d =
      if d ∣ (j : ℕ) then (coefficient j d : ℂ) else 0 := by
  have hmem : d ∈ (j : ℕ).divisors ↔ d ∣ (j : ℕ) := by
    constructor
    · exact Nat.dvd_of_mem_divisors
    · intro hd
      exact Nat.mem_divisors.mpr ⟨hd, Nat.ne_of_gt j.2⟩
  rw [vector_apply]
  by_cases h : d ∣ (j : ℕ)
  · rw [if_pos (hmem.mpr h), if_pos h]
  · rw [if_neg (fun hm => h (hmem.mp hm)), if_neg h]

lemma vector_support (j : ℕ+) :
    Function.support (fun d => vector j d) ⊆
      ((j : ℕ).divisors : Set ℕ) := by
  intro d hd
  change vector j d ≠ 0 at hd
  change d ∈ (j : ℕ).divisors
  by_contra h
  exact hd (by rw [vector_apply, if_neg h])

lemma vector_finite_support (j : ℕ+) :
    (Function.support (fun d => vector j d)).Finite :=
  (j : ℕ).divisors.finite_toSet.subset (vector_support j)

lemma vector_zero_coordinate (j : ℕ+) : vector j 0 = 0 := by
  have h : (0 : ℕ) ∉ (j : ℕ).divisors := by
    intro h
    exact (Nat.lt_irrefl 0) (Nat.pos_of_mem_divisors h)
  rw [vector_apply, if_neg h]

lemma vector_conj (j : ℕ+) (d : ℕ) :
    starRingEnd ℂ (vector j d) = vector j d := by
  rw [vector_apply]
  split_ifs <;> simp

lemma coefficient_product (j k : ℕ+) (d : ℕ) :
    coefficient j d * coefficient k d =
      (jordan2 d : ℝ) / (((j : ℕ) : ℝ) * ((k : ℕ) : ℝ)) := by
  unfold coefficient
  calc
    _ = (Real.sqrt (jordan2 d : ℝ)) ^ 2 /
        (((j : ℕ) : ℝ) * ((k : ℕ) : ℝ)) := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity)]

lemma divisor_formula (j k : ℕ+) :
    kernel j k =
      (∑ d ∈ (Nat.gcd (j : ℕ) (k : ℕ)).divisors, (jordan2 d : ℝ)) /
        (((j : ℕ) : ℝ) * ((k : ℕ) : ℝ)) := by
  have hs :
      (∑ d ∈ (Nat.gcd (j : ℕ) (k : ℕ)).divisors, (jordan2 d : ℝ)) =
        (Nat.gcd (j : ℕ) (k : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast jordan2_sum (Nat.gcd (j : ℕ) (k : ℕ))
  rw [hs]
  rfl

lemma coefficient_sum (j k : ℕ+) :
    (∑ d ∈ (Nat.gcd (j : ℕ) (k : ℕ)).divisors,
      coefficient j d * coefficient k d) = kernel j k := by
  simp_rw [coefficient_product]
  rw [← Finset.sum_div]
  exact (divisor_formula j k).symm

lemma inner_finite_sum (z w : H) (s : Finset ℕ)
    (hs : ∀ d ∉ s, inner ℂ (z d) (w d) = 0) :
    inner ℂ z w = ∑ d ∈ s, inner ℂ (z d) (w d) :=
  (lp.hasSum_inner (𝕜 := ℂ) z w).unique (hasSum_sum_of_ne_finset_zero hs)

lemma scalar_inner (a b : ℝ) :
    inner ℂ (a : ℂ) (b : ℂ) = ((a * b : ℝ) : ℂ) := by
  simp only [RCLike.inner_apply', Complex.conj_ofReal, Complex.ofReal_mul]

lemma vector_inner (j k : ℕ+) :
    inner ℂ (vector j) (vector k) = (kernel j k : ℂ) := by
  have hg : Nat.gcd (j : ℕ) (k : ℕ) ≠ 0 :=
    (Nat.gcd_pos_of_pos_left (k : ℕ) j.2).ne'
  calc
    _ = ∑ d ∈ (Nat.gcd (j : ℕ) (k : ℕ)).divisors,
        inner ℂ (vector j d) (vector k d) := by
      apply inner_finite_sum
      intro d hd
      by_cases hj : d ∈ (j : ℕ).divisors
      · have hk : d ∉ (k : ℕ).divisors := by
          intro hk
          exact hd (Nat.mem_divisors.mpr
            ⟨Nat.dvd_gcd (Nat.dvd_of_mem_divisors hj)
              (Nat.dvd_of_mem_divisors hk), hg⟩)
        rw [vector_apply k d, if_neg hk]
        simp
      · rw [vector_apply j d, if_neg hj]
        simp
    _ = ((∑ d ∈ (Nat.gcd (j : ℕ) (k : ℕ)).divisors,
        coefficient j d * coefficient k d : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hdiv := Nat.dvd_of_mem_divisors hd
      have hj : d ∈ (j : ℕ).divisors :=
        Nat.mem_divisors.mpr
          ⟨hdiv.trans (Nat.gcd_dvd_left _ _), Nat.ne_of_gt j.2⟩
      have hk : d ∈ (k : ℕ).divisors :=
        Nat.mem_divisors.mpr
          ⟨hdiv.trans (Nat.gcd_dvd_right _ _), Nat.ne_of_gt k.2⟩
      rw [vector_apply j d, if_pos hj, vector_apply k d, if_pos hk]
      exact scalar_inner _ _
    _ = _ := congrArg (fun r : ℝ => (r : ℂ)) (coefficient_sum j k)

lemma kernel_tsum (j k : ℕ+) :
    (kernel j k : ℂ) = ∑' d : ℕ, vector j d * vector k d := by
  rw [← vector_inner, lp.inner_eq_tsum]
  apply tsum_congr
  intro d
  rw [RCLike.inner_apply', vector_conj]

def basedKernel (j k : ℕ+) : ℝ :=
  kernel j k - kernel j 1 - kernel 1 k + kernel 1 1

def basedVector (j : ℕ+) : H := vector j - vector 1

lemma based_inner (j k : ℕ+) :
    inner ℂ (basedVector j) (basedVector k) = (basedKernel j k : ℂ) := by
  simp only [basedVector, inner_sub_left, inner_sub_right, vector_inner, basedKernel]
  push_cast
  ring

lemma basedVector_one : basedVector 1 = 0 := by
  simp [basedVector]

lemma basedKernel_one_left (j : ℕ+) : basedKernel 1 j = 0 := by
  unfold basedKernel
  ring

lemma basedKernel_one_right (j : ℕ+) : basedKernel j 1 = 0 := by
  unfold basedKernel
  ring

lemma kernel_hermitian (j k : ℕ+) :
    starRingEnd ℂ (kernel k j : ℂ) = (kernel j k : ℂ) := by
  rw [← vector_inner, ← vector_inner]
  exact inner_conj_symm _ _

lemma basedKernel_hermitian (j k : ℕ+) :
    starRingEnd ℂ (basedKernel k j : ℂ) = (basedKernel j k : ℂ) := by
  rw [← based_inner, ← based_inner]
  exact inner_conj_symm _ _

variable {ι : Type*} [Fintype ι]

def quadratic (L : ℕ+ → ℕ+ → ℂ) (x : ι → ℕ+) (a : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (a i) * L (x i) (x j) * a j

lemma gram_quadratic (v : ι → H) (a : ι → ℂ) :
    (∑ i, ∑ j, starRingEnd ℂ (a i) * inner ℂ (v i) (v j) * a j) =
      inner ℂ (∑ i, a i • v i) (∑ i, a i • v i) := by
  symm
  simp only [sum_inner]
  simp only [inner_sum]
  simp only [inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma inner_self_squares (s : Finset ℕ) (z : H)
    (hz : ∀ d ∉ s, z d = 0) :
    inner ℂ z z = ((∑ d ∈ s, ‖z d‖ ^ 2 : ℝ) : ℂ) := by
  have h : inner ℂ z z = ∑ d ∈ s, inner ℂ (z d) (z d) := by
    apply inner_finite_sum
    intro d hd
    rw [hz d hd]
    simp
  rw [h, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro d _
  simpa only [Complex.ofReal_pow] using
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (z d))

lemma gram_squares (v : ι → H) (a : ι → ℂ) (s : Finset ℕ)
    (hs : ∀ i d, d ∉ s → v i d = 0) :
    (∑ i, ∑ j, starRingEnd ℂ (a i) * inner ℂ (v i) (v j) * a j) =
      ((∑ d ∈ s, ‖∑ i, a i * v i d‖ ^ 2 : ℝ) : ℂ) := by
  rw [gram_quadratic]
  have hz : ∀ d ∉ s, (∑ i, a i • v i) d = 0 := by
    intro d hd
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [hs i d hd, smul_zero]
  simpa only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul] using
    (inner_self_squares s (∑ i, a i • v i) hz)

def sampleCoordinates (x : ι → ℕ+) : Finset ℕ :=
  (1 : ℕ).divisors ∪ Finset.univ.biUnion (fun i => (x i : ℕ).divisors)

lemma sample_vector_zero (x : ι → ℕ+) (i : ι) (d : ℕ)
    (hd : d ∉ sampleCoordinates x) : vector (x i) d = 0 := by
  have h : d ∉ (x i : ℕ).divisors := by
    intro h
    apply hd
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩))
  rw [vector_apply, if_neg h]

lemma sample_base_zero (x : ι → ℕ+) (d : ℕ)
    (hd : d ∉ sampleCoordinates x) : vector 1 d = 0 := by
  have h : d ∉ (1 : ℕ).divisors := by
    intro h
    exact hd (Finset.mem_union.mpr (Or.inl h))
  rw [vector_apply]
  exact if_neg h

lemma sample_based_zero (x : ι → ℕ+) (i : ι) (d : ℕ)
    (hd : d ∉ sampleCoordinates x) : basedVector (x i) d = 0 := by
  change vector (x i) d - vector 1 d = 0
  rw [sample_vector_zero x i d hd, sample_base_zero x d hd, sub_self]

lemma kernel_squares (x : ι → ℕ+) (a : ι → ℂ) :
    quadratic (fun j k => (kernel j k : ℂ)) x a =
      ((∑ d ∈ sampleCoordinates x,
        ‖∑ i, a i * vector (x i) d‖ ^ 2 : ℝ) : ℂ) := by
  unfold quadratic
  simp_rw [← vector_inner]
  exact gram_squares (fun i => vector (x i)) a (sampleCoordinates x)
    (sample_vector_zero x)

lemma basedKernel_squares (x : ι → ℕ+) (a : ι → ℂ) :
    quadratic (fun j k => (basedKernel j k : ℂ)) x a =
      ((∑ d ∈ sampleCoordinates x,
        ‖∑ i, a i * basedVector (x i) d‖ ^ 2 : ℝ) : ℂ) := by
  unfold quadratic
  simp_rw [← based_inner]
  exact gram_squares (fun i => basedVector (x i)) a (sampleCoordinates x)
    (sample_based_zero x)

lemma kernel_quadratic_nonneg (x : ι → ℕ+) (a : ι → ℂ) :
    0 ≤ (quadratic (fun j k => (kernel j k : ℂ)) x a).re := by
  rw [kernel_squares]
  change 0 ≤ ∑ d ∈ sampleCoordinates x, ‖∑ i, a i * vector (x i) d‖ ^ 2
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma basedKernel_quadratic_nonneg (x : ι → ℕ+) (a : ι → ℂ) :
    0 ≤ (quadratic (fun j k => (basedKernel j k : ℂ)) x a).re := by
  rw [basedKernel_squares]
  change 0 ≤ ∑ d ∈ sampleCoordinates x, ‖∑ i, a i * basedVector (x i) d‖ ^ 2
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

def PositiveKernel (L : ℕ+ → ℕ+ → ℂ) : Prop :=
  (∀ j k, starRingEnd ℂ (L k j) = L j k) ∧
    ∀ (n : ℕ) (x : Fin n → ℕ+) (a : Fin n → ℂ),
      0 ≤ (quadratic L x a).re

lemma kernel_positive : PositiveKernel (fun j k => (kernel j k : ℂ)) :=
  ⟨kernel_hermitian, fun _ x a => kernel_quadratic_nonneg x a⟩

lemma basedKernel_positive : PositiveKernel (fun j k => (basedKernel j k : ℂ)) :=
  ⟨basedKernel_hermitian, fun _ x a => basedKernel_quadratic_nonneg x a⟩

end GCDKernel

open GCDKernel

theorem gcd_kernel :
    (∀ m : ℕ, ∑ d ∈ m.divisors, jordan2 d = m ^ 2) ∧
    (∀ j : ℕ+, (Function.support (fun d => vector j d)).Finite) ∧
    (∀ j k : ℕ+, inner ℂ (vector j) (vector k) = (kernel j k : ℂ)) ∧
    PositiveKernel (fun j k => (kernel j k : ℂ)) ∧
    (∀ j k : ℕ+,
      inner ℂ (basedVector j) (basedVector k) = (basedKernel j k : ℂ)) ∧
    PositiveKernel (fun j k => (basedKernel j k : ℂ)) ∧
    basedVector 1 = 0 ∧
    (∀ j : ℕ+, basedKernel 1 j = 0 ∧ basedKernel j 1 = 0) := by
  exact ⟨jordan2_sum, vector_finite_support, vector_inner, kernel_positive,
    based_inner, basedKernel_positive, basedVector_one,
    fun j => ⟨basedKernel_one_left j, basedKernel_one_right j⟩⟩

end

end OperatorKO7.Meta.LiteratureReview
