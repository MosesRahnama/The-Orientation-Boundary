import OperatorKO7.Meta.BoundaryObserver.GaussianTotals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

set_option autoImplicit false

/-!
# Weak Gaussian limit of normalized binary-pair sums

Proof graph: `Audit/ledgers/operational-inexpressibility/TWO-VOIDS-PROOF-GRAPH.md`, M12a.
The characteristic limit follows from a sinc identity and the exponential power limit.
Uniform coordinate tails prove tightness. Bounded character-polynomial approximation
then gives weak convergence to the constructed Gaussian, including degenerate correlations.
Relation: weak convergence of normalized independent binary-pair probability laws.
Trust: kernel-only.
-/

open Filter MeasureTheory ProbabilityTheory BoundedContinuousFunction
open scoped Topology

namespace OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit

noncomputable section

/-- The removable singularity of sinc gives an identity valid even at zero. -/
theorem sin_eq_mul_sinc (x : ℝ) : Real.sin x = x * Real.sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

/-- An exact second-order cosine identity, without a remainder assumption. -/
theorem cos_sub_one_sinc (x : ℝ) :
    Real.cos x - 1 = -(x ^ 2 / 2) * (Real.sinc (x / 2)) ^ 2 := by
  have hc := Real.cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hc
  have hs := Real.sin_sq_add_cos_sq (x / 2)
  rw [sin_eq_mul_sinc (x / 2)] at hs
  nlinarith

/-- Square-root scaling tends to infinity along the natural numbers. -/
theorem sqrt_nat_tendsto : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
  simp_rw [Real.sqrt_eq_rpow]
  exact (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    tendsto_natCast_atTop_atTop

/-- Exact variance-scale identity at every positive sample count. -/
theorem scaled_cos_identity (c : ℝ) (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * (Real.cos (c / Real.sqrt n) - 1) =
      -(c ^ 2 / 2) * (Real.sinc (c / (2 * Real.sqrt n))) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [cos_sub_one_sinc, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hh : c / Real.sqrt n / 2 = c / (2 * Real.sqrt n) := by ring
  rw [hh]
  field_simp
  ring

/-- The variance-scale cosine limit, including the zero coefficient. -/
theorem scaled_cos_limit (c : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (Real.cos (c / Real.sqrt n) - 1))
      atTop (𝓝 (-(c ^ 2 / 2))) := by
  have hi : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp sqrt_nat_tendsto
  have ht : Tendsto (fun n : ℕ => c / (2 * Real.sqrt n)) atTop (𝓝 0) := by
    convert hi.const_mul (c / 2) using 1 <;> simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hs : Tendsto (fun n : ℕ => Real.sinc (c / (2 * Real.sqrt n))) atTop (𝓝 1) := by
    simpa only [Real.sinc_zero] using Real.continuous_sinc.continuousAt.tendsto.comp ht
  have h := (hs.pow 2).const_mul (-(c ^ 2 / 2))
  simp only [one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (scaled_cos_identity c n hn).symm

/-- The real characteristic kernel for a centered sign pair with correlation `r`. -/
def pairKernel (r s t : ℝ) : ℝ :=
  (1 + r) / 2 * Real.cos (s + t) + (1 - r) / 2 * Real.cos (s - t)

/-- The linear combination of the two cosine variances is exactly the pair covariance form. -/
theorem pair_kernel_variance_limit (r s t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (pairKernel r (s / Real.sqrt n) (t / Real.sqrt n) - 1)) atTop
      (𝓝 (-(s ^ 2 + t ^ 2 + 2 * r * s * t) / 2)) := by
  have h := ((scaled_cos_limit (s + t)).const_mul ((1 + r) / 2)).add
    ((scaled_cos_limit (s - t)).const_mul ((1 - r) / 2))
  convert h using 1
  · funext n
    simp only [pairKernel, ← add_div, ← sub_div]
    ring
  · congr 1
    ring

/-- The normalized finite-round kernels converge to the Gaussian kernel. No convergence
of probability measures is assumed or concluded by this analytic statement alone. -/
theorem normalized_pair_kernel_limit (r s t : ℝ) :
    Tendsto (fun n : ℕ => (pairKernel r (s / Real.sqrt n) (t / Real.sqrt n)) ^ n)
      atTop (𝓝 (Real.exp (-(s ^ 2 + t ^ 2 + 2 * r * s * t) / 2))) := by
  have h := Real.tendsto_one_add_pow_exp_of_tendsto (pair_kernel_variance_limit r s t)
  have hadd (x : ℝ) : 1 + (x - 1) = x := by ring
  simpa only [hadd] using h

/-- The four ordered sign pairs in one round. -/
def pairOutcome : Fin 4 → (Fin 2 → ℝ) :=
  ![![1, 1], ![1, -1], ![-1, 1], ![-1, -1]]

/-- The centered binary-pair probabilities with correlation parameter `r`. -/
def pairMass (r : ℝ) : Fin 4 → ℝ :=
  ![(1 + r) / 4, (1 - r) / 4, (1 - r) / 4, (1 + r) / 4]

/-- The probability range includes both perfectly correlated endpoints. -/
theorem pairMass_nonneg (r : ℝ) (hr : |r| ≤ 1) (i : Fin 4) :
    0 ≤ pairMass r i := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hr
  fin_cases i <;> norm_num [pairMass] <;> linarith

/-- The four probabilities sum to one. -/
theorem pairMass_sum (r : ℝ) : ∑ i, pairMass r i = 1 := by
  simp [pairMass, Fin.sum_univ_succ]
  ring

/-- The finite probability distribution of one centered sign pair. -/
def pairPMF (r : ℝ) (hr : |r| ≤ 1) : PMF (Fin 4) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (pairMass r i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => pairMass_nonneg r hr i), pairMass_sum]
    simp)

/-- The one-round probability measure on the two real reports. -/
def pairLaw (r : ℝ) (hr : |r| ≤ 1) : Measure (Fin 2 → ℝ) :=
  (pairPMF r hr).toMeasure.map pairOutcome

instance pairLaw_isProbabilityMeasure (r : ℝ) (hr : |r| ≤ 1) :
    IsProbabilityMeasure (pairLaw r hr) := by
  unfold pairLaw
  exact isProbabilityMeasure_map (measurable_of_finite pairOutcome).aemeasurable

/-- A real linear report of the two coordinates. -/
def pairReport (s t : ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  s • ContinuousLinearMap.proj 0 + t • ContinuousLinearMap.proj 1

/-- The finite input probabilities determine every measurable integrable report by a sum. -/
theorem pairLaw_integral (r : ℝ) (hr : |r| ≤ 1)
    (f : (Fin 2 → ℝ) → ℂ) (hf : AEStronglyMeasurable f (pairLaw r hr)) :
    (∫ x, f x ∂pairLaw r hr) = ∑ i, (pairMass r i : ℂ) * f (pairOutcome i) := by
  rw [pairLaw, integral_map (measurable_of_finite pairOutcome).aemeasurable hf,
    PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pairPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (pairMass_nonneg r hr i),
    Complex.real_smul]

/-- Opposite signs cancel the imaginary part of the exponential report. -/
theorem exp_opposite_sum (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) + Complex.exp ((-x : ℝ) * Complex.I) =
      2 * (Real.cos x : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  ring

/-- The characteristic function is computed from the four input probabilities. -/
theorem pairLaw_charFun (r : ℝ) (hr : |r| ≤ 1) (s t : ℝ) :
    charFunDual (pairLaw r hr) (pairReport s t) = (pairKernel r s t : ℂ) := by
  rw [charFunDual_apply, pairLaw_integral r hr _ (by fun_prop)]
  calc
    _ = ((1 + r) / 4 : ℝ) *
          (Complex.exp (((s + t : ℝ) : ℂ) * Complex.I) +
            Complex.exp (((-(s + t) : ℝ) : ℂ) * Complex.I)) +
        ((1 - r) / 4 : ℝ) *
          (Complex.exp (((s - t : ℝ) : ℂ) * Complex.I) +
            Complex.exp (((-(s - t) : ℝ) : ℂ) * Complex.I)) := by
      simp [pairMass, pairOutcome, pairReport, Fin.sum_univ_succ]
      ring_nf
    _ = (pairKernel r s t : ℂ) := by
      rw [exp_opposite_sum, exp_opposite_sum]
      simp only [pairKernel, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]
      ring

/-- The restriction on the correlation parameter is exactly nonnegativity of the weights. -/
theorem pairMass_nonnegative_iff (r : ℝ) :
    (∀ i, 0 ≤ pairMass r i) ↔ |r| ≤ 1 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    norm_num [pairMass] at h0 h1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro h i
    exact pairMass_nonneg r h i

/-- Both one-round coordinate means vanish. -/
theorem pairMass_mean (r : ℝ) (j : Fin 2) :
    ∑ i, pairMass r i * pairOutcome i j = 0 := by
  fin_cases j <;> norm_num [pairMass, pairOutcome, Fin.sum_univ_succ]

/-- The one-round second moment of each coordinate is one. -/
theorem pairMass_second_moment (r : ℝ) (j : Fin 2) :
    ∑ i, pairMass r i * (pairOutcome i j) ^ 2 = 1 := by
  fin_cases j <;> norm_num [pairMass, pairOutcome, Fin.sum_univ_succ] <;> ring

/-- The correlation of the actual signs is the declared parameter. -/
theorem pairMass_cross_moment (r : ℝ) :
    ∑ i, pairMass r i * pairOutcome i 0 * pairOutcome i 1 = r := by
  norm_num [pairMass, pairOutcome, Fin.sum_univ_succ]
  ring

/-- The two opposite-sign outcomes have total probability `(1-r)/2`. -/
theorem pairMass_disagreement (r : ℝ) :
    pairMass r 1 + pairMass r 2 = (1 - r) / 2 := by
  change (1 - r) / 4 + (1 - r) / 4 = (1 - r) / 2
  ring

/-- Substituting the manuscript's correlation gives its original disagreement rate. -/
theorem pairMass_table_rate (d : ℝ) :
    pairMass (1 - 2 * d) 1 + pairMass (1 - 2 * d) 2 = d := by
  rw [pairMass_disagreement]
  ring

/-- The sum law adds one independent copy of the same pair at each step. -/
def pairSumLaw (r : ℝ) (hr : |r| ≤ 1) : ℕ → Measure (Fin 2 → ℝ)
  | 0 => Measure.dirac 0
  | n + 1 => (pairLaw r hr).conv (pairSumLaw r hr n)

/-- The product measure in each successor step expresses independence. -/
theorem pairSumLaw_succ (r : ℝ) (hr : |r| ≤ 1) (n : ℕ) :
    pairSumLaw r hr (n + 1) =
      ((pairLaw r hr).prod (pairSumLaw r hr n)).map
        (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => z.1 + z.2) := rfl

instance pairSumLaw_isProbabilityMeasure (r : ℝ) (hr : |r| ≤ 1) (n : ℕ) :
    IsProbabilityMeasure (pairSumLaw r hr n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac 0); infer_instance
  | succ n ih =>
      letI := ih
      change IsProbabilityMeasure ((pairLaw r hr).conv (pairSumLaw r hr n))
      infer_instance

/-- Independence multiplies the one-round characteristic functions. -/
theorem pairSumLaw_charFun (r : ℝ) (hr : |r| ≤ 1) (n : ℕ) (s t : ℝ) :
    charFunDual (pairSumLaw r hr n) (pairReport s t) = (pairKernel r s t : ℂ) ^ n := by
  induction n with
  | zero => simp [pairSumLaw]
  | succ n ih =>
      rw [pairSumLaw, charFunDual_conv, pairLaw_charFun, ih, pow_succ]
      ring

/-- Scaling by the square root of the number of rounds, with zero mapped to zero. -/
def normalizePair (n : ℕ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (Real.sqrt (n : ℝ))⁻¹ • ContinuousLinearMap.id ℝ (Fin 2 → ℝ)

/-- The probability law of the manuscript's two scaled totals. -/
def pairTotalLaw (r : ℝ) (hr : |r| ≤ 1) (n : ℕ) : Measure (Fin 2 → ℝ) :=
  (pairSumLaw r hr n).map (normalizePair n)

instance pairTotalLaw_isProbabilityMeasure (r : ℝ) (hr : |r| ≤ 1) (n : ℕ) :
    IsProbabilityMeasure (pairTotalLaw r hr n) := by
  unfold pairTotalLaw
  exact isProbabilityMeasure_map (by fun_prop)

/-- Scaling the state scales both coefficients of each linear report. -/
theorem pairReport_normalize (n : ℕ) (s t : ℝ) :
    (pairReport s t).comp (normalizePair n) =
      pairReport (s / Real.sqrt (n : ℝ)) (t / Real.sqrt (n : ℝ)) := by
  ext x
  simp [pairReport, normalizePair, div_eq_mul_inv]
  ring

/-- The finite-round formula is a theorem about the actual probability measure. -/
theorem pairTotalLaw_charFun (r : ℝ) (hr : |r| ≤ 1) (n : ℕ) (s t : ℝ) :
    charFunDual (pairTotalLaw r hr n) (pairReport s t) =
      (pairKernel r (s / Real.sqrt (n : ℝ)) (t / Real.sqrt (n : ℝ)) : ℂ) ^ n := by
  rw [pairTotalLaw, charFunDual_map, pairReport_normalize, pairSumLaw_charFun]

/-- Every linear characteristic report of the actual laws has the Gaussian limit. -/
theorem pairTotalLaw_characteristic_limit (r : ℝ) (hr : |r| ≤ 1) (s t : ℝ) :
    Tendsto (fun n => charFunDual (pairTotalLaw r hr n) (pairReport s t)) atTop
      (𝓝 ((Real.exp (-(s ^ 2 + t ^ 2 + 2 * r * s * t) / 2) : ℝ) : ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (normalized_pair_kernel_limit r s t)
  change Tendsto (fun n : ℕ =>
    (((pairKernel r (s / Real.sqrt n) (t / Real.sqrt n)) ^ n : ℝ) : ℂ)) atTop _ at h
  simpa only [pairTotalLaw_charFun, Complex.ofReal_pow] using h

/-- The Gaussian constructed in the totals module has the limiting characteristic function. -/
theorem pairNormal_charFun (r : ℝ) (hr : |r| ≤ 1) (s t : ℝ) :
    charFunDual (GaussianTotals.pairNormal r) (pairReport s t) =
      ((Real.exp (-(s ^ 2 + t ^ 2 + 2 * r * s * t) / 2) : ℝ) : ℂ) := by
  have hLp : ∀ i : Fin 2, MemLp (fun x : Fin 2 → ℝ => x i) 2
      (GaussianTotals.pairNormal r) :=
    fun i => IsGaussian.memLp_dual (GaussianTotals.pairNormal r)
      (ContinuousLinearMap.proj i : (Fin 2 → ℝ) →L[ℝ] ℝ) 2 (by simp)
  have hm : (∫ x, pairReport s t x ∂GaussianTotals.pairNormal r) = 0 := by
    rw [GaussianTotals.linear_mean_coordinates _ hLp]
    simp only [GaussianTotals.pairNormal_mean, mul_zero, Finset.sum_const_zero]
  have hv : Var[pairReport s t; GaussianTotals.pairNormal r] =
      s ^ 2 + t ^ 2 + 2 * r * s * t := by
    rw [GaussianTotals.linear_variance_coordinates _ hLp,
      GaussianTotals.pairNormal_covariance r hr]
    norm_num [pairReport, Fin.sum_univ_succ]
    ring
  rw [IsGaussian.charFunDual_eq, integral_complex_ofReal, hm, hv]
  simp only [Complex.ofReal_zero, zero_mul, zero_sub]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The characteristic reports converge to those of the constructed Gaussian measure. -/
theorem pairTotalLaw_tendsto_pairNormal_charFun (r : ℝ) (hr : |r| ≤ 1) (s t : ℝ) :
    Tendsto (fun n => charFunDual (pairTotalLaw r hr n) (pairReport s t)) atTop
      (𝓝 (charFunDual (GaussianTotals.pairNormal r) (pairReport s t))) := by
  rw [pairNormal_charFun r hr]
  exact pairTotalLaw_characteristic_limit r hr s t

/-- Every continuous linear report of the pair is given by its two coordinate coefficients. -/
theorem pairReport_coordinates (L : (Fin 2 → ℝ) →L[ℝ] ℝ) :
    L = pairReport (L ![1, 0]) (L ![0, 1]) := by
  have h0 : (fun j : Fin 2 => if 0 = j then (1 : ℝ) else 0) = ![1, 0] := by
    funext j
    fin_cases j <;> norm_num
  have h1 : (fun j : Fin 2 => if 1 = j then (1 : ℝ) else 0) = ![0, 1] := by
    funext j
    fin_cases j <;> norm_num
  ext x
  have h := congrFun (GaussianTotals.linear_report_coordinates L) x
  simpa only [Fin.sum_univ_two, h0, h1, pairReport, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul] using h

/-- Convergence holds for every continuous linear report, with no coordinate choice in the type. -/
theorem pairTotalLaw_all_characteristic_limit (r : ℝ) (hr : |r| ≤ 1)
    (L : (Fin 2 → ℝ) →L[ℝ] ℝ) :
    Tendsto (fun n => charFunDual (pairTotalLaw r hr n) L) atTop
      (𝓝 (charFunDual (GaussianTotals.pairNormal r) L)) := by
  rw [pairReport_coordinates L]
  exact pairTotalLaw_tendsto_pairNormal_charFun r hr _ _

/-- With no rounds both totals are zero. -/
theorem pairTotalLaw_zero (r : ℝ) (hr : |r| ≤ 1) :
    pairTotalLaw r hr 0 = Measure.dirac 0 := by
  rw [pairTotalLaw, pairSumLaw, Measure.map_dirac (by fun_prop)]
  simp only [map_zero]

/-- A single round has the original pair law. -/
theorem pairTotalLaw_one (r : ℝ) (hr : |r| ≤ 1) :
    pairTotalLaw r hr 1 = pairLaw r hr := by
  simp [pairTotalLaw, pairSumLaw, normalizePair]

/-- At zero correlation every sign pair has weight one quarter. -/
theorem pairMass_zero_correlation (i : Fin 4) : pairMass 0 i = 1 / 4 := by
  fin_cases i <;> norm_num [pairMass]

/-- A parameter beyond the correlation range fails to define nonnegative weights. -/
theorem pairMass_outside_range : ¬ ∀ i, 0 ≤ pairMass 2 i := by
  rw [pairMass_nonnegative_iff]
  norm_num

/-- A power of a number in the unit interval of absolute values has a linear increment bound. -/
theorem one_sub_pow_abs_le (a : ℝ) (ha : |a| ≤ 1) (n : ℕ) :
    |1 - a ^ n| ≤ (n : ℝ) * |1 - a| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : 1 - a ^ (n + 1) = (1 - a ^ n) + a ^ n * (1 - a) := by ring
    rw [he]
    calc
      _ ≤ |1 - a ^ n| + |a ^ n * (1 - a)| := abs_add_le _ _
      _ ≤ (n : ℝ) * |1 - a| + 1 * |1 - a| := by
        apply add_le_add ih
        rw [abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg a) ha) (abs_nonneg _)
      _ = ((n + 1 : ℕ) : ℝ) * |1 - a| := by push_cast; ring

/-- The cosine increment is bounded by half the squared frequency. -/
theorem one_sub_cos_abs_le (x : ℝ) : |1 - Real.cos x| ≤ x ^ 2 / 2 := by
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one x))]
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

/-- The bound is uniform in the number of scaled rounds, including zero rounds. -/
theorem normalized_cos_increment_le (n : ℕ) (t : ℝ) :
    |1 - (Real.cos (t / Real.sqrt (n : ℝ))) ^ n| ≤ t ^ 2 / 2 := by
  by_cases hn : n = 0
  · subst n
    simpa using (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  calc
    _ ≤ (n : ℝ) * |1 - Real.cos (t / Real.sqrt (n : ℝ))| :=
      one_sub_pow_abs_le _ (Real.abs_cos_le_one _) n
    _ ≤ (n : ℝ) * ((t / Real.sqrt (n : ℝ)) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (one_sub_cos_abs_le _) (Nat.cast_nonneg n)
    _ = t ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      field_simp
      ring

/-- A coordinate alone has the characteristic function of a sum of fair signs. -/
theorem pairTotalLaw_coordinate_charFun (r : ℝ) (hr : |r| ≤ 1) (n : ℕ)
    (j : Fin 2) (t : ℝ) :
    charFunDual (pairTotalLaw r hr n)
      (t • (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ)) =
        (Real.cos (t / Real.sqrt (n : ℝ)) : ℂ) ^ n := by
  have hk0 (s : ℝ) : pairKernel r s 0 = Real.cos s := by
    simp only [pairKernel, add_zero, sub_zero]
    ring
  have hk1 (s : ℝ) : pairKernel r 0 s = Real.cos s := by
    simp only [pairKernel, zero_add, zero_sub, Real.cos_neg]
    ring
  fin_cases j
  · calc
      _ = charFunDual (pairTotalLaw r hr n) (pairReport t 0) := by
        congr 1
        ext x
        simp [pairReport]
      _ = _ := by rw [pairTotalLaw_charFun]; simp only [zero_div, hk0]
  · calc
      _ = charFunDual (pairTotalLaw r hr n) (pairReport 0 t) := by
        congr 1
        ext x
        simp [pairReport]
      _ = _ := by rw [pairTotalLaw_charFun]; simp only [zero_div, hk1]

/-- Every coordinate has the same uniform quadratic characteristic increment bound. -/
theorem coordinate_characteristic_increment_le (r : ℝ) (hr : |r| ≤ 1)
    (n : ℕ) (j : Fin 2) (t : ℝ) :
    ‖1 - charFunDual (pairTotalLaw r hr n)
      (t • (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ))‖ ≤ t ^ 2 / 2 := by
  rw [pairTotalLaw_coordinate_charFun, ← Complex.ofReal_pow, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact normalized_cos_increment_le n t

/-- A quadratic characteristic increment bounds each coordinate tail of a probability law. -/
theorem coordinate_tail_of_increment (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ]
    (j : Fin 2)
    (h : ∀ t : ℝ, ‖1 - charFunDual μ
      (t • (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ))‖ ≤ t ^ 2 / 2)
    (R : ℝ) (hR : 0 < R) : μ.real {x | R < |x j|} ≤ 4 / R ^ 2 := by
  have ha : 0 ≤ 2 * R⁻¹ := by positivity
  have horder : -2 * R⁻¹ ≤ 2 * R⁻¹ := by linarith only [ha]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -2 * R⁻¹) (b := 2 * R⁻¹) (C := (2 * R⁻¹) ^ 2 / 2)
    (f := fun t => 1 - charFunDual μ
      (t • (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ))) (by
      intro t ht
      rw [Set.uIoc_of_le horder] at ht
      have ht2 : t ^ 2 ≤ (2 * R⁻¹) ^ 2 := by
        have hlo := ht.1
        have hhi := ht.2
        nlinarith only [mul_nonneg (show 0 ≤ t + 2 * R⁻¹ by linarith only [hlo])
          (show 0 ≤ 2 * R⁻¹ - t by linarith only [hhi])]
      exact (h t).trans (by linarith only [ht2]))
  calc
    _ ≤ 2⁻¹ * R * ‖∫ t in -2 * R⁻¹..2 * R⁻¹, 1 - charFunDual μ
        (t • (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ))‖ :=
      measureReal_abs_dual_gt_le_integral_charFunDual (μ := μ)
        (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ) hR
    _ ≤ 2⁻¹ * R * ((2 * R⁻¹) ^ 2 / 2 * |2 * R⁻¹ - -2 * R⁻¹|) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = 4 / R ^ 2 := by
      rw [abs_of_nonneg (by linarith only [horder])]
      field_simp
      ring

/-- The tail bound is uniform in the number of rounds and in the correlation parameter. -/
theorem pairTotalLaw_coordinate_tail (r : ℝ) (hr : |r| ≤ 1) (n : ℕ) (j : Fin 2)
    (R : ℝ) (hR : 0 < R) : (pairTotalLaw r hr n).real {x | R < |x j|} ≤ 4 / R ^ 2 :=
  coordinate_tail_of_increment _ j (coordinate_characteristic_increment_le r hr n j) R hR

/-- Restrict a real value to the closed interval from `-b` to `b`. -/
def clampValue (b x : ℝ) : ℝ := max (-b) (min b x)

/-- The restricted value stays in the requested interval. -/
theorem clampValue_abs_le {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : |clampValue b x| ≤ b := by
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Restriction leaves values already in the interval unchanged. -/
theorem clampValue_eq_self {b x : ℝ} (hx : |x| ≤ b) : clampValue b x = x := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  simp only [clampValue, min_eq_right hhi, max_eq_right hlo]

/-- Restriction cannot increase distance from a value in the interval. -/
theorem clampValue_error {b v : ℝ} (hv : |v| ≤ b) (u : ℝ) :
    |clampValue b u - v| ≤ |u - v| := by
  have h := ((LipschitzWith.id.const_min b).const_max (-b)).dist_le_mul u v
  have h' : |clampValue b u - clampValue b v| ≤ |u - v| := by
    simpa only [clampValue, Function.id_def, NNReal.coe_one, one_mul, Real.dist_eq] using h
  simpa only [clampValue_eq_self hv] using h'

/-- Polynomial evaluation in bounded continuous functions is pointwise evaluation. -/
theorem bounded_aeval_apply {E : Type*} [TopologicalSpace E]
    (p : Polynomial ℝ) (g : E →ᵇ ℝ) (x : E) :
    (Polynomial.aeval g p) x = p.eval (g x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

/-- A separating algebra approximates a bounded test on a compact set while keeping a
uniform bound on the approximant over the whole state space. -/
theorem bounded_algebra_approximation {E : Type*} [TopologicalSpace E]
    (A : Subalgebra ℝ (E →ᵇ ℝ))
    (hA : (A.map (BoundedContinuousFunction.toContinuousMapₐ ℝ)).SeparatesPoints)
    (f : E →ᵇ ℝ) {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ A, (∀ x, |g x| ≤ ‖f‖ + ε) ∧ (∀ x ∈ K, |g x - f x| < ε) := by
  obtain ⟨g', hg', happrox⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      hA f.toContinuousMap hK (half_pos hε)
  obtain ⟨g, hg, hgg'⟩ := Subalgebra.mem_map.mp hg'
  rw [← hgg'] at happrox
  change ∀ x ∈ K, |g x - f x| < ε / 2 at happrox
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn
    (-‖g‖) ‖g‖ (clampValue ‖f‖) (by unfold clampValue; fun_prop) (ε / 2) (half_pos hε)
  let gp : A := Polynomial.aeval (⟨g, hg⟩ : A) p
  have hnear (x : E) : |(gp : E →ᵇ ℝ) x - clampValue ‖f‖ (g x)| < ε / 2 := by
    change |((Polynomial.aeval (⟨g, hg⟩ : A) p : E →ᵇ ℝ) x) - _| < _
    rw [Polynomial.aeval_subalgebra_coe, bounded_aeval_apply]
    apply hp
    exact abs_le.mp (BoundedContinuousFunction.norm_coe_le_norm g x)
  refine ⟨gp, gp.property, ?_, ?_⟩
  · intro x
    have he := abs_lt.mp (hnear x)
    have hb := abs_le.mp (clampValue_abs_le (norm_nonneg f) (g x))
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro x hx
    have he := hnear x
    have hgx := happrox x hx
    have hc := clampValue_error (BoundedContinuousFunction.norm_coe_le_norm f x) (g x)
    have ht := abs_sub_le ((gp : E →ᵇ ℝ) x) (clampValue ‖f‖ (g x)) (f x)
    linarith

/-! ## From characteristic limits to weak convergence -/

/-- Uniform approximation on a compact set and small exterior mass control the integral error. -/
theorem integral_approximation_bound {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (f g : E →ᵇ ℝ) {K : Set E} (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 ≤ δ)
    (hg : ∀ x, |g x| ≤ ‖f‖ + δ) (hnear : ∀ x ∈ K, |g x - f x| ≤ δ) :
    |(∫ x, g x ∂μ) - ∫ x, f x ∂μ| ≤ δ + (2 * ‖f‖ + δ) * μ.real Kᶜ := by
  have hint : Integrable (fun x => g x - f x) μ := (g.integrable μ).sub (f.integrable μ)
  have hsplit := integral_add_compl hK hint
  have hinside := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := K)
    (f := fun x => g x - f x) (measure_lt_top μ K)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hnear x hx)
  have houtside := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := Kᶜ)
    (f := fun x => g x - f x) (C := 2 * ‖f‖ + δ) (measure_lt_top μ Kᶜ) (by
      intro x _
      rw [Real.norm_eq_abs]
      have hf : |f x| ≤ ‖f‖ := norm_coe_le_norm f x
      calc
        |g x - f x| ≤ |g x| + |f x| := abs_sub _ _
        _ ≤ (‖f‖ + δ) + ‖f‖ := add_le_add (hg x) hf
        _ = 2 * ‖f‖ + δ := by ring)
  rw [← integral_sub (g.integrable μ) (f.integrable μ), ← hsplit]
  have hμ : μ.real K ≤ 1 := measureReal_le_one
  calc
    _ ≤ |∫ x in K, g x - f x ∂μ| + |∫ x in Kᶜ, g x - f x ∂μ| := abs_add_le _ _
    _ ≤ δ * μ.real K + (2 * ‖f‖ + δ) * μ.real Kᶜ := add_le_add hinside houtside
    _ ≤ δ + (2 * ‖f‖ + δ) * μ.real Kᶜ := by nlinarith [mul_le_mul_of_nonneg_left hμ hδ]

/-- A tight family needs convergence only on a separating algebra of bounded tests. -/
theorem tight_algebra_integral_limit {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] (μs : ℕ → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (htight : IsTightMeasureSet (Set.range (fun n => (μs n : Measure E)) ∪ {(μ : Measure E)}))
    (A : Subalgebra ℝ (E →ᵇ ℝ))
    (hA : (A.map (toContinuousMapₐ ℝ)).SeparatesPoints)
    (hconv : ∀ g ∈ A, Tendsto (fun n => ∫ x, g x ∂(μs n : Measure E)) atTop
      (𝓝 (∫ x, g x ∂(μ : Measure E)))) (f : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f x ∂(μs n : Measure E)) atTop
      (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := min 1 (ε / (8 * (‖f‖ + 1)))
  have hd : 0 < 8 * (‖f‖ + 1) := by positivity
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε hd)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : 8 * (‖f‖ + 1) * δ ≤ ε := by
    have h := (le_div_iff₀ hd).mp (min_le_right 1 (ε / (8 * (‖f‖ + 1))))
    nlinarith
  obtain ⟨K, hK, htail⟩ := IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
    (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
  obtain ⟨g, hgA, hg, hnear⟩ := bounded_algebra_approximation A hA f hK hδ
  have herr (ν : ProbabilityMeasure E)
      (hν : (ν : Measure E) ∈ Set.range (fun n => (μs n : Measure E)) ∪ {(μ : Measure E)}) :
      |(∫ x, g x ∂(ν : Measure E)) - ∫ x, f x ∂(ν : Measure E)| ≤
        δ + (2 * ‖f‖ + δ) * δ := by
    have ht : (ν : Measure E).real Kᶜ ≤ δ :=
      ENNReal.toReal_le_of_le_ofReal hδ.le (htail _ hν)
    exact (integral_approximation_bound (ν : Measure E) f g hK.measurableSet hδ.le hg
      (fun x hx => (hnear x hx).le)).trans (by
        exact add_le_add_left (mul_le_mul_of_nonneg_left ht (by positivity)) δ)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hconv g hgA)) δ hδ
  refine ⟨N, ?_⟩
  intro n hn
  have hm := hN n hn
  rw [Real.dist_eq] at hm ⊢
  have hnerr := herr (μs n) (Or.inl ⟨n, rfl⟩)
  have hμerr := herr μ (Or.inr rfl)
  have htriangle := abs_sub_le (∫ x, f x ∂(μs n : Measure E))
    (∫ x, g x ∂(μs n : Measure E)) (∫ x, f x ∂(μ : Measure E))
  have htriangle' := abs_sub_le (∫ x, g x ∂(μs n : Measure E))
    (∫ x, g x ∂(μ : Measure E)) (∫ x, f x ∂(μ : Measure E))
  rw [abs_sub_comm (∫ x, f x ∂(μs n : Measure E)) (∫ x, g x ∂(μs n : Measure E))] at htriangle
  have hδsq : δ * δ ≤ δ := mul_le_of_le_one_right hδ.le hδ1
  have hmargin : 0 < (4 * ‖f‖ + 3) * δ := by positivity
  nlinarith [norm_nonneg f]

/-- For tight probability measures, convergence of all continuous linear characteristic
reports implies weak convergence. The proof uses finite character polynomials and bounded
approximation on compact sets. -/
theorem tight_charFunDual_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μs : ℕ → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (htight : IsTightMeasureSet (Set.range (fun n => (μs n : Measure E)) ∪ {(μ : Measure E)}))
    (hchar : ∀ a : NormedSpace.Dual ℝ E,
      Tendsto (fun n => charFunDual (μs n : Measure E) a) atTop
        (𝓝 (charFunDual (μ : Measure E) a))) : Tendsto μs atTop (𝓝 μ) := by
  let L : E →ₗ[ℝ] NormedSpace.Dual ℝ E →ₗ[ℝ] ℝ :=
    isBoundedBilinearMap_apply.symm.toContinuousLinearMap.toLinearMap₁₂
  have hL : Continuous (fun p : E × NormedSpace.Dual ℝ E => L p.1 p.2) :=
    isBoundedBilinearMap_apply.symm.continuous
  have hLsep : ∀ v ≠ 0, L v ≠ 0 := by
    intro v hv
    rw [ne_eq, LinearMap.ext_iff]
    simp only [LinearMap.zero_apply, not_forall]
    change ∃ a : NormedSpace.Dual ℝ E, a v ≠ 0
    by_contra! h
    exact hv (NormedSpace.eq_zero_of_forall_dual_eq_zero _ h)
  let A : StarSubalgebra ℂ (E →ᵇ ℂ) := charPoly Real.continuous_probChar hL
  have hA : (A.map (toContinuousMapStarₐ ℂ)).SeparatesPoints :=
    separatesPoints_charPoly Real.continuous_probChar Real.probChar_ne_one hL hLsep
  have hconvA : ∀ g ∈ A, Tendsto (fun n => ∫ x, g x ∂(μs n : Measure E)) atTop
      (𝓝 (∫ x, g x ∂(μ : Measure E))) := by
    intro g hg
    change g ∈ (charAlgHom Real.continuous_probChar hL).range at hg
    obtain ⟨w, rfl⟩ := hg
    have hint (ν : ProbabilityMeasure E) :
        (∫ x, charAlgHom Real.continuous_probChar hL w x ∂(ν : Measure E)) =
          ∑ a ∈ w.support, w a * charFunDual (ν : Measure E) a := by
      simp only [charAlgHom_apply]
      change (∫ x, ∑ a ∈ w.support, w a * (char Real.continuous_probChar hL a) x
        ∂(ν : Measure E)) = _
      rw [integral_finset_sum w.support (fun a _ =>
        ((char Real.continuous_probChar hL a).integrable (ν : Measure E)).const_mul (w a))]
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_const_mul]
      rfl
    change Tendsto (fun n => ∫ x, charAlgHom Real.continuous_probChar hL w x
      ∂(μs n : Measure E)) atTop
      (𝓝 (∫ x, charAlgHom Real.continuous_probChar hL w x ∂(μ : Measure E)))
    simp_rw [hint]
    exact tendsto_finset_sum _ (fun a _ => tendsto_const_nhds.mul (hchar a))
  let AReal := (A.restrictScalars ℝ).comap
    (RCLike.ofRealAm.compLeftContinuousBounded ℝ RCLike.lipschitzWith_ofReal)
  have hAReal : (AReal.map (toContinuousMapₐ ℝ)).SeparatesPoints := by
    rw [RCLike.restrict_toContinuousMap_eq_toContinuousMapStar_restrict]
    exact Subalgebra.SeparatesPoints.rclike_to_real hA
  have hconvReal : ∀ g ∈ AReal, Tendsto (fun n => ∫ x, g x ∂(μs n : Measure E)) atTop
      (𝓝 (∫ x, g x ∂(μ : Measure E))) := by
    intro g hg
    have h := hconvA _ hg
    change Tendsto (fun n => ∫ x, (g x : ℂ) ∂(μs n : Measure E)) atTop
      (𝓝 (∫ x, (g x : ℂ) ∂(μ : Measure E))) at h
    simp_rw [integral_complex_ofReal] at h
    simpa only [Complex.ofReal_re] using (Complex.continuous_re.tendsto _).comp h
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  exact tight_algebra_integral_limit μs μ htight AReal hAReal hconvReal

/-- A square contains all but a uniformly bounded mass of every normalized pair-sum law. -/
theorem pairTotalLaw_box_tail (r : ℝ) (hr : |r| ≤ 1) (n : ℕ) (R : ℝ) (hR : 0 < R) :
    (pairTotalLaw r hr n).real
      (Set.Icc (fun _ : Fin 2 => -R) (fun _ : Fin 2 => R))ᶜ ≤ 8 / R ^ 2 := by
  have hsub : (Set.Icc (fun _ : Fin 2 => -R) (fun _ : Fin 2 => R))ᶜ ⊆
      {x : Fin 2 → ℝ | R < |x 0|} ∪ {x : Fin 2 → ℝ | R < |x 1|} := by
    intro x hx
    by_contra hn
    have h0 : |x 0| ≤ R := le_of_not_gt (fun h => hn (Or.inl h))
    have h1 : |x 1| ≤ R := le_of_not_gt (fun h => hn (Or.inr h))
    apply hx
    constructor
    · intro j
      fin_cases j
      · exact (abs_le.mp h0).1
      · exact (abs_le.mp h1).1
    · intro j
      fin_cases j
      · exact (abs_le.mp h0).2
      · exact (abs_le.mp h1).2
  calc
    _ ≤ (pairTotalLaw r hr n).real
        ({x : Fin 2 → ℝ | R < |x 0|} ∪ {x : Fin 2 → ℝ | R < |x 1|}) := measureReal_mono hsub
    _ ≤ (pairTotalLaw r hr n).real {x | R < |x 0|} +
        (pairTotalLaw r hr n).real {x | R < |x 1|} := measureReal_union_le _ _
    _ ≤ 4 / R ^ 2 + 4 / R ^ 2 := add_le_add
      (pairTotalLaw_coordinate_tail r hr n 0 R hR)
      (pairTotalLaw_coordinate_tail r hr n 1 R hR)
    _ = 8 / R ^ 2 := by ring

/-- The two coordinate bounds give tightness of the entire family, uniformly in the round count. -/
theorem pairTotalLaw_tight (r : ℝ) (hr : |r| ≤ 1) :
    IsTightMeasureSet (Set.range (pairTotalLaw r hr)) := by
  apply IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases htop : ε = ⊤
  · subst ε
    exact ⟨∅, isCompact_empty, fun _ _ => le_top⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  let R : ℝ := 8 / ε.toReal + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := by
    dsimp [R]
    linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 8) he.le]
  have hproduct : ε.toReal * R = 8 + ε.toReal := by
    dsimp [R]
    field_simp
  have hbound : 8 / R ^ 2 ≤ ε.toReal := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    have hs : R ≤ R ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs he.le
    nlinarith
  refine ⟨Set.Icc (fun _ : Fin 2 => -R) (fun _ : Fin 2 => R), isCompact_Icc, ?_⟩
  rintro ν ⟨n, rfl⟩
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) htop).mp
  exact (pairTotalLaw_box_tail r hr n R hR).trans hbound

def pairTotalProbability (r : ℝ) (hr : |r| ≤ 1) (n : ℕ) :
    ProbabilityMeasure (Fin 2 → ℝ) := ⟨pairTotalLaw r hr n, inferInstance⟩

def pairNormalProbability (r : ℝ) : ProbabilityMeasure (Fin 2 → ℝ) :=
  ⟨GaussianTotals.pairNormal r, inferInstance⟩

/-- The normalized sums of independent binary pairs converge weakly to the constructed
Gaussian with covariance parameter r. Degenerate endpoints r = -1 and r = 1 are included. -/
theorem pairTotalLaw_weak_limit (r : ℝ) (hr : |r| ≤ 1) :
    Tendsto (pairTotalProbability r hr) atTop (𝓝 (pairNormalProbability r)) := by
  apply tight_charFunDual_limit
  · exact (pairTotalLaw_tight r hr).union (isTightMeasureSet_singleton (μ := GaussianTotals.pairNormal r))
  · intro L
    exact pairTotalLaw_all_characteristic_limit r hr L

/-- The weak limit gives convergence for every bounded continuous real test. -/
theorem pairTotalLaw_bounded_test_limit (r : ℝ) (hr : |r| ≤ 1) (f : (Fin 2 → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f x ∂pairTotalLaw r hr n) atTop
      (𝓝 (∫ x, f x ∂GaussianTotals.pairNormal r)) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (pairTotalLaw_weak_limit r hr) f

end

end OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit
