import OperatorKO7.Meta.BoundaryObserver.FourTestTables
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false

/-!
# Gaussian laws for common observations

Constructs actual probability measures from finitely many independent normal contributions,
using convolution. Their linear projections, means, variances and covariance are derived from
that construction. Zero and singular covariance are included.
Relation: probability laws and linear report maps. Trust: kernel-only.
The weak convergence of normalized binary rounds is a separate obligation.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace OperatorKO7.Meta.BoundaryObserver.GaussianTotals

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- Put a scalar contribution along one report vector. -/
def axisLinear (u : E) : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight u

/-- The law of the sum of independent standard normal contributions along a finite list of
vectors. The empty sum is a point mass, so singular cases require no exception. -/
def gaussianSum : List E → Measure E
  | [] => Measure.dirac 0
  | u :: us => ((gaussianReal 0 1).map (axisLinear u)).conv (gaussianSum us)

/-- The variance of a linear report of the constructed sum. -/
def varianceParameter : List E → (E →L[ℝ] ℝ) → ℝ≥0
  | [], _ => 0
  | u :: us, L => Real.toNNReal ((L u) ^ 2) + varianceParameter us L

/-- Every constructed law is Gaussian, hence a probability law. -/
instance gaussianSum_isGaussian (us : List E) : IsGaussian (gaussianSum us) := by
  induction us with
  | nil => change IsGaussian (Measure.dirac (0 : E)); infer_instance
  | cons u us ih =>
    letI : IsGaussian (gaussianSum us) := ih
    change IsGaussian (((gaussianReal 0 1).map (axisLinear u)).conv (gaussianSum us))
    infer_instance

omit [SecondCountableTopology E] in
/-- A scalar report of one normal contribution has exactly the squared report coefficient as
its variance. -/
theorem axis_projection (u : E) (L : E →L[ℝ] ℝ) :
    ((gaussianReal 0 1).map (axisLinear u)).map L =
      gaussianReal 0 (Real.toNNReal ((L u) ^ 2)) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  change (gaussianReal 0 1).map (L.comp (axisLinear u)) = _
  rw [gaussianReal_map_continuousLinearMap]
  simp [axisLinear]

/-- Every linear projection of the constructed joint law is the prescribed centered Gaussian.
The theorem determines its probability law, not only a formal covariance matrix. -/
theorem gaussianSum_projection (us : List E) (L : E →L[ℝ] ℝ) :
    (gaussianSum us).map L = gaussianReal 0 (varianceParameter us L) := by
  induction us with
  | nil =>
    change (Measure.dirac (0 : E)).map L = gaussianReal 0 0
    rw [Measure.map_dirac (by fun_prop), map_zero, gaussianReal_zero_var]
  | cons u us ih =>
    rw [gaussianSum, Measure.map_conv_continuousLinearMap L, axis_projection, ih,
      gaussianReal_conv_gaussianReal]
    simp only [zero_add, varianceParameter]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The nonnegative parameter agrees with the real sum of squared coefficients. -/
theorem varianceParameter_coe (us : List E) (L : E →L[ℝ] ℝ) :
    (varianceParameter us L : ℝ) = (us.map (fun u => (L u) ^ 2)).sum := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [varianceParameter, NNReal.coe_add, Real.coe_toNNReal',
      max_eq_left (sq_nonneg (L u)), List.map_cons, List.sum_cons, ih]

/-- Every linear report of the constructed law has mean zero. -/
theorem gaussianSum_mean (us : List E) (L : E →L[ℝ] ℝ) :
    ∫ x, L x ∂gaussianSum us = 0 := by
  calc
    (∫ x, L x ∂gaussianSum us) = ∫ x, x ∂((gaussianSum us).map L) :=
      (integral_map (μ := gaussianSum us) (φ := L) (f := fun x : ℝ => x)
        (by fun_prop) (by fun_prop)).symm
    _ = 0 := by rw [gaussianSum_projection]; exact integral_id_gaussianReal

/-- The variance is the actual variance of the probability law. -/
theorem gaussianSum_variance (us : List E) (L : E →L[ℝ] ℝ) :
    Var[L; gaussianSum us] = (us.map (fun u => (L u) ^ 2)).sum := by
  rw [← variance_id_map (by fun_prop), gaussianSum_projection, variance_id_gaussianReal]
  exact varianceParameter_coe us L

/-- Polarization computes the actual covariance of any two reports of the joint law. -/
theorem gaussianSum_covariance (us : List E) (L K : E →L[ℝ] ℝ) :
    cov[L, K; gaussianSum us] = (us.map (fun u => L u * K u)).sum := by
  have hL : MemLp L 2 (gaussianSum us) := IsGaussian.memLp_dual _ L 2 (by simp)
  have hK : MemLp K 2 (gaussianSum us) := IsGaussian.memLp_dual _ K 2 (by simp)
  have hv := variance_add hL hK
  change Var[(L + K : E →L[ℝ] ℝ); gaussianSum us] =
    Var[L; gaussianSum us] + 2 * cov[L, K; gaussianSum us] + Var[K; gaussianSum us] at hv
  rw [gaussianSum_variance, gaussianSum_variance, gaussianSum_variance] at hv
  have hp : (us.map (fun u => ((L + K) u) ^ 2)).sum =
      (us.map (fun u => (L u) ^ 2)).sum +
      2 * (us.map (fun u => L u * K u)).sum + (us.map (fun u => (K u) ^ 2)).sum := by
    clear hL hK hv
    induction us with
    | nil => simp
    | cons u us ih =>
      simp only [List.map_cons, List.sum_cons, ContinuousLinearMap.add_apply] at ih ⊢
      rw [ih]
      ring
  linarith

/-- The covariance matrix of a finite family of real reports on one probability space. -/
def covarianceMatrix {Ω I : Type*} [MeasurableSpace Ω]
    (X : I → Ω → ℝ) (μ : Measure Ω) : Matrix I I ℝ := fun i j => cov[X i, X j; μ]

/-- Covariance on one underlying finite measure is positive semidefinite. This applies to
non-Gaussian laws as well and uses the actual second moments of the reports. -/
theorem covarianceMatrix_posSemidef {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (X : I → Ω → ℝ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hX : ∀ i, MemLp (X i) 2 μ) : (covarianceMatrix X μ).PosSemidef := by
  classical
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, covarianceMatrix, star_trivial]
    exact covariance_comm _ _
  · intro c
    have hLP : ∀ i, MemLp (fun ω => c i * X i ω) 2 μ := fun i => (hX i).const_mul (c i)
    have hv := variance_nonneg (fun ω => ∑ i, c i * X i ω) μ
    rw [variance_fun_sum hLP] at hv
    simp_rw [covariance_mul_left, covariance_mul_right] at hv
    simpa only [covarianceMatrix, Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hv

/-- A matrix specifies one normal contribution per row to its vector of column reports. -/
def matrixLaw {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℝ) : Measure (Fin m → ℝ) :=
  gaussianSum (List.ofFn B)

/-- The matrix construction is an actual Gaussian probability measure. -/
instance matrixLaw_isGaussian {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℝ) :
    IsGaussian (matrixLaw B) := gaussianSum_isGaussian _

/-- The matrix law is centered in every coordinate. -/
theorem matrixLaw_mean {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℝ) (i : Fin m) :
    ∫ x, x i ∂matrixLaw B = 0 :=
  gaussianSum_mean (List.ofFn B) (ContinuousLinearMap.proj i)

/-- Its covariance is the Gram matrix of the supplied rows. -/
theorem matrixLaw_covariance {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℝ) :
    covarianceMatrix (fun i x => x i) (matrixLaw B) = B.conjTranspose * B := by
  ext i j
  change cov[(ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ),
    (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ); gaussianSum (List.ofFn B)] = _
  rw [gaussianSum_covariance]
  simp only [List.map_ofFn, List.sum_ofFn, ContinuousLinearMap.proj_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, Function.comp_apply]

/-- A matrix is a centered Gaussian covariance exactly when it is positive semidefinite.
The forward construction includes singular matrices and dimension zero. -/
theorem psd_iff_gaussian_covariance {m : ℕ} (G : Matrix (Fin m) (Fin m) ℝ) :
    G.PosSemidef ↔ ∃ μ : Measure (Fin m → ℝ), IsGaussian μ ∧
      (∀ i, ∫ x, x i ∂μ = 0) ∧ covarianceMatrix (fun i x => x i) μ = G := by
  constructor
  · intro hG
    obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hG
    exact ⟨matrixLaw B, inferInstance, matrixLaw_mean B, (matrixLaw_covariance B).trans hB.symm⟩
  · rintro ⟨μ, hμ, _, hG⟩
    letI : IsGaussian μ := hμ
    rw [← hG]
    exact covarianceMatrix_posSemidef (fun i x => x i) μ
      (fun i => IsGaussian.memLp_dual μ (ContinuousLinearMap.proj i) 2 (by simp))

/-- A common centered Gaussian law of the four totals, with unit coordinate variances and
the specified cross-correlations. Joint Gaussianity also fixes each two-coordinate normal law. -/
def HasGaussianTotals (d : FourTestTables.Table) : Prop :=
  ∃ μ : Measure (Fin 4 → ℝ), IsGaussian μ ∧ (∀ i, ∫ x, x i ∂μ = 0) ∧
    (∀ i, covarianceMatrix (fun i x => x i) μ i i = 1) ∧
    covarianceMatrix (fun i x => x i) μ 0 2 = FourTestTables.corr d false false ∧
    covarianceMatrix (fun i x => x i) μ 0 3 = FourTestTables.corr d false true ∧
    covarianceMatrix (fun i x => x i) μ 1 2 = FourTestTables.corr d true false ∧
    covarianceMatrix (fun i x => x i) μ 1 3 = FourTestTables.corr d true true

/-- The vector criterion is equivalent to an actual common Gaussian law of the four totals,
not just to the existence of a matrix. -/
theorem hasVectors_iff_gaussianTotals (d : FourTestTables.Table) :
    FourTestTables.HasVectors d ↔ HasGaussianTotals d := by
  rw [FourTestTables.hasVectors_iff_psd_completion]
  constructor
  · rintro ⟨G, hG, hdiag, h02, h03, h12, h13⟩
    obtain ⟨μ, hμ, hmean, hcov⟩ := (psd_iff_gaussian_covariance G).mp hG
    refine ⟨μ, hμ, hmean, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hcov] using hdiag
    · simpa only [hcov] using h02
    · simpa only [hcov] using h03
    · simpa only [hcov] using h12
    · simpa only [hcov] using h13
  · rintro ⟨μ, hμ, hmean, hdiag, h02, h03, h12, h13⟩
    exact ⟨covarianceMatrix (fun i x => x i) μ,
      (psd_iff_gaussian_covariance _).mpr ⟨μ, hμ, hmean, rfl⟩,
      hdiag, h02, h03, h12, h13⟩

/-- Any common law with the required second moments, Gaussian or otherwise, satisfies the
same vector criterion. This is the necessity half for arbitrary candidate total observers. -/
theorem common_moments_imply_vectors (d : FourTestTables.Table)
    (μ : Measure (Fin 4 → ℝ)) [IsFiniteMeasure μ]
    (hLp : ∀ i, MemLp (fun x => x i) 2 μ)
    (hdiag : ∀ i, covarianceMatrix (fun i x => x i) μ i i = 1)
    (h02 : covarianceMatrix (fun i x => x i) μ 0 2 = FourTestTables.corr d false false)
    (h03 : covarianceMatrix (fun i x => x i) μ 0 3 = FourTestTables.corr d false true)
    (h12 : covarianceMatrix (fun i x => x i) μ 1 2 = FourTestTables.corr d true false)
    (h13 : covarianceMatrix (fun i x => x i) μ 1 3 = FourTestTables.corr d true true) :
    FourTestTables.HasVectors d :=
  (FourTestTables.hasVectors_iff_psd_completion d).mpr
    ⟨covarianceMatrix (fun i x => x i) μ,
      covarianceMatrix_posSemidef _ μ hLp, hdiag, h02, h03, h12, h13⟩

/-- A linear report on a finite vector space is the stated weighted sum of coordinates. -/
theorem linear_report_coordinates {m : ℕ} (L : (Fin m → ℝ) →L[ℝ] ℝ) :
    (L : (Fin m → ℝ) → ℝ) = fun x =>
      ∑ i, L (fun j => if i = j then 1 else 0) * x i := by
  funext x
  have h := LinearMap.pi_apply_eq_sum_univ L.toLinearMap x
  simpa only [smul_eq_mul, mul_comm] using h

/-- The mean of a linear report is determined by the coordinate means. -/
theorem linear_mean_coordinates {m : ℕ} (μ : Measure (Fin m → ℝ)) [IsFiniteMeasure μ]
    (hLp : ∀ i, MemLp (fun x => x i) 2 μ) (L : (Fin m → ℝ) →L[ℝ] ℝ) :
    ∫ x, L x ∂μ = ∑ i, L (fun j => if i = j then 1 else 0) * ∫ x, x i ∂μ := by
  conv_lhs => rw [linear_report_coordinates L]
  rw [integral_finset_sum]
  · simp only [integral_const_mul]
  · intro i _
    exact ((hLp i).integrable (by norm_num)).const_mul _

/-- The variance of a linear report is determined by the actual coordinate covariance. -/
theorem linear_variance_coordinates {m : ℕ} (μ : Measure (Fin m → ℝ)) [IsFiniteMeasure μ]
    (hLp : ∀ i, MemLp (fun x => x i) 2 μ) (L : (Fin m → ℝ) →L[ℝ] ℝ) :
    Var[L; μ] = ∑ i, ∑ j,
      L (fun k => if i = k then 1 else 0) * L (fun k => if j = k then 1 else 0) *
        covarianceMatrix (fun i x => x i) μ i j := by
  conv_lhs => rw [linear_report_coordinates L]
  rw [variance_fun_sum (fun i => (hLp i).const_mul _)]
  simp_rw [covariance_mul_left, covariance_mul_right]
  simp only [covarianceMatrix]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Two finite-dimensional Gaussian laws with equal coordinate means and covariance are
identical as measures. -/
theorem gaussian_eq_of_moments {m : ℕ} (μ ν : Measure (Fin m → ℝ))
    [IsGaussian μ] [IsGaussian ν]
    (hmean : ∀ i, (∫ x, x i ∂μ) = ∫ x, x i ∂ν)
    (hcov : covarianceMatrix (fun i x => x i) μ = covarianceMatrix (fun i x => x i) ν) :
    μ = ν := by
  have hμ : ∀ i, MemLp (fun x => x i) 2 μ :=
    fun i => IsGaussian.memLp_dual μ (ContinuousLinearMap.proj i) 2 (by simp)
  have hν : ∀ i, MemLp (fun x => x i) 2 ν :=
    fun i => IsGaussian.memLp_dual ν (ContinuousLinearMap.proj i) 2 (by simp)
  apply Measure.ext_of_charFunDual
  funext L
  have hm : (∫ x, L x ∂μ) = ∫ x, L x ∂ν := by
    rw [linear_mean_coordinates μ hμ L, linear_mean_coordinates ν hν L]
    simp_rw [hmean]
  have hv : Var[L; μ] = Var[L; ν] := by
    rw [linear_variance_coordinates μ hμ L, linear_variance_coordinates ν hν L, hcov]
  simp_rw [IsGaussian.charFunDual_eq, integral_complex_ofReal, hm, hv]

/-- Select a finite family of coordinates from the common report. -/
def selectCoordinates {m n : ℕ} (r : Fin n → Fin m) : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (r j))

/-- Selection transports the actual covariance, even for non-Gaussian candidate laws. -/
theorem selected_covariance {m n : ℕ} (μ : Measure (Fin m → ℝ))
    (r : Fin n → Fin m) (i j : Fin n) :
    covarianceMatrix (fun i x => x i) (μ.map (selectCoordinates r)) i j =
      covarianceMatrix (fun i x => x i) μ (r i) (r j) := by
  exact covariance_map_fun (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable (selectCoordinates r).measurable.aemeasurable

/-- Selection transports coordinate means. -/
theorem selected_mean {m n : ℕ} (μ : Measure (Fin m → ℝ))
    (r : Fin n → Fin m) (i : Fin n) :
    (∫ x, x i ∂(μ.map (selectCoordinates r))) = ∫ x, x (r i) ∂μ := by
  exact integral_map (selectCoordinates r).measurable.aemeasurable
    (measurable_pi_apply i).aestronglyMeasurable

/-- The centered pair normal with correlation parameter `r`, constructed from two independent
scalar normals. At `r = ±1` the second contribution vanishes. -/
def pairNormal (r : ℝ) : Measure (Fin 2 → ℝ) :=
  matrixLaw (!![1, r; 0, Real.sqrt (1 - r ^ 2)])

instance pairNormal_isGaussian (r : ℝ) : IsGaussian (pairNormal r) := matrixLaw_isGaussian _

/-- The pair normal is centered. -/
theorem pairNormal_mean (r : ℝ) (i : Fin 2) : ∫ x, x i ∂pairNormal r = 0 :=
  matrixLaw_mean _ i

/-- Exact covariance of the pair normal, including the singular endpoint cases. -/
theorem pairNormal_covariance (r : ℝ) (hr : |r| ≤ 1) :
    covarianceMatrix (fun i x => x i) (pairNormal r) = !![1, r; r, 1] := by
  have hr2 : r ^ 2 ≤ 1 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hr
    nlinarith
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - r ^ 2)
  rw [pairNormal, matrixLaw_covariance]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  nlinarith

/-- A pair marginal of a centered Gaussian is the specified pair normal once the two variances
and their covariance agree. This is equality of probability measures. -/
theorem gaussian_pair_marginal {m : ℕ} (μ : Measure (Fin m → ℝ)) [IsGaussian μ]
    (i j : Fin m) (r : ℝ) (hr : |r| ≤ 1)
    (hi : (∫ x, x i ∂μ) = 0) (hj : (∫ x, x j ∂μ) = 0)
    (hii : covarianceMatrix (fun i x => x i) μ i i = 1)
    (hjj : covarianceMatrix (fun i x => x i) μ j j = 1)
    (hij : covarianceMatrix (fun i x => x i) μ i j = r) :
    μ.map (selectCoordinates ![i, j]) = pairNormal r := by
  apply gaussian_eq_of_moments
  · intro k
    rw [selected_mean, pairNormal_mean]
    fin_cases k
    · exact hi
    · exact hj
  · rw [pairNormal_covariance r hr]
    ext a b
    rw [selected_covariance]
    have hji : covarianceMatrix (fun i x => x i) μ j i = r :=
      (covariance_comm _ _).trans hij
    fin_cases a <;> fin_cases b <;> simp [hii, hjj, hij, hji]

/-- The selected pair marginal supplies second moments of its two coordinates on the original
probability space, without assuming that the original joint law is Gaussian. -/
theorem pair_marginal_memLp {m : ℕ} (μ : Measure (Fin m → ℝ)) (i j : Fin m) (r : ℝ)
    (h : μ.map (selectCoordinates ![i, j]) = pairNormal r) :
    MemLp (fun x => x i) 2 μ ∧ MemLp (fun x => x j) 2 μ := by
  have hLp (k : Fin 2) : MemLp (fun x => x (![i, j] k)) 2 μ := by
    have hmap : MemLp (ContinuousLinearMap.proj k : (Fin 2 → ℝ) →L[ℝ] ℝ) 2
        (μ.map (selectCoordinates ![i, j])) := by
      rw [h]
      exact IsGaussian.memLp_dual _ _ 2 (by simp)
    exact hmap.comp_of_map (by fun_prop)
  exact ⟨hLp 0, hLp 1⟩

/-- The selected pair marginal supplies exact covariance entries on the original space. -/
theorem pair_marginal_covariance {m : ℕ} (μ : Measure (Fin m → ℝ)) (i j : Fin m) (r : ℝ)
    (hr : |r| ≤ 1) (h : μ.map (selectCoordinates ![i, j]) = pairNormal r) :
    covarianceMatrix (fun i x => x i) μ i i = 1 ∧
      covarianceMatrix (fun i x => x i) μ j j = 1 ∧
      covarianceMatrix (fun i x => x i) μ i j = r := by
  have hc (a b : Fin 2) : covarianceMatrix (fun i x => x i) μ (![i, j] a) (![i, j] b) =
      (!![1, r; r, 1] : Matrix (Fin 2) (Fin 2) ℝ) a b := by
    rw [← selected_covariance μ ![i, j] a b, h, pairNormal_covariance r hr]
  exact ⟨hc 0 0, hc 1 1, hc 0 1⟩

/-- The four prescribed Gaussian pair marginals admit a common probability measure exactly
when the rate table has vectors. The common measure is not assumed Gaussian in the definition. -/
def HasPairMarginals (d : FourTestTables.Table) : Prop :=
  ∃ μ : Measure (Fin 4 → ℝ), IsProbabilityMeasure μ ∧
    ∀ x y : Bool, μ.map (selectCoordinates ![if x then 1 else 0, if y then 3 else 2]) =
      pairNormal (FourTestTables.corr d x y)

/-- Proposition 11.6(ii), with its actual prescribed pair probability laws in both directions.
The central-limit convergence in part (i) is not a premise and is not claimed here. -/
theorem hasVectors_iff_pairMarginals (d : FourTestTables.Table)
    (hd : ∀ x y, 0 ≤ d x y ∧ d x y ≤ 1) :
    FourTestTables.HasVectors d ↔ HasPairMarginals d := by
  have hr : ∀ x y, |FourTestTables.corr d x y| ≤ 1 := by
    intro x y
    obtain ⟨hlo, hhi⟩ := hd x y
    unfold FourTestTables.corr
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  constructor
  · intro hv
    obtain ⟨μ, hμ, hm, hdiag, h02, h03, h12, h13⟩ := (hasVectors_iff_gaussianTotals d).mp hv
    letI : IsGaussian μ := hμ
    refine ⟨μ, inferInstance, ?_⟩
    intro x y
    apply gaussian_pair_marginal μ _ _ _ (hr x y) (hm _) (hm _) (hdiag _) (hdiag _)
    cases x <;> cases y <;> simp only [Bool.false_eq_true, if_false, if_true]
    · exact h02
    · exact h03
    · exact h12
    · exact h13
  · rintro ⟨μ, hμ, hp⟩
    letI : IsProbabilityMeasure μ := hμ
    have m00 := pair_marginal_covariance μ 0 2 _ (hr false false) (hp false false)
    have m01 := pair_marginal_covariance μ 0 3 _ (hr false true) (hp false true)
    have m10 := pair_marginal_covariance μ 1 2 _ (hr true false) (hp true false)
    have m11 := pair_marginal_covariance μ 1 3 _ (hr true true) (hp true true)
    have l00 := pair_marginal_memLp μ 0 2 _ (hp false false)
    have l01 := pair_marginal_memLp μ 0 3 _ (hp false true)
    have l10 := pair_marginal_memLp μ 1 2 _ (hp true false)
    apply common_moments_imply_vectors d μ
    · intro i
      fin_cases i
      · exact l00.1
      · exact l10.1
      · exact l00.2
      · exact l01.2
    · intro i
      fin_cases i
      · exact m00.1
      · exact m10.1
      · exact m00.2.1
      · exact m01.2.1
    · exact m00.2.2
    · exact m01.2.2
    · exact m10.2.2
    · exact m11.2.2

end

end OperatorKO7.Meta.BoundaryObserver.GaussianTotals
