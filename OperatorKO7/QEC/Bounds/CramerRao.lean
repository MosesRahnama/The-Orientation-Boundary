import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic

noncomputable section

open MeasureTheory Set
open scoped BigOperators ProbabilityTheory

namespace OperatorKO7.QEC.Bounds.CramerRao

/-- Manuscript label `lem:maxent`: differential entropy of a real-valued density. -/
def differentialEntropy (p : ℝ → ℝ) : ℝ :=
  -∫ x, p x * Real.log (p x)

/-- Manuscript label `thm:cramer-rao`: weighted expectation on a finite sample space. -/
def weightedExpectation {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ ω, w ω * f ω

/-- Manuscript label `thm:cramer-rao`: weighted variance about a target parameter `θ` on a
finite sample space. -/
def weightedVariance {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (estimator : Ω → ℝ)
    (θ : ℝ) : ℝ :=
  weightedExpectation w (fun ω => (estimator ω - θ) ^ 2)

/-- Manuscript label `thm:cramer-rao`: per-sample Fisher information for the binary
distinction model with probabilities `1 / 2 ± ε`. -/
def binaryFisherInformation (ε : ℝ) : ℝ :=
  (1 / (1 / 2 + ε)) + (1 / (1 / 2 - ε))

/-- Manuscript label `thm:cramer-rao`: ideal real-valued sample count corresponding to the
paper's epsilon-N gate before applying the natural-number ceiling. -/
def epsilonGateSampleCount (ε : ℝ) : ℝ :=
  Real.log 2 / (2 * ε ^ 2)

/-- Manuscript label `lem:maxent`: Gaussian witness density with mean `μ` and variance `σ²`. -/
def gaussianWitnessDensity (μ σ : ℝ) : ℝ → ℝ :=
  ProbabilityTheory.gaussianPDFReal μ ⟨σ ^ 2, sq_nonneg σ⟩


/-- Manuscript label `lem:maxent`: logarithm of the Gaussian witness density. This is the
log-affine identity used to convert the cross-entropy term against the Gaussian into fixed
normalization and variance moments. -/
theorem gaussianWitnessDensity_log {mean σ x : ℝ} (hσ : 0 < σ) :
    Real.log (gaussianWitnessDensity mean σ x) =
      -Real.log (Real.sqrt (2 * Real.pi * σ ^ 2)) - (x - mean) ^ 2 / (2 * σ ^ 2) := by
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hσ_sq_pos : 0 < σ ^ 2 := sq_pos_of_ne_zero hσ_ne
  have hden_pos : 0 < 2 * Real.pi * σ ^ 2 := by
    nlinarith [Real.pi_pos, hσ_sq_pos]
  have hsqrt_ne : Real.sqrt (2 * Real.pi * σ ^ 2) ≠ 0 := (Real.sqrt_pos.2 hden_pos).ne'
  have hexp_ne : Real.exp (-(x - mean) ^ 2 / (2 * σ ^ 2)) ≠ 0 := Real.exp_ne_zero _
  rw [gaussianWitnessDensity, ProbabilityTheory.gaussianPDFReal]
  simp only [NNReal.coe_mk]
  rw [Real.log_mul (inv_ne_zero hsqrt_ne) hexp_ne]
  rw [Real.log_inv, Real.log_exp]
  ring_nf

/-- Manuscript label `lem:maxent`: cross-entropy of any competitor against the Gaussian witness
is fixed by normalization and the centered second moment. This is the moment side of the
Jaynes/KL maximum-entropy calculation. -/
theorem gaussian_cross_entropy_eq_of_moments {p : ℝ → ℝ} {mean σ : ℝ} (hσ : 0 < σ)
    (hp_norm : ∫ x, p x = 1)
    (hp_second : ∫ x, p x * (x - mean) ^ 2 = σ ^ 2)
    (hp_int : Integrable p)
    (hp_second_int : Integrable fun x => p x * (x - mean) ^ 2) :
    ∫ x, p x * Real.log (gaussianWitnessDensity mean σ x) =
      -Real.log (Real.sqrt (2 * Real.pi * σ ^ 2)) - 1 / 2 := by
  have hσ_sq_ne : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ.ne'
  have hfun : (fun x => p x * Real.log (gaussianWitnessDensity mean σ x)) =
      fun x => (-Real.log (Real.sqrt (2 * Real.pi * σ ^ 2))) * p x -
        (2 * σ ^ 2)⁻¹ * (p x * (x - mean) ^ 2) := by
    funext x
    rw [gaussianWitnessDensity_log hσ]
    ring_nf
  rw [hfun]
  rw [integral_sub]
  · rw [integral_const_mul, integral_const_mul, hp_norm, hp_second]
    field_simp [hσ_sq_ne]
    ring
  · exact hp_int.const_mul _
  · exact hp_second_int.const_mul _
/-- Manuscript label `lem:maxent`: Gaussian moment witness used by the Jaynes maximum-entropy
argument. This theorem proves normalization and the first two Gaussian moments only; it does
NOT assert the constrained-entropy maximization. The top-level entropy-maximization theorem is
`OperatorKO7.QEC.Bounds.CramerRao.maxent` (defined below), which uses this lemma plus the
density-level Gibbs argument.

Relation: density-level moment identities for the Gaussian witness.
Property: definition / metadata-style fact (not a maximum-entropy claim). -/
theorem maxent_moments {μ σ : ℝ} (hσ : 0 < σ) :
    (∫ x, gaussianWitnessDensity μ σ x = 1) ∧
      (∫ x, x ∂ProbabilityTheory.gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩ = μ) ∧
      Var[id; ProbabilityTheory.gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩] = σ ^ 2 := by
  let sigmaSqNN : NNReal := ⟨σ ^ 2, sq_nonneg σ⟩
  have hσ_sq_ne : σ ^ 2 ≠ 0 := by
    intro hsq
    nlinarith [hσ, hsq]
  have hv : sigmaSqNN ≠ 0 := by
    intro hv0
    have h0 : (sigmaSqNN : ℝ) = 0 := congrArg (fun t : NNReal => (t : ℝ)) hv0
    exact hσ_sq_ne (by simpa [sigmaSqNN] using h0)
  refine ⟨?_, ?_, ?_⟩
  · simpa [gaussianWitnessDensity, sigmaSqNN] using
      ProbabilityTheory.integral_gaussianPDFReal_eq_one μ hv
  · simp
  · simp

/-- Manuscript label `lem:maxent`: the Gaussian witness density is strictly positive everywhere
when `σ > 0`.

Relation: density-level positivity of the Gaussian witness.
Property: pointwise positivity (definition-level fact). -/
theorem gaussianWitnessDensity_pos {μ σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    0 < gaussianWitnessDensity μ σ x := by
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hσ_sq_ne : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ_ne
  have hv_ne : (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal) ≠ 0 := by
    intro h0
    apply hσ_sq_ne
    have := congrArg (fun t : NNReal => (t : ℝ)) h0
    simpa using this
  exact ProbabilityTheory.gaussianPDFReal_pos μ ⟨σ ^ 2, sq_nonneg σ⟩ x hv_ne

/-- Manuscript label `lem:maxent`: the Gaussian witness density has the centered second moment
`σ²`. This is the density-level analogue of
`ProbabilityTheory.variance_id_gaussianReal`, obtained by integrating against the explicit
Gaussian density via `ProbabilityTheory.integral_gaussianReal_eq_integral_smul`.

Relation: density-level second-moment identity for the Gaussian witness.
Property: closed-form moment integral (object-level mathematical theorem). -/
theorem gaussianWitnessDensity_centered_second_moment {μ σ : ℝ} (hσ : 0 < σ) :
    ∫ x, gaussianWitnessDensity μ σ x * (x - μ) ^ 2 = σ ^ 2 := by
  set sigmaSqNN : NNReal := ⟨σ ^ 2, sq_nonneg σ⟩ with hsigmaSqNN
  have hσ_sq_ne : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ.ne'
  have hv : sigmaSqNN ≠ 0 := by
    intro hv0
    have h0 : (sigmaSqNN : ℝ) = 0 := congrArg (fun t : NNReal => (t : ℝ)) hv0
    exact hσ_sq_ne (by simpa [sigmaSqNN] using h0)
  -- Mathlib gives Var[id; gaussianReal μ v] = v, and via variance_eq_integral plus
  -- integral_id_gaussianReal this unfolds to ∫ x, (x - μ)^2 ∂(gaussianReal μ v) = v.
  have hvar_id :
      Var[id; ProbabilityTheory.gaussianReal μ sigmaSqNN] = (sigmaSqNN : ℝ) :=
    ProbabilityTheory.variance_id_gaussianReal (μ := μ) (v := sigmaSqNN)
  have hvar_integral :
      ∫ x, (x - μ) ^ 2 ∂(ProbabilityTheory.gaussianReal μ sigmaSqNN) = σ ^ 2 := by
    have hve := ProbabilityTheory.variance_eq_integral
      (μ := ProbabilityTheory.gaussianReal μ sigmaSqNN)
      (X := id) measurable_id'.aemeasurable
    -- hve : Var[id; gaussianReal μ sigmaSqNN] =
    --         ∫ ω, (id ω - (gaussianReal μ sigmaSqNN)[id])^2 ∂(gaussianReal μ sigmaSqNN)
    -- Fold `id ω` to `ω` and `∫ x, id x ∂...` to `∫ x, x ∂...`.
    simp only [id_eq] at hve
    rw [ProbabilityTheory.integral_id_gaussianReal] at hve
    -- hve : Var[id; ...] = ∫ ω, (ω - μ)^2 ∂...
    have hcoe : ((sigmaSqNN : ℝ)) = σ ^ 2 := by simp [sigmaSqNN]
    rw [hvar_id, hcoe] at hve
    -- hve : σ^2 = ∫ ω, (ω - μ)^2 ∂...
    linarith [hve]
  -- Density bridge: ∫ x, f x ∂(gaussianReal μ v) = ∫ x, gaussianPDFReal μ v x • f x.
  have hbridge :=
    (ProbabilityTheory.integral_gaussianReal_eq_integral_smul
      (μ := μ) (v := sigmaSqNN) (f := fun x : ℝ => (x - μ) ^ 2) hv)
  have hsmul :
      (fun x : ℝ => ProbabilityTheory.gaussianPDFReal μ sigmaSqNN x • (x - μ) ^ 2) =
        fun x : ℝ => gaussianWitnessDensity μ σ x * (x - μ) ^ 2 := by
    funext x
    simp [gaussianWitnessDensity, sigmaSqNN, smul_eq_mul]
  rw [hsmul] at hbridge
  linarith [hbridge, hvar_integral]

/-- Manuscript label `lem:maxent`: the top-level Jaynes maximum-entropy theorem at the density
level. Among all probability densities on `ℝ` strictly positive everywhere, normalised, with
mean `μ` and centered variance `σ²`, and admitting the standard integrability conditions,
the Gaussian witness density has at least as large differential entropy.

The proof is the standard density-level Gibbs argument:

```
H(p) ≤ -∫ p · log g           (Gibbs at density level, from
                                Real.log_le_sub_one_of_pos applied to g/p)
H(g) = -∫ g · log g
∫ p · log g  =  ∫ g · log g    (gaussian_cross_entropy_eq_of_moments
                                yields the same cross-entropy value for both,
                                under matching moments)
⇒ H(p) ≤ H(g).
```

The hypothesis `hp_pos` is the standard strict-positivity assumption used in the density-level
Jaynes argument; it lets us apply `Real.log_le_sub_one_of_pos` pointwise to `g x / p x`.
The hypotheses `hg_second_int`, `hp_plogp_int`, and `hp_plogg_int` are the standard
integrability conditions implicit in the manuscript's "fix mean and variance" phrasing.
`hg_second_int` is the L² regularity of the Gaussian witness; the value of the integral itself
is already discharged by `gaussianWitnessDensity_centered_second_moment`. The integrability
of `g · (x - μ)²` follows from `MeasureTheory.MemLp.integrable` plus the
`ProbabilityTheory.integral_gaussianReal_eq_integral_smul` density bridge — exposed here as a
hypothesis to keep this theorem independent of further Gaussian moment infrastructure.

Relation: density-level entropy inequality.
Property: differential-entropy upper bound (object-level mathematical theorem). -/
theorem maxent {μ σ : ℝ} (hσ : 0 < σ) {p : ℝ → ℝ}
    (hp_pos : ∀ x, 0 < p x)
    (hp_norm : ∫ x, p x = 1)
    (hp_second : ∫ x, p x * (x - μ) ^ 2 = σ ^ 2)
    (hp_int : Integrable p)
    (hp_second_int : Integrable fun x => p x * (x - μ) ^ 2)
    (hp_plogp_int : Integrable fun x => p x * Real.log (p x))
    (hp_plogg_int : Integrable fun x => p x * Real.log (gaussianWitnessDensity μ σ x))
    (hg_second_int :
      Integrable fun x => gaussianWitnessDensity μ σ x * (x - μ) ^ 2) :
    differentialEntropy p ≤ differentialEntropy (gaussianWitnessDensity μ σ) := by
  set g : ℝ → ℝ := gaussianWitnessDensity μ σ with hg_def
  have hg_norm : ∫ x, g x = 1 := by
    simpa [g, gaussianWitnessDensity] using (maxent_moments hσ).1
  have hg_second : ∫ x, g x * (x - μ) ^ 2 = σ ^ 2 :=
    gaussianWitnessDensity_centered_second_moment hσ
  have hg_int : Integrable g := by
    show Integrable (gaussianWitnessDensity μ σ)
    simpa [gaussianWitnessDensity] using
      (ProbabilityTheory.integrable_gaussianPDFReal μ ⟨σ ^ 2, sq_nonneg σ⟩)
  have hg_pos : ∀ x, 0 < g x := fun x => gaussianWitnessDensity_pos hσ x
  -- Cross-entropy identity for p against g (from the existing cross-entropy lemma).
  have hcross_p :
      ∫ x, p x * Real.log (g x) =
        -Real.log (Real.sqrt (2 * Real.pi * σ ^ 2)) - 1 / 2 :=
    gaussian_cross_entropy_eq_of_moments hσ hp_norm hp_second hp_int hp_second_int
  -- Cross-entropy identity for g against itself.
  have hcross_g :
      ∫ x, g x * Real.log (g x) =
        -Real.log (Real.sqrt (2 * Real.pi * σ ^ 2)) - 1 / 2 :=
    gaussian_cross_entropy_eq_of_moments hσ hg_norm hg_second hg_int hg_second_int
  -- Density-level Gibbs: pointwise log(g/p) ≤ g/p - 1 ⇒ p log g - p log p ≤ g - p.
  have h_pointwise :
      ∀ x, p x * Real.log (g x) - p x * Real.log (p x) ≤ g x - p x := by
    intro x
    have hp : 0 < p x := hp_pos x
    have hgp_pos : 0 < g x / p x := div_pos (hg_pos x) hp
    have hlog := Real.log_le_sub_one_of_pos hgp_pos
    rw [Real.log_div (hg_pos x).ne' hp.ne'] at hlog
    have hmul : p x * (Real.log (g x) - Real.log (p x)) ≤ p x * (g x / p x - 1) :=
      mul_le_mul_of_nonneg_left hlog hp.le
    have hrhs : p x * (g x / p x - 1) = g x - p x := by
      field_simp
    linarith [hmul, hrhs.le, hrhs.ge]
  -- Integrate.
  have h_int_lhs :
      Integrable fun x => p x * Real.log (g x) - p x * Real.log (p x) :=
    hp_plogg_int.sub hp_plogp_int
  have h_int_rhs : Integrable fun x => g x - p x := hg_int.sub hp_int
  have h_integrated :
      ∫ x, p x * Real.log (g x) - p x * Real.log (p x) ≤ ∫ x, g x - p x :=
    integral_mono_ae h_int_lhs h_int_rhs (ae_of_all _ h_pointwise)
  have h_lhs_eq :
      ∫ x, p x * Real.log (g x) - p x * Real.log (p x) =
        (∫ x, p x * Real.log (g x)) - ∫ x, p x * Real.log (p x) :=
    integral_sub hp_plogg_int hp_plogp_int
  have h_rhs_eq : ∫ x, g x - p x = (∫ x, g x) - ∫ x, p x :=
    integral_sub hg_int hp_int
  rw [h_lhs_eq, h_rhs_eq, hg_norm, hp_norm] at h_integrated
  -- After rewrite: ∫ p log g - ∫ p log p ≤ 1 - 1 = 0.
  have h_cross_eq : ∫ x, p x * Real.log (g x) = ∫ x, g x * Real.log (g x) := by
    rw [hcross_p, hcross_g]
  unfold differentialEntropy
  show -∫ x, p x * Real.log (p x) ≤ -∫ x, g x * Real.log (g x)
  rw [← h_cross_eq]
  linarith
theorem gibbs_integral_nonneg_of_equal_mass {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (hmass : μ univ = ν univ) :
    0 ≤ ∫ x, llr μ ν x ∂μ := by
  have h := InformationTheory.integral_llr_add_sub_measure_univ_nonneg
    (μ := μ) (ν := ν) hμν h_int
  simpa [hmass, measureReal_def] using h

/-- Manuscript label `lem:maxent`: universal KL-gap maximum-entropy theorem. If the entropy gap
between a candidate Gaussian entropy and any competitor entropy is the KL divergence from the
competitor measure to the Gaussian witness measure, then the competitor entropy is bounded above
by the Gaussian entropy. -/
theorem maxent_entropy_le_of_kl_gap {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {competitorEntropy gaussianEntropy : ℝ}
    (entropyGap_eq_kl : gaussianEntropy - competitorEntropy =
      (InformationTheory.klDiv μ ν).toReal) :
    competitorEntropy ≤ gaussianEntropy := by
  have hkl_nonneg : 0 ≤ (InformationTheory.klDiv μ ν).toReal := ENNReal.toReal_nonneg
  linarith

/-- Manuscript label `lem:maxent`: equality case for the universal KL-gap maximum-entropy theorem.
If the KL gap is finite and the competitor reaches the Gaussian entropy, the competitor and
Gaussian witness measures are equal. This is the measure-level uniqueness statement; density-level
pointwise uniqueness requires an additional Radon-Nikodym representative theorem. -/
theorem maxent_unique_measure_of_kl_gap {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {competitorEntropy gaussianEntropy : ℝ}
    (entropyGap_eq_kl : gaussianEntropy - competitorEntropy =
      (InformationTheory.klDiv μ ν).toReal)
    (hkl_finite : InformationTheory.klDiv μ ν ≠ ⊤)
    (entropy_eq : competitorEntropy = gaussianEntropy) :
    μ = ν := by
  have hto : (InformationTheory.klDiv μ ν).toReal = 0 := by
    nlinarith [entropyGap_eq_kl, entropy_eq]
  rcases (ENNReal.toReal_eq_zero_iff (InformationTheory.klDiv μ ν)).mp hto with hzero | htop
  · exact (InformationTheory.klDiv_eq_zero_iff (μ := μ) (ν := ν)).mp hzero
  · exact False.elim (hkl_finite htop)

/-- Manuscript label `lem:maxent`: Gaussian-facing entropy bound from a KL-gap certificate. This
is the direct paper-facing maximum-entropy inequality once the density calculation identifies the
entropy gap with KL divergence. -/
theorem gaussian_maxent_entropy_le_of_kl_gap {p : ℝ → ℝ} {mean σ : ℝ}
    {competitorMeasure gaussianMeasure : Measure ℝ}
    (entropyGap_eq_kl :
      differentialEntropy (gaussianWitnessDensity mean σ) - differentialEntropy p =
        (InformationTheory.klDiv competitorMeasure gaussianMeasure).toReal) :
    differentialEntropy p ≤ differentialEntropy (gaussianWitnessDensity mean σ) :=
  maxent_entropy_le_of_kl_gap entropyGap_eq_kl

/-- Manuscript label `lem:maxent`: Gaussian-facing uniqueness from a KL-gap certificate. Equality
at the maximum-entropy bound forces equality of the competitor and Gaussian witness measures,
provided the KL divergence is finite. -/
theorem gaussian_maxent_unique_measure_of_kl_gap {p : ℝ → ℝ} {mean σ : ℝ}
    {competitorMeasure gaussianMeasure : Measure ℝ}
    [IsFiniteMeasure competitorMeasure] [IsFiniteMeasure gaussianMeasure]
    (entropyGap_eq_kl :
      differentialEntropy (gaussianWitnessDensity mean σ) - differentialEntropy p =
        (InformationTheory.klDiv competitorMeasure gaussianMeasure).toReal)
    (hkl_finite : InformationTheory.klDiv competitorMeasure gaussianMeasure ≠ ⊤)
    (entropy_eq : differentialEntropy p = differentialEntropy (gaussianWitnessDensity mean σ)) :
    competitorMeasure = gaussianMeasure :=
  maxent_unique_measure_of_kl_gap entropyGap_eq_kl hkl_finite entropy_eq

/-- Manuscript label `lem:maxent`: strongest Lean-facing maximum-entropy theorem in this module.
For any competitor density with the Gaussian normalization and centered second moment, once the
entropy gap is identified with KL divergence to the Gaussian witness measure, the Gaussian entropy
is maximal. Equality forces equality of the competitor and Gaussian witness measures. -/
theorem gaussian_maxent_unique_from_moments_and_kl_gap {p : ℝ → ℝ} {mean σ : ℝ}
    {competitorMeasure gaussianMeasure : Measure ℝ}
    [IsFiniteMeasure competitorMeasure] [IsFiniteMeasure gaussianMeasure]
    (hσ : 0 < σ)
    (hp_norm : ∫ x, p x = 1)
    (hp_second : ∫ x, p x * (x - mean) ^ 2 = σ ^ 2)
    (hp_int : Integrable p)
    (hp_second_int : Integrable fun x => p x * (x - mean) ^ 2)
    (entropyGap_eq_kl :
      differentialEntropy (gaussianWitnessDensity mean σ) - differentialEntropy p =
        (InformationTheory.klDiv competitorMeasure gaussianMeasure).toReal)
    (hkl_finite : InformationTheory.klDiv competitorMeasure gaussianMeasure ≠ ⊤) :
    differentialEntropy p ≤ differentialEntropy (gaussianWitnessDensity mean σ) ∧
      (differentialEntropy p = differentialEntropy (gaussianWitnessDensity mean σ) →
        competitorMeasure = gaussianMeasure) := by
  have _hcross := gaussian_cross_entropy_eq_of_moments hσ hp_norm hp_second hp_int hp_second_int
  exact ⟨gaussian_maxent_entropy_le_of_kl_gap entropyGap_eq_kl,
    fun entropy_eq =>
      gaussian_maxent_unique_measure_of_kl_gap entropyGap_eq_kl hkl_finite entropy_eq⟩
/-- Manuscript label `thm:cramer-rao`: finite Cauchy-Schwarz in the score-function form used
to derive the Cramer-Rao bound. -/
theorem finite_cauchy_schwarz {Ω : Type*} [Fintype Ω] (u v : Ω → ℝ) :
    (∑ ω, u ω * v ω) ^ 2 ≤ (∑ ω, u ω ^ 2) * ∑ ω, v ω ^ 2 := by
  simpa using
    Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := u) (g := v)

/-- Manuscript label `thm:cramer-rao`: the binary distinction model has Fisher information
`FI(ε = 0) = 4`. -/
theorem fisher_info_binary : binaryFisherInformation 0 = 4 := by
  norm_num [binaryFisherInformation]

/-- Manuscript label `thm:cramer-rao`: Cramer-Rao for a finite score model. The hypothesis
`scoreIdentity` is the standard unbiased score-function identity
`E[(Khat - K) score] = 1`, and the conclusion is
`Var(Khat) ≥ 1 / (N * FI)`. -/
theorem cramer_rao_bound {Ω : Type*} [Fintype Ω] {N FI variance : ℝ}
    (hN : 0 < N) (hFI : 0 < FI) (centeredEstimator score : Ω → ℝ)
    (scoreIdentity : ∑ ω, centeredEstimator ω * score ω = 1)
    (variance_eq : variance = ∑ ω, centeredEstimator ω ^ 2)
    (fisher_eq : N * FI = ∑ ω, score ω ^ 2) :
    1 / (N * FI) ≤ variance := by
  have hcs := finite_cauchy_schwarz centeredEstimator score
  have hmain : 1 ≤ variance * (N * FI) := by
    calc
      1 = (∑ ω, centeredEstimator ω * score ω) ^ 2 := by
        rw [scoreIdentity]
        norm_num
      _ ≤ (∑ ω, centeredEstimator ω ^ 2) * ∑ ω, score ω ^ 2 := hcs
      _ = variance * (N * FI) := by
        rw [← variance_eq, ← fisher_eq]
  have hden_pos : 0 < N * FI := mul_pos hN hFI
  apply (mul_le_mul_right hden_pos).mp
  calc
    (1 / (N * FI)) * (N * FI) = 1 := by
      field_simp [hden_pos.ne']
    _ ≤ variance * (N * FI) := hmain
/-- Manuscript label `thm:cramer-rao`: binary specialization of the finite Cramer-Rao
score theorem. Since `FI(0) = 4`, any finite score model satisfying the score, variance, and
Fisher identities has variance at least `1 / (4 * N)`. -/
theorem binary_cramer_rao_floor {Ω : Type*} [Fintype Ω] {N variance : ℝ}
    (hN : 0 < N) (centeredEstimator score : Ω → ℝ)
    (scoreIdentity : ∑ ω, centeredEstimator ω * score ω = 1)
    (variance_eq : variance = ∑ ω, centeredEstimator ω ^ 2)
    (fisher_eq : N * binaryFisherInformation 0 = ∑ ω, score ω ^ 2) :
    1 / (4 * N) ≤ variance := by
  have hFI : 0 < binaryFisherInformation 0 := by
    rw [fisher_info_binary]
    norm_num
  have hcr := cramer_rao_bound (N := N) (FI := binaryFisherInformation 0)
    (variance := variance) hN hFI centeredEstimator score scoreIdentity variance_eq fisher_eq
  simpa [fisher_info_binary, mul_comm] using hcr

/-- Manuscript label `thm:cramer-rao`: under the ideal real-valued epsilon-N gate, substituting `FI(0) = 4` rewrites the Cramer-Rao floor to `ε² / (2 log 2)`. This is the equality case before the manuscript's natural-number ceiling; the ceiling inequality has the opposite monotonicity for lower bounds of the form `1 / (4 * N)`. -/
theorem gating_eq {ε N : ℝ} (_hε : ε ≠ 0) (hN : N = epsilonGateSampleCount ε) :
    1 / (N * binaryFisherInformation 0) = ε ^ 2 / (2 * Real.log 2) := by
  subst N
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [fisher_info_binary]
  field_simp [epsilonGateSampleCount, hlog]
  ring
/-- Manuscript label `thm:cramer-rao`: corrected ceiling-gate consequence. If the sample count
is at or above the real-valued epsilon gate, the Cramer-Rao floor `1 / (4N)` is no larger than
the saturation value `ε² / (2 log 2)`. This is the monotonic statement compatible with a lower
bound that decreases as `N` increases. -/
theorem gating_ceiling_monotone {ε N : ℝ} (hε : ε ≠ 0)
    (hN : epsilonGateSampleCount ε ≤ N) :
    1 / (N * binaryFisherInformation 0) ≤ ε ^ 2 / (2 * Real.log 2) := by
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hgate_pos : 0 < epsilonGateSampleCount ε := by
    rw [epsilonGateSampleCount]
    positivity
  have hN_pos : 0 < N := lt_of_lt_of_le hgate_pos hN
  have hbound : Real.log 2 ≤ 2 * N * ε ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hN (by positivity : 0 ≤ 2 * ε ^ 2)
    have hleft : epsilonGateSampleCount ε * (2 * ε ^ 2) = Real.log 2 := by
      rw [epsilonGateSampleCount]
      field_simp [hε]
    nlinarith [hmul, hleft]
  rw [fisher_info_binary]
  have hden_left : 0 < N * 4 := by positivity
  have hden_right : 0 < 2 * Real.log 2 := by positivity
  rw [div_le_div_iff₀ hden_left hden_right]
  nlinarith [hbound]

/-- Manuscript label `thm:cramer-rao`: concrete binary-Bernoulli non-vacuity witness for
`cramer_rao_bound`. Constructs explicit functions `centeredEstimator, score : Fin 2 → ℝ`
realising the three identities of the Cramér-Rao Cauchy-Schwarz form, with the binary Fisher
information `FI(ε = 0) = 4` and the standard `1/(4N)` variance floor for `N` i.i.d. binary
distinction commits.

This discharges audit gate R5 (non-vacuity) for `cramer_rao_bound` and theorem-level S09 (missing
witness). The witness uses the symmetric Bernoulli score-variance pair on
`Ω = Fin 2`:
- `centeredEstimator = ![1 / (2 √N), 0]`
- `score = ![2 √N, 0]`
so `∑ e · s = 1`, `∑ e² = 1/(4N)`, and `∑ s² = 4N = N · FI(0)`.

Relation: finite Cramér-Rao Cauchy-Schwarz instance.
Property: witness / non-vacuity (object-level instance for the conditional `cramer_rao_bound`). -/
theorem cramer_rao_bound_binary {N : ℕ} (hN : 0 < N) :
    ∃ centeredEstimator score : Fin 2 → ℝ,
      (∑ ω, centeredEstimator ω * score ω = 1) ∧
      (1 / (4 * (N : ℝ)) ≤ ∑ ω, centeredEstimator ω ^ 2) ∧
      ((N : ℝ) * binaryFisherInformation 0 = ∑ ω, score ω ^ 2) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN_ne : (N : ℝ) ≠ 0 := hN_pos.ne'
  have hsqrtN_pos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
  have hsqrtN_ne : Real.sqrt N ≠ 0 := hsqrtN_pos.ne'
  have hsq_sqrt : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hN_pos.le
  refine ⟨![1 / (2 * Real.sqrt N), 0], ![2 * Real.sqrt N, 0], ?_, ?_, ?_⟩
  · -- ∑ ω, e(ω) * s(ω) = (1 / (2 √N)) * (2 √N) + 0 * 0 = 1.
    have : (∑ ω : Fin 2,
        (![1 / (2 * Real.sqrt (N : ℝ)), 0] : Fin 2 → ℝ) ω *
          (![2 * Real.sqrt (N : ℝ), 0] : Fin 2 → ℝ) ω) =
        1 / (2 * Real.sqrt (N : ℝ)) * (2 * Real.sqrt (N : ℝ)) := by
      simp [Fin.sum_univ_two]
    rw [this]
    field_simp
  · -- 1 / (4 N) ≤ (1 / (2 √N))² + 0² = 1 / (4 N), so equality holds.
    have hsum :
        ∑ ω : Fin 2, (![1 / (2 * Real.sqrt (N : ℝ)), 0] : Fin 2 → ℝ) ω ^ 2 =
          (1 / (2 * Real.sqrt (N : ℝ))) ^ 2 := by
      simp [Fin.sum_univ_two]
    rw [hsum]
    have hsq :
        (1 / (2 * Real.sqrt (N : ℝ))) ^ 2 = 1 / (4 * (N : ℝ)) := by
      rw [div_pow, one_pow, mul_pow, hsq_sqrt]
      norm_num
    rw [hsq]
  · -- N · FI(0) = N · 4 = 4N = (2 √N)² + 0² = ∑ s².
    rw [fisher_info_binary]
    have hsum :
        ∑ ω : Fin 2, (![2 * Real.sqrt (N : ℝ), 0] : Fin 2 → ℝ) ω ^ 2 =
          (2 * Real.sqrt (N : ℝ)) ^ 2 := by
      simp [Fin.sum_univ_two]
    rw [hsum]
    have hsq2 : (2 * Real.sqrt (N : ℝ)) ^ 2 = 4 * (N : ℝ) := by
      rw [mul_pow, hsq_sqrt]
      norm_num
    rw [hsq2]
    ring

/-- Manuscript label `thm:cramer-rao`: the ε-N gating bound `σ_K² ≥ ε² / (2 ln 2)` from the
manuscript (line ~610, natural-units form). This is the SATURATION case of the Cramér-Rao
floor: at the exact gate value `N = ln 2 / (2 ε²)`, the `1 / (4N)` Cramér-Rao floor evaluates
to `ε² / (2 ln 2)`. Above the gate (`N > ln 2 / (2 ε²)`) the manuscript's "≥" direction is
NOT preserved — `gating_ceiling_monotone` shows that the floor `1/(4N)` is strictly less than
`ε² / (2 ln 2)` in that regime. The manuscript should be read as the saturation-case
statement; this theorem packages exactly that reading.

This resolves Issue 3 of the Sprint 1-bis audit: the manuscript inequality direction is
consistent with the Lean theorems WHEN N is the exact gate value. See
`lean_sprint/sprint_1bis/manuscript_alignment_note.md` for the recommended one-line
manuscript clarification.

Relation: finite Cramér-Rao + ε-N gating saturation.
Property: variance lower bound at the gating saturation point (object-level mathematical theorem). -/
theorem gating_saturation_bound
    {ε : ℝ} (hε : ε ≠ 0) {variance : ℝ}
    (centeredEstimator score : Fin 2 → ℝ)
    (scoreIdentity : ∑ ω, centeredEstimator ω * score ω = 1)
    (variance_eq : variance = ∑ ω, centeredEstimator ω ^ 2)
    (fisher_eq :
      epsilonGateSampleCount ε * binaryFisherInformation 0 = ∑ ω, score ω ^ 2) :
    ε ^ 2 / (2 * Real.log 2) ≤ variance := by
  have hN_pos : 0 < epsilonGateSampleCount ε := by
    rw [epsilonGateSampleCount]; positivity
  have hFI_pos : 0 < binaryFisherInformation 0 := by
    rw [fisher_info_binary]; norm_num
  have hcr :
      1 / (epsilonGateSampleCount ε * binaryFisherInformation 0) ≤ variance :=
    cramer_rao_bound hN_pos hFI_pos centeredEstimator score scoreIdentity variance_eq fisher_eq
  have hg :
      1 / (epsilonGateSampleCount ε * binaryFisherInformation 0) =
        ε ^ 2 / (2 * Real.log 2) :=
    gating_eq hε rfl
  linarith [hcr, hg.le, hg.ge]

end OperatorKO7.QEC.Bounds.CramerRao
