import OperatorKO7.Meta.BoundaryGeneral.CountableRoleExchange
import OperatorKO7.Meta.Recursor.HiddenDepthAmplitude
import OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden

set_option autoImplicit false

/-!
# Maximum entropy at a hidden-depth burden constraint

Graph: `Audit/ledgers/operational-inexpressibility/TWO-VOIDS-PROOF-GRAPH.md`, M17.
Uses the existing Gibbs inequality, recursor burden count and normalized phase lift. The
Gibbs law is derived as the unique optimizer on a finite index type, including competitors
with zero masses. Applying it to the exact triangular burden gives a quadratic log-density
on nonnegative integers. This is not a normal law on the whole real line.
Relation: finite probability laws, expected structural cost, and coherent phase representations.
Trust: kernel-only. A thermodynamic identification of the cost requires separate physical data.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BurdenGibbs

open OperatorKO7.Meta.BoundaryGeneral.CountableRoleExchange
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden
open OperatorKO7.Meta.Recursor.HiddenDepthAmplitude

noncomputable section

/-- Partition function of an arbitrary finite cost profile. -/
def partition {K : Type} [Fintype K] (cost : K → ℝ) (β : ℝ) : ℝ :=
  ∑ k, Real.exp (-β * cost k)

/-- A nonempty finite cost profile has a positive partition function. -/
theorem partition_pos {K : Type} [Fintype K] [Nonempty K] (cost : K → ℝ) (β : ℝ) :
    0 < partition cost β :=
  Finset.sum_pos (fun _k _ => Real.exp_pos _) Finset.univ_nonempty

/-- The candidate hidden-depth law, with normalization and nonnegativity proved. -/
def gibbsLaw {K : Type} [Fintype K] [Nonempty K] (cost : K → ℝ) (β : ℝ) :
    HiddenDepthLaw K where
  p k := Real.exp (-β * cost k) / partition cost β
  nonneg k := (div_pos (Real.exp_pos _) (partition_pos cost β)).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (partition_pos cost β).ne'

/-- Every finite Gibbs mass is positive. -/
theorem gibbs_pos {K : Type} [Fintype K] [Nonempty K] (cost : K → ℝ) (β : ℝ) (k : K) :
    0 < (gibbsLaw cost β).p k := div_pos (Real.exp_pos _) (partition_pos cost β)

/-- The logarithm of the law is affine in the supplied cost. -/
theorem log_gibbs {K : Type} [Fintype K] [Nonempty K] (cost : K → ℝ) (β : ℝ) (k : K) :
    Real.log ((gibbsLaw cost β).p k) = -β * cost k - Real.log (partition cost β) := by
  rw [gibbsLaw, Real.log_div (Real.exp_ne_zero _) (partition_pos cost β).ne', Real.log_exp]

/-- Expected cost in the original structural units. -/
def expectedCost {K : Type} [Fintype K] (cost : K → ℝ) (p : K → ℝ) : ℝ :=
  ∑ k, p k * cost k

/-- Entropy in nats minus a weighted cost. No temperature interpretation is built in. -/
def entropyMinusCost {K : Type} [Fintype K] (cost : K → ℝ) (β : ℝ) (p : K → ℝ) : ℝ :=
  H p - β * expectedCost cost p

/-- The optimization gap is exactly the existing relative entropy, not an assumed gap
certificate. The identity includes zero probabilities. -/
theorem gibbs_gap_identity {K : Type} [Fintype K] [Nonempty K]
    (cost : K → ℝ) (β : ℝ) (p : K → ℝ) (hs : ∑ k, p k = 1) :
    Real.log (partition cost β) - entropyMinusCost cost β p =
      countableRoleDivergence p (gibbsLaw cost β).p := by
  have ht : ∀ k, p k * Real.log (p k / (gibbsLaw cost β).p k) =
      p k * Real.log (p k) + β * (p k * cost k) + p k * Real.log (partition cost β) := by
    intro k
    by_cases hp : p k = 0
    · simp [hp]
    · rw [Real.log_div hp (gibbs_pos cost β k).ne', log_gibbs]
      ring
  rw [countableRoleDivergence_fintype]
  simp_rw [ht]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, hs, one_mul]
  unfold entropyMinusCost expectedCost H
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

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

/-- Gibbs achieves the partition bound exactly. -/
theorem gibbs_objective {K : Type} [Fintype K] [Nonempty K] (cost : K → ℝ) (β : ℝ) :
    entropyMinusCost cost β (gibbsLaw cost β).p = Real.log (partition cost β) := by
  have h := gibbs_gap_identity cost β (gibbsLaw cost β).p (gibbsLaw cost β).sum_one
  rw [countableRoleDivergence_self] at h
  linarith

/-- The Gibbs law uniquely maximizes entropy minus expected cost over every probability law
on the given finite carrier. No positivity requirement is imposed on competing masses. -/
theorem gibbs_unique_maximum {K : Type} [Fintype K] [Nonempty K]
    (cost : K → ℝ) (β : ℝ) (p : HiddenDepthLaw K) :
    entropyMinusCost cost β p.p ≤ entropyMinusCost cost β (gibbsLaw cost β).p ∧
      (entropyMinusCost cost β p.p = entropyMinusCost cost β (gibbsLaw cost β).p ↔
        p.p = (gibbsLaw cost β).p) := by
  have hid := gibbs_gap_identity cost β p.p p.sum_one
  have hn := finite_divergence_nonneg p.p (gibbsLaw cost β).p p.nonneg
    (gibbs_pos cost β) p.sum_one (gibbsLaw cost β).sum_one
  rw [gibbs_objective]
  constructor
  · linarith
  · constructor
    · intro he
      apply (finite_divergence_eq_zero_iff p.p (gibbsLaw cost β).p p.nonneg
        (gibbs_pos cost β) p.sum_one (gibbsLaw cost β).sum_one).mp
      linarith
    · intro he
      rw [he, gibbs_objective]

/-- The same law uniquely maximizes entropy among laws with its expected cost. -/
theorem maxent_at_equal_cost {K : Type} [Fintype K] [Nonempty K]
    (cost : K → ℝ) (β : ℝ) (p : HiddenDepthLaw K)
    (hc : expectedCost cost p.p = expectedCost cost (gibbsLaw cost β).p) :
    H p.p ≤ H (gibbsLaw cost β).p ∧
      (H p.p = H (gibbsLaw cost β).p ↔ p.p = (gibbsLaw cost β).p) := by
  have h := gibbs_unique_maximum cost β p
  unfold entropyMinusCost at h
  rw [hc] at h
  exact ⟨by linarith [h.1], by simpa only [sub_left_inj] using h.2⟩

/-- With nonnegative cost penalty, the maximum-entropy assertion also holds under the cost
budget set by the Gibbs law. -/
theorem maxent_under_cost_budget {K : Type} [Fintype K] [Nonempty K]
    (cost : K → ℝ) (β : ℝ) (hβ : 0 ≤ β) (p : HiddenDepthLaw K)
    (hc : expectedCost cost p.p ≤ expectedCost cost (gibbsLaw cost β).p) :
    H p.p ≤ H (gibbsLaw cost β).p := by
  have h := (gibbs_unique_maximum cost β p).1
  unfold entropyMinusCost at h
  nlinarith [mul_le_mul_of_nonneg_left hc hβ]

/-- The already-proved recursor carrier count is an exact shifted quadratic in depth. -/
theorem carrierRaw_quadratic (L k : ℕ) :
    (carrierRaw L k : ℝ) = (L : ℝ) / 2 * ((k : ℝ) + 3 / 2) ^ 2 - (L : ℝ) / 8 := by
  have h := carrierRaw_two_mul L k
  have hr : (2 : ℝ) * (carrierRaw L k : ℝ) = ((k : ℝ) + 1) * ((k : ℝ) + 2) * L := by
    exact_mod_cast h
  nlinarith

/-- Actual hidden-depth distribution on a finite horizon with one state per depth. -/
def burdenLaw (n L : ℕ) (β : ℝ) : HiddenDepthLaw (Fin (n + 1)) :=
  gibbsLaw (fun k => (carrierRaw L k.val : ℝ)) β

/-- The exact log-density is a discrete, truncated Gaussian-shaped kernel, including its
center shift. No continuous approximation or normal runtime law is assumed. -/
theorem burden_log_density (n L : ℕ) (β : ℝ) (k : Fin (n + 1)) :
    Real.log ((burdenLaw n L β).p k) =
      (β * L / 8 - Real.log (partition (fun j : Fin (n + 1) => (carrierRaw L j.val : ℝ)) β)) -
        β * L / 2 * ((k.val : ℝ) + 3 / 2) ^ 2 := by
  rw [burdenLaw, log_gibbs, carrierRaw_quadratic]
  ring

/-- The natural finite depth law is not an unconstrained normal prior: its probabilities
are fixed by the declared entropy-cost optimization. -/
theorem burden_unique_maximum (n L : ℕ) (β : ℝ) (p : HiddenDepthLaw (Fin (n + 1))) :
    entropyMinusCost (fun k => (carrierRaw L k.val : ℝ)) β p.p ≤
      entropyMinusCost (fun k => (carrierRaw L k.val : ℝ)) β (burdenLaw n L β).p ∧
    (entropyMinusCost (fun k => (carrierRaw L k.val : ℝ)) β p.p =
      entropyMinusCost (fun k => (carrierRaw L k.val : ℝ)) β (burdenLaw n L β).p ↔
      p.p = (burdenLaw n L β).p) := gibbs_unique_maximum _ _ _

/-- The existing characteristic-phase lift supplies normalized amplitudes for the derived
law. Phase remains supplied data; this does not infer coherence from a distribution. -/
theorem burden_phase_weights (n L : ℕ) (β w : ℝ) (k : Fin (n + 1)) :
    ‖charPhaseLift (burdenLaw n L β) (fun j => (j.val : ℤ)) w k‖ ^ 2 =
      (burdenLaw n L β).p k := charPhaseLift_normSq _ _ _ _

/-- Normalization follows from the existing Born-weight identity. -/
theorem burden_phase_normalized (n L : ℕ) (β w : ℝ) :
    (∑ k, ‖charPhaseLift (burdenLaw n L β) (fun j => (j.val : ℤ)) w k‖ ^ 2) = 1 := by
  simp_rw [burden_phase_weights]
  exact (burdenLaw n L β).sum_one

/-- With no cost penalty the finite law is uniform, rather than a Gaussian on the real line. -/
theorem zero_penalty_uniform {K : Type} [Fintype K] [Nonempty K] (cost : K → ℝ) (k : K) :
    (gibbsLaw cost 0).p k = 1 / Fintype.card K := by
  simp [gibbsLaw, partition]

/-- Non-vacuity at zero horizon: the unique count has probability one for every cost scale. -/
theorem zero_horizon (L : ℕ) (β : ℝ) : (burdenLaw 0 L β).p 0 = 1 := by
  have h := (burdenLaw 0 L β).sum_one
  simpa using h

/-- Free-energy form at a positive entropy scale. Interpreting that scale as kB times
bath temperature requires an energy model for the supplied cost. -/
theorem free_energy_minimum {K : Type} [Fintype K] [Nonempty K]
    (cost : K → ℝ) (θ : ℝ) (hθ : 0 < θ) (p : HiddenDepthLaw K) :
    expectedCost cost (gibbsLaw cost (1 / θ)).p - θ * H (gibbsLaw cost (1 / θ)).p ≤
      expectedCost cost p.p - θ * H p.p := by
  have h := (gibbs_unique_maximum cost (1 / θ) p).1
  unfold entropyMinusCost at h
  have hm := mul_le_mul_of_nonneg_left h hθ.le
  have hc : θ * (1 / θ) = 1 := by field_simp
  simp only [mul_sub, ← mul_assoc, hc, one_mul] at hm
  linarith

/-- Increasing the cost penalty decreases expected burden. -/
theorem gibbs_cost_antitone {K : Type} [Fintype K] [Nonempty K]
    (cost : K → ℝ) {β γ : ℝ} (h : β < γ) :
    expectedCost cost (gibbsLaw cost γ).p ≤ expectedCost cost (gibbsLaw cost β).p := by
  have hβ := (gibbs_unique_maximum cost β (gibbsLaw cost γ)).1
  have hγ := (gibbs_unique_maximum cost γ (gibbsLaw cost β)).1
  unfold entropyMinusCost at hβ hγ
  nlinarith

/-- Along nonnegative penalties, entropy decreases with the tolerated expected burden.
The entropy objective is constrained; its maximizer need not be the uniform law. -/
theorem gibbs_entropy_antitone {K : Type} [Fintype K] [Nonempty K]
    (cost : K → ℝ) {β γ : ℝ} (hβ : 0 ≤ β) (h : β < γ) :
    H (gibbsLaw cost γ).p ≤ H (gibbsLaw cost β).p := by
  have ho := (gibbs_unique_maximum cost β (gibbsLaw cost γ)).1
  have hc := gibbs_cost_antitone cost h
  unfold entropyMinusCost at ho
  nlinarith [mul_le_mul_of_nonneg_left hc hβ]

/-- Hidden microstate multiplicity changes the law of an observed depth. Maximizing over
microstates assigns an additional fiber-count factor to the Gibbs weight of each depth. -/
theorem gibbs_depth_multiplicity {X D : Type} [Fintype X] [Nonempty X] [DecidableEq D]
    (depth : X → D) (cost : D → ℝ) (β : ℝ) (d : D) :
    (∑ x, if depth x = d then (gibbsLaw (cost ∘ depth) β).p x else 0) =
      ((Finset.univ.filter (fun x => depth x = d)).card : ℝ) * Real.exp (-β * cost d) /
        partition (cost ∘ depth) β := by
  classical
  have ht : ∀ x, (if depth x = d then (gibbsLaw (cost ∘ depth) β).p x else 0) =
      (if depth x = d then Real.exp (-β * cost d) / partition (cost ∘ depth) β else 0) := by
    intro x
    by_cases hx : depth x = d
    · simp [hx, gibbsLaw, Function.comp_apply]
    · simp [hx]
  simp_rw [ht]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-! ## Exact probability and amplitude correspondence -/

/-- Nonnegative real amplitudes of squared norm one. Phase is not part of this carrier. -/
def NonnegativeAmplitude (K : Type) [Fintype K] :=
  {a : K → ℝ // (∀ k, 0 ≤ a k) ∧ ∑ k, (a k) ^ 2 = 1}

/-- Equality of the probability masses determines the whole law. -/
theorem law_ext {K : Type} [Fintype K] {p q : HiddenDepthLaw K} (h : p.p = q.p) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- The positive square-root representation of a probability law. -/
def sqrtLaw {K : Type} [Fintype K] (p : HiddenDepthLaw K) : NonnegativeAmplitude K :=
  ⟨fun k => Real.sqrt (p.p k), fun k => Real.sqrt_nonneg _, by
    simp_rw [Real.sq_sqrt (p.nonneg _)]
    exact p.sum_one⟩

/-- Recover a law by squaring its nonnegative amplitudes. -/
def squareLaw {K : Type} [Fintype K] (a : NonnegativeAmplitude K) : HiddenDepthLaw K where
  p k := (a.val k) ^ 2
  nonneg _k := sq_nonneg _
  sum_one := a.property.2

/-- Probability laws and nonnegative unit amplitudes are equivalent, including zero masses.
This identifies the specified carriers, not classical laws with unrestricted quantum states. -/
def lawAmplitudeEquiv (K : Type) [Fintype K] : HiddenDepthLaw K ≃ NonnegativeAmplitude K where
  toFun := sqrtLaw
  invFun := squareLaw
  left_inv p := by
    apply law_ext
    funext k
    exact Real.sq_sqrt (p.nonneg k)
  right_inv a := by
    apply Subtype.ext
    funext k
    exact Real.sqrt_sq (a.property.1 k)

/-- Entropy-cost optimization transports through both directions of the equivalence. -/
theorem gibbs_amplitude_unique {K : Type} [Fintype K] [Nonempty K]
    (cost : K → ℝ) (β : ℝ) (a : NonnegativeAmplitude K) :
    entropyMinusCost cost β (squareLaw a).p ≤ entropyMinusCost cost β (gibbsLaw cost β).p ∧
      (entropyMinusCost cost β (squareLaw a).p = entropyMinusCost cost β (gibbsLaw cost β).p ↔
        a = sqrtLaw (gibbsLaw cost β)) := by
  have h := gibbs_unique_maximum cost β (squareLaw a)
  refine ⟨h.1, h.2.trans ?_⟩
  constructor
  · intro he
    have hp := congrArg sqrtLaw (law_ext he)
    exact ((lawAmplitudeEquiv K).apply_symm_apply a).symm.trans hp
  · intro he
    subst a
    exact congrArg HiddenDepthLaw.p ((lawAmplitudeEquiv K).symm_apply_apply _)

/-- Probability of the supplied evidence, or the normalization of a nonnegative likelihood. -/
def evidenceWeight {K : Type} [Fintype K] (p : HiddenDepthLaw K) (likelihood : K → ℝ) : ℝ :=
  ∑ k, likelihood k * p.p k

/-- Conditioning on evidence of positive weight. -/
def conditionLaw {K : Type} [Fintype K] (p : HiddenDepthLaw K) (likelihood : K → ℝ)
    (hL : ∀ k, 0 ≤ likelihood k) (hZ : 0 < evidenceWeight p likelihood) : HiddenDepthLaw K where
  p k := likelihood k * p.p k / evidenceWeight p likelihood
  nonneg k := div_nonneg (mul_nonneg (hL k) (p.nonneg k)) hZ.le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self hZ.ne'

/-- Conditioning then taking square roots equals multiplication by the square root of the
likelihood followed by normalization. This is the update law of the equivalence. -/
theorem sqrt_condition_commutes {K : Type} [Fintype K] (p : HiddenDepthLaw K)
    (likelihood : K → ℝ) (hL : ∀ k, 0 ≤ likelihood k)
    (hZ : 0 < evidenceWeight p likelihood) (k : K) :
    (sqrtLaw (conditionLaw p likelihood hL hZ)).val k =
      Real.sqrt (likelihood k) * (sqrtLaw p).val k / Real.sqrt (evidenceWeight p likelihood) := by
  change Real.sqrt (likelihood k * p.p k / evidenceWeight p likelihood) = _
  rw [Real.sqrt_div (mul_nonneg (hL k) (p.nonneg k)), Real.sqrt_mul (hL k)]
  rfl

/-- The amplitude update is normalized, with no assertion that all measurements have this form. -/
theorem sqrt_condition_normalized {K : Type} [Fintype K] (p : HiddenDepthLaw K)
    (likelihood : K → ℝ) (hL : ∀ k, 0 ≤ likelihood k)
    (hZ : 0 < evidenceWeight p likelihood) :
    (∑ k, (Real.sqrt (likelihood k) * (sqrtLaw p).val k /
      Real.sqrt (evidenceWeight p likelihood)) ^ 2) = 1 := by
  simp_rw [← sqrt_condition_commutes p likelihood hL hZ]
  exact (sqrtLaw (conditionLaw p likelihood hL hZ)).property.2

/-- With no evidence discrimination the probability law remains unchanged. -/
theorem condition_one {K : Type} [Fintype K] (p : HiddenDepthLaw K)
    (hZ : 0 < evidenceWeight p (fun _ => 1)) :
    conditionLaw p (fun _ => 1) (fun _ => zero_le_one) hZ = p := by
  apply law_ext
  funext k
  simp [conditionLaw, evidenceWeight, p.sum_one]

/-- The square-root representation of the finite burden law has half its quadratic exponent. -/
theorem burden_log_amplitude (n L : ℕ) (β : ℝ) (k : Fin (n + 1)) :
    Real.log ((sqrtLaw (burdenLaw n L β)).val k) =
      (β * L / 16 - Real.log (partition (fun j : Fin (n + 1) => (carrierRaw L j.val : ℝ)) β) / 2) -
        β * L / 4 * ((k.val : ℝ) + 3 / 2) ^ 2 := by
  change Real.log (Real.sqrt ((burdenLaw n L β).p k)) = _
  have hp : 0 ≤ (burdenLaw n L β).p k := (burdenLaw n L β).nonneg k
  rw [Real.log_sqrt hp, burden_log_density]
  ring

end

end OperatorKO7.Meta.BoundaryObserver.BurdenGibbs
