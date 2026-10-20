import OperatorKO7.Meta.UUET.Statistics.BernoulliInstance
import OperatorKO7.Meta.UUET.Probability.Channel

set_option autoImplicit false

/-!
# Fisher data processing under a finite Markov kernel

Relation: output law and tangent are finite pushforwards through one fixed kernel.
Closure: the squared score residual derives contraction and its equality criterion.
Trust: native finite sums and real differentiation, with paired axiom checks.
Scope: positive attained support and a parameter-independent normalized kernel.
-/

namespace OperatorKO7.Meta.UUET.Statistics

open scoped BigOperators
open OperatorKO7.Meta.UUET.Probability

/-- Exact statement-carrying finite Markov-kernel Fisher model. -/
structure FisherMarkovCertificate
    (Ω Γ : Type) [Fintype Ω] [Fintype Γ] where
  input : ParametricFamily Ω
  output : ParametricFamily Γ
  kernel : Channel Ω Γ
  output_probability : forall γ,
    output.probability γ = ∑ ω, input.probability ω * (kernel.row ω).mass γ
  output_tangent : forall γ,
    output.tangent γ = ∑ ω, input.tangent ω * (kernel.row ω).mass γ
  conditionalScoreProjection :
    fisherInformation output <= fisherInformation input

/-- CONDITIONAL MODEL: Fisher contracts under the certified finite Markov kernel. -/
theorem fisher_data_processing_under_markov_kernel
    {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (C : FisherMarkovCertificate Ω Γ) :
    fisherInformation C.output <= fisherInformation C.input :=
  C.conditionalScoreProjection

/-- Native finite consequence: identity processing preserves Fisher information. -/
theorem fisher_identity_processing {Ω : Type} [Fintype Ω]
    (F : ParametricFamily Ω) :
    fisherInformation F <= fisherInformation F := le_rfl

/-- Native negative fixture: a parameter-insensitive output carries zero Fisher. -/
theorem constant_output_fisher_zero :
    fisherInformation constantBinaryFamily = 0 :=
  constant_family_fisher_zero

/-- NO-TRANSPORT: the old finite-difference surrogate lacks this structure. -/
structure FisherDPITransportGap where
  missingStructure : String
  exactRequirement : missingStructure =
    "output score as conditional expectation of the input score"

def fisherDPI_noTransport : FisherDPITransportGap where
  missingStructure :=
    "output score as conditional expectation of the input score"
  exactRequirement := rfl


/-! ## Fisher contraction derived from the finite channel

Proof graph: nodes F0-F6 and X. The probability and tangent identities determine the residual as a sum of squares.
-/

/-- The loss of Fisher information is the mean squared score residual. -/
theorem fisher_score_residual_identity
    {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (F : ParametricFamily Ω) (G : ParametricFamily Γ) (K : Channel Ω Γ)
    (hp : ∀ γ, G.probability γ = ∑ ω, F.probability ω * (K.row ω).mass γ)
    (ht : ∀ γ, G.tangent γ = ∑ ω, F.tangent ω * (K.row ω).mass γ) :
    fisherInformation F - fisherInformation G =
      ∑ γ, ∑ ω, F.probability ω * (K.row ω).mass γ *
        (score F ω - score G γ) ^ 2 := by
  have hcross (γ : Γ) :
      (∑ ω, F.probability ω * (K.row ω).mass γ * score F ω) = G.tangent γ := by
    rw [ht]
    apply Finset.sum_congr rfl
    intro ω _
    rw [← probability_mul_score F ω]
    ring
  have hinner (γ : Γ) :
      (∑ ω, F.probability ω * (K.row ω).mass γ * (score F ω - score G γ) ^ 2) =
        (∑ ω, F.probability ω * (K.row ω).mass γ * score F ω ^ 2) -
          G.probability γ * score G γ ^ 2 := by
    calc
      _ = ∑ ω, (F.probability ω * (K.row ω).mass γ * score F ω ^ 2 -
          (2 * score G γ) * (F.probability ω * (K.row ω).mass γ * score F ω) +
          score G γ ^ 2 * (F.probability ω * (K.row ω).mass γ)) := by
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = (∑ ω, F.probability ω * (K.row ω).mass γ * score F ω ^ 2) -
          (2 * score G γ) * (∑ ω, F.probability ω * (K.row ω).mass γ * score F ω) +
          score G γ ^ 2 * (∑ ω, F.probability ω * (K.row ω).mass γ) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by
        rw [hcross, ← hp γ, ← probability_mul_score G γ]
        ring
  have hfirst :
      (∑ γ, ∑ ω, F.probability ω * (K.row ω).mass γ * score F ω ^ 2) =
        fisherInformation F := by
    rw [Finset.sum_comm]
    unfold fisherInformation
    apply Finset.sum_congr rfl
    intro ω _
    calc
      _ = (F.probability ω * score F ω ^ 2) * ∑ γ, (K.row ω).mass γ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro γ _
        ring
      _ = _ := by rw [(K.row ω).total, mul_one]
  symm
  calc
    _ = (∑ γ, ∑ ω, F.probability ω * (K.row ω).mass γ * score F ω ^ 2) -
        ∑ γ, G.probability γ * score G γ ^ 2 := by
      simp_rw [hinner]
      rw [Finset.sum_sub_distrib]
    _ = _ := by rw [hfirst]; rfl

/-- A fixed finite channel contracts Fisher information. -/
theorem fisher_data_processing_of_pushforward
    {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (F : ParametricFamily Ω) (G : ParametricFamily Γ) (K : Channel Ω Γ)
    (hp : ∀ γ, G.probability γ = ∑ ω, F.probability ω * (K.row ω).mass γ)
    (ht : ∀ γ, G.tangent γ = ∑ ω, F.tangent ω * (K.row ω).mass γ) :
    fisherInformation G ≤ fisherInformation F := by
  have h : 0 ≤ fisherInformation F - fisherInformation G := by
    rw [fisher_score_residual_identity F G K hp ht]
    exact Finset.sum_nonneg fun γ _ => Finset.sum_nonneg fun ω _ =>
      mul_nonneg (mul_nonneg (F.probability_nonnegative ω) ((K.row ω).nonnegative γ))
        (sq_nonneg _)
  linarith

/-- Equality holds on channels that retain the input score on every possible output. -/
theorem fisher_equality_iff_score_preserved
    {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (F : ParametricFamily Ω) (G : ParametricFamily Γ) (K : Channel Ω Γ)
    (hp : ∀ γ, G.probability γ = ∑ ω, F.probability ω * (K.row ω).mass γ)
    (ht : ∀ γ, G.tangent γ = ∑ ω, F.tangent ω * (K.row ω).mass γ) :
    fisherInformation G = fisherInformation F ↔
      ∀ ω γ, 0 < (K.row ω).mass γ → score F ω = score G γ := by
  have hn (γ : Γ) (ω : Ω) :
      0 ≤ F.probability ω * (K.row ω).mass γ * (score F ω - score G γ) ^ 2 :=
    mul_nonneg (mul_nonneg (F.probability_nonnegative ω) ((K.row ω).nonnegative γ))
      (sq_nonneg _)
  constructor
  · intro heq ω γ hk
    have hz :
        (∑ γ, ∑ ω, F.probability ω * (K.row ω).mass γ *
          (score F ω - score G γ) ^ 2) = 0 := by
      rw [← fisher_score_residual_identity F G K hp ht, heq, sub_self]
    have hle :
        F.probability ω * (K.row ω).mass γ * (score F ω - score G γ) ^ 2 ≤
          ∑ γ, ∑ ω, F.probability ω * (K.row ω).mass γ *
            (score F ω - score G γ) ^ 2 := by
      calc
        _ ≤ ∑ ω, F.probability ω * (K.row ω).mass γ * (score F ω - score G γ) ^ 2 :=
          Finset.single_le_sum (fun ω _ => hn γ ω) (Finset.mem_univ ω)
        _ ≤ _ := Finset.single_le_sum
          (fun γ _ => Finset.sum_nonneg fun ω _ => hn γ ω) (Finset.mem_univ γ)
    have hzero := le_antisymm (hle.trans_eq hz) (hn γ ω)
    have hsquare : (score F ω - score G γ) ^ 2 = 0 :=
      (mul_eq_zero.mp hzero).resolve_left (ne_of_gt (mul_pos (F.positive_support ω) hk))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro h
    apply Eq.symm
    apply sub_eq_zero.mp
    rw [fisher_score_residual_identity F G K hp ht]
    apply Finset.sum_eq_zero
    intro γ _
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hk : (K.row ω).mass γ = 0
    · simp [hk]
    · have hkpos : 0 < (K.row ω).mass γ :=
        lt_of_le_of_ne ((K.row ω).nonnegative γ) (Ne.symm hk)
      rw [h ω γ hkpos, sub_self]
      norm_num

/-- A common output can merge only equal input scores at equality. -/
theorem fisher_equality_iff_common_output_scores
    {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (F : ParametricFamily Ω) (G : ParametricFamily Γ) (K : Channel Ω Γ)
    (hp : ∀ γ, G.probability γ = ∑ ω, F.probability ω * (K.row ω).mass γ)
    (ht : ∀ γ, G.tangent γ = ∑ ω, F.tangent ω * (K.row ω).mass γ) :
    fisherInformation G = fisherInformation F ↔
      ∀ ω ω' γ, 0 < (K.row ω).mass γ → 0 < (K.row ω').mass γ →
        score F ω = score F ω' := by
  rw [fisher_equality_iff_score_preserved F G K hp ht]
  constructor
  · intro h ω ω' γ hω hω'
    exact (h ω γ hω).trans (h ω' γ hω').symm
  · intro h ω γ hk
    have hg : G.tangent γ = score F ω * G.probability γ := by
      rw [ht, hp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω' _
      by_cases hk' : (K.row ω').mass γ = 0
      · simp [hk']
      · have hkpos : 0 < (K.row ω').mass γ :=
          lt_of_le_of_ne ((K.row ω').nonnegative γ) (Ne.symm hk')
        rw [← probability_mul_score F ω', ← h ω ω' γ hk hkpos]
        ring
    unfold score
    rw [hg]
    exact (mul_div_cancel_right₀ _ (ne_of_gt (G.positive_support γ))).symm

/-- Build the existing certificate using the derived contraction theorem. -/
def FisherMarkovCertificate.ofPushforward
    {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (F : ParametricFamily Ω) (G : ParametricFamily Γ) (K : Channel Ω Γ)
    (hp : ∀ γ, G.probability γ = ∑ ω, F.probability ω * (K.row ω).mass γ)
    (ht : ∀ γ, G.tangent γ = ∑ ω, F.tangent ω * (K.row ω).mass γ) :
    FisherMarkovCertificate Ω Γ where
  input := F
  output := G
  kernel := K
  output_probability := hp
  output_tangent := ht
  conditionalScoreProjection := fisher_data_processing_of_pushforward F G K hp ht

/-- Push the local law and tangent through a finite channel. -/
noncomputable def ParametricFamily.pushforward
    {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (F : ParametricFamily Ω) (K : Channel Ω Γ)
    (hpos : ∀ γ, 0 < ∑ ω, F.probability ω * (K.row ω).mass γ) :
    ParametricFamily Γ where
  parameter := F.parameter
  probability := fun γ => ∑ ω, F.probability ω * (K.row ω).mass γ
  tangent := fun γ => ∑ ω, F.tangent ω * (K.row ω).mass γ
  probability_nonnegative := fun γ => Finset.sum_nonneg fun ω _ =>
    mul_nonneg (F.probability_nonnegative ω) ((K.row ω).nonnegative γ)
  probability_total := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ ω, F.probability ω := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [← Finset.mul_sum, (K.row ω).total, mul_one]
      _ = 1 := F.probability_total
  tangent_total_zero := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ ω, F.tangent ω := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [← Finset.mul_sum, (K.row ω).total, mul_one]
      _ = 0 := F.tangent_total_zero
  positive_support := hpos

/-- A channel and its pushed local family produce a derived certificate. -/
noncomputable def FisherMarkovCertificate.fromChannel
    {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (F : ParametricFamily Ω) (K : Channel Ω Γ)
    (hpos : ∀ γ, 0 < ∑ ω, F.probability ω * (K.row ω).mass γ) :
    FisherMarkovCertificate Ω Γ :=
  FisherMarkovCertificate.ofPushforward F (F.pushforward K hpos) K
    (fun _ => rfl) (fun _ => rfl)

/-- Probability transfer alone does not imply Fisher contraction. -/
theorem fisher_probability_transfer_alone_insufficient :
    (∀ γ : Fin 2, bernoulliHalfFamily.probability γ =
      ∑ ω, constantBinaryFamily.probability ω *
        ((Channel.identity (Fin 2)).row ω).mass γ) ∧
      ¬ fisherInformation bernoulliHalfFamily ≤ fisherInformation constantBinaryFamily := by
  constructor
  · intro γ
    fin_cases γ <;>
      norm_num [bernoulliHalfFamily, bernoulliFamily, constantBinaryFamily,
        Channel.identity, Channel.deterministic, FiniteDistribution.pointMass, Fin.sum_univ_two]
  · rw [bernoulli_half_fisher_exact, constant_family_fisher_zero]
    norm_num


/-- Positive local statistical data arise from an actually differentiable normalized curve. -/
noncomputable def ParametricFamily.ofCurve
    {Ω : Type} [Fintype Ω] (p : ℝ → Ω → ℝ) (θ : ℝ)
    (hd : ∀ ω, DifferentiableAt ℝ (fun t => p t ω) θ)
    (hpos : ∀ ω, 0 < p θ ω)
    (hn : (fun t => ∑ ω, p t ω) =ᶠ[nhds θ] fun _ => (1 : ℝ)) :
    ParametricFamily Ω where
  parameter := θ
  probability := p θ
  tangent := fun ω => deriv (fun t => p t ω) θ
  probability_nonnegative := fun ω => (hpos ω).le
  probability_total := hn.eq_of_nhds
  tangent_total_zero := by
    have hs : HasDerivAt (fun t => ∑ ω, p t ω)
        (∑ ω, deriv (fun t => p t ω) θ) θ :=
      HasDerivAt.fun_sum (fun ω _ => (hd ω).hasDerivAt)
    exact hs.unique ((hasDerivAt_const θ (1 : ℝ)).congr_of_eventuallyEq hn)
  positive_support := hpos

/-- Differentiation commutes with a parameter-independent finite Markov kernel. -/
theorem channel_pushforward_hasDerivAt
    {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (p : ℝ → Ω → ℝ) (θ : ℝ) (K : Channel Ω Γ)
    (hd : ∀ ω, DifferentiableAt ℝ (fun t => p t ω) θ) (γ : Γ) :
    HasDerivAt (fun t => ∑ ω, p t ω * (K.row ω).mass γ)
      (∑ ω, deriv (fun t => p t ω) θ * (K.row ω).mass γ) θ :=
  HasDerivAt.fun_sum (fun ω _ => (hd ω).hasDerivAt.mul_const ((K.row ω).mass γ))

/-- The score form of Fisher information equals its derivative-over-probability form. -/
theorem fisherInformation_eq_tangent_square_div
    {Ω : Type} [Fintype Ω] (F : ParametricFamily Ω) :
    fisherInformation F = ∑ ω, F.tangent ω ^ 2 / F.probability ω := by
  unfold fisherInformation score
  apply Finset.sum_congr rfl
  intro ω _
  field_simp [ne_of_gt (F.positive_support ω)]
  ring

/-- For a deterministic observation, Fisher equality is exactly score constancy on fibers. -/
theorem fisher_equality_iff_fiber_constant
    {Ω Γ : Type} [Fintype Ω] [Fintype Γ] [DecidableEq Γ]
    (F : ParametricFamily Ω) (G : ParametricFamily Γ) (q : Ω → Γ)
    (hp : ∀ γ, G.probability γ =
      ∑ ω, F.probability ω * ((Channel.deterministic q).row ω).mass γ)
    (ht : ∀ γ, G.tangent γ =
      ∑ ω, F.tangent ω * ((Channel.deterministic q).row ω).mass γ) :
    fisherInformation G = fisherInformation F ↔
      ∀ ω ω', q ω = q ω' → score F ω = score F ω' := by
  classical
  rw [fisher_equality_iff_common_output_scores F G (Channel.deterministic q) hp ht]
  constructor
  · intro h ω ω' hq
    apply h ω ω' (q ω)
    · simp [Channel.deterministic, FiniteDistribution.pointMass]
    · simp [Channel.deterministic, FiniteDistribution.pointMass, hq]
  · intro h ω ω' γ hω hω'
    have hq : q ω = γ := by
      by_contra hn
      simp [Channel.deterministic, FiniteDistribution.pointMass, Ne.symm hn] at hω
    have hq' : q ω' = γ := by
      by_contra hn
      simp [Channel.deterministic, FiniteDistribution.pointMass, Ne.symm hn] at hω'
    exact h ω ω' (hq.trans hq'.symm)

/-! Imported NameGate and TypeGate. -/
#check @Channel.row
#check @fisherInformation
#check @FisherMarkovCertificate.output_tangent
#check @FisherMarkovCertificate.conditionalScoreProjection

#check @fisher_data_processing_under_markov_kernel
#check @fisher_identity_processing
#check @constant_output_fisher_zero
#print axioms fisher_data_processing_under_markov_kernel
#print axioms fisher_identity_processing
#print axioms constant_output_fisher_zero

#check @fisher_score_residual_identity
#print axioms fisher_score_residual_identity
#check @fisher_data_processing_of_pushforward
#print axioms fisher_data_processing_of_pushforward
#check @fisher_equality_iff_score_preserved
#print axioms fisher_equality_iff_score_preserved
#check @fisher_equality_iff_common_output_scores
#print axioms fisher_equality_iff_common_output_scores
#check @FisherMarkovCertificate.ofPushforward
#print axioms FisherMarkovCertificate.ofPushforward
#check @ParametricFamily.pushforward
#print axioms ParametricFamily.pushforward
#check @FisherMarkovCertificate.fromChannel
#print axioms FisherMarkovCertificate.fromChannel
#check @fisher_probability_transfer_alone_insufficient
#print axioms fisher_probability_transfer_alone_insufficient

#check @ParametricFamily.ofCurve
#print axioms ParametricFamily.ofCurve
#check @channel_pushforward_hasDerivAt
#print axioms channel_pushforward_hasDerivAt
#check @fisherInformation_eq_tangent_square_div
#print axioms fisherInformation_eq_tangent_square_div
#check @fisher_equality_iff_fiber_constant
#print axioms fisher_equality_iff_fiber_constant

end OperatorKO7.Meta.UUET.Statistics

