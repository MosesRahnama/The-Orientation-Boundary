import OperatorKO7.QEC.Codes.KnillLaflamme
import OperatorKO7.QEC.Bounds.CramerRao
import OperatorKO7.QEC.Dicke.Basis
import OperatorKO7.QEC.Operators.Projector
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false

/-!
# Abstention-aware decoder and projector-overlap identity

The theorem `prop_abstention_as_overlap` equates the decoder's weighted abstention quantity with the squared norm of the coherent Dicke state outside the code subspace. The result requires a binomial parameter in `[0,1]` and a posterior that matches the code-membership profile at every Dicke weight.
-/

namespace QEC.Codes.Abstention

open QEC.Codes.KnillLaflamme
open QEC.Dicke.Basis
open QEC.Operators
open QEC.Operators.Projector
open scoped BigOperators ComplexConjugate

variable {n : ℕ}

/-- Y/N/U/H output alphabet from Definition `def:abstention-decoder`. -/
inductive AbstentionDecision where
  | Y
  | N
  | U
  | H
  deriving DecidableEq, Repr

/-- Posterior data used by the abstention-aware decoder. The manuscript compares
the maximum-likelihood posterior `p_hat` against the Y/U thresholds and also
allows a direct no-correction branch through the identity posterior. -/
structure CalibratedPosterior where
  mlPosterior : ℝ
  identityPosterior : ℝ
  mlPosterior_nonneg : 0 ≤ mlPosterior
  mlPosterior_le_one : mlPosterior ≤ 1
  identityPosterior_nonneg : 0 ≤ identityPosterior
  identityPosterior_le_one : identityPosterior ≤ 1

/-- Threshold package for the abstention-aware decoder. -/
structure AbstentionDecoder where
  tauY : ℝ
  tauU : ℝ
  tauU_pos : 0 < tauU
  tauU_lt_tauY : tauU < tauY
  tauY_le_one : tauY ≤ 1

/-- Posterior profile for Dicke weights lying in the code subspace: the decoder
accepts the identity branch with full confidence. -/
def inCodePosterior : CalibratedPosterior where
  mlPosterior := 0
  identityPosterior := 1
  mlPosterior_nonneg := by norm_num
  mlPosterior_le_one := by norm_num
  identityPosterior_nonneg := by norm_num
  identityPosterior_le_one := by norm_num

/-- Posterior profile for Dicke weights lying outside the code subspace: the
decoder abstains because neither the correction nor the identity branch crosses
the confidence thresholds. -/
def outOfCodePosterior : CalibratedPosterior where
  mlPosterior := 0
  identityPosterior := 0
  mlPosterior_nonneg := by norm_num
  mlPosterior_le_one := by norm_num
  identityPosterior_nonneg := by norm_num
  identityPosterior_le_one := by norm_num

/-- Posterior assignment induced by the code-membership split of the Dicke basis. -/
def codeMembershipPosterior (S : Finset (Fin (n + 1))) (w : Fin (n + 1)) : CalibratedPosterior :=
  if w ∈ S then inCodePosterior else outOfCodePosterior

/-- Finite Dicke weights outside the code-subspace index set `S`. -/
def outsideCodeWeights (S : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun w => w ∉ S

noncomputable section

private theorem tauY_pos (decoder : AbstentionDecoder) : 0 < decoder.tauY :=
  lt_trans decoder.tauU_pos decoder.tauU_lt_tauY

/-- Manuscript Y/N/U/H decision rule. -/
def decide (decoder : AbstentionDecoder) (posterior : CalibratedPosterior) : AbstentionDecision :=
  if decoder.tauY ≤ posterior.mlPosterior then
    .Y
  else if decoder.tauY ≤ posterior.identityPosterior then
    .N
  else if decoder.tauU ≤ posterior.mlPosterior then
    .U
  else
    .H

private theorem decide_inCodePosterior (decoder : AbstentionDecoder) :
    decide decoder inCodePosterior = .N := by
  have htauY_pos : 0 < decoder.tauY := tauY_pos decoder
  unfold decide inCodePosterior
  simp [htauY_pos.not_ge, decoder.tauY_le_one]

private theorem decide_outOfCodePosterior (decoder : AbstentionDecoder) :
    decide decoder outOfCodePosterior = .H := by
  have htauY_pos : 0 < decoder.tauY := tauY_pos decoder
  unfold decide outOfCodePosterior
  simp [htauY_pos.not_ge, decoder.tauU_pos.not_ge]

/-- Operational abstention predicate: the decoder abstains exactly on the U and H branches. -/
def isAbstention (decision : AbstentionDecision) : Prop :=
  match decision with
  | .U => True
  | .H => True
  | .Y => False
  | .N => False

/-- Operational abstention rate. When `weight` is a normalized round-frequency or
probability mass function, this is the fraction of rounds that emit U or H. -/
def q_abst {Ω : Type*} [Fintype Ω]
    (decoder : AbstentionDecoder)
    (weight : Ω → ℝ)
    (posterior : Ω → CalibratedPosterior) : ℝ :=
  OperatorKO7.QEC.Bounds.CramerRao.weightedExpectation weight fun ω =>
    match decide decoder (posterior ω) with
    | .U => 1
    | .H => 1
    | .Y => 0
    | .N => 0

/-- The coherent-state binomial parameter `p_alpha = |alpha|² / n` from
Definition `def:coherent-trace`. -/
def coherentDickeProb (n : ℕ) (alpha : ℂ) : ℝ :=
  Complex.normSq alpha / (n : ℝ)

/-- Exact calibrated-confidence hypothesis used for
`prop_abstention_as_overlap`: the coherent Dicke parameter is a genuine
binomial probability and the posterior agrees pointwise with the projector's
code-membership split on Dicke weights. -/
def CalibratedConfidence
    (n : ℕ) (S : Finset (Fin (n + 1))) (alpha : ℂ)
    (posterior : Fin (n + 1) → CalibratedPosterior) : Prop :=
  coherentDickeProb n alpha ∈ Set.Icc 0 1 ∧
    ∀ w, posterior w = codeMembershipPosterior S w

/-- Born weight of Dicke weight `w` in the coherent Dicke state. -/
def coherentBornWeight (n : ℕ) (alpha : ℂ) (w : Fin (n + 1)) : ℝ :=
  (Nat.choose n w.1 : ℝ) *
    coherentDickeProb n alpha ^ w.1 *
    (1 - coherentDickeProb n alpha) ^ (n - w.1)

/-- Phase factor `exp(i w arg(alpha))` from Definition `def:coherent-trace`. -/
noncomputable def coherentDickePhase (alpha : ℂ) (w : Fin (n + 1)) : ℂ :=
  Complex.exp (Complex.I * ((w.1 : ℝ) : ℂ) * Complex.arg alpha)

/-- Dicke coefficient of the coherent Dicke state. -/
noncomputable def coherentDickeCoeff (n : ℕ) (alpha : ℂ) (w : Fin (n + 1)) : ℂ :=
  (Real.sqrt (coherentBornWeight n alpha w) : ℂ) * coherentDickePhase (n := n) alpha w

/-- Coherent Dicke state `ψ_alpha` as a finite Dicke-basis superposition. -/
noncomputable def coherentDickeState (n : ℕ) (alpha : ℂ) : QubitRegister n :=
  ∑ w : Fin (n + 1), coherentDickeCoeff n alpha w • dickeState n w

/-- Wavefunction abstention quantity for an arbitrary projector/state pair. -/
def q_abst_wf_of_projector (P_C : Op (QubitRegister n)) (ψ : QubitRegister n) : ℝ :=
  ‖((Op.id : Op (QubitRegister n)) - P_C) ψ‖ ^ 2

/-- Wavefunction abstention quantity from `prop:abstention-as-overlap`, specialized to the
code projector onto the Dicke span indexed by `S`. -/
def q_abst_wf (n : ℕ) (S : Finset (Fin (n + 1))) (alpha : ℂ) : ℝ :=
  q_abst_wf_of_projector (codeSubspaceProjector n S) (coherentDickeState n alpha)

private theorem coherentBornWeight_nonneg
    (n : ℕ) (alpha : ℂ)
    (hprob : coherentDickeProb n alpha ∈ Set.Icc 0 1)
    (w : Fin (n + 1)) :
    0 ≤ coherentBornWeight n alpha w := by
  rcases hprob with ⟨hprob_nonneg, hprob_le_one⟩
  unfold coherentBornWeight
  have hchoose : 0 ≤ (Nat.choose n w.1 : ℝ) := by
    positivity
  have hpow : 0 ≤ coherentDickeProb n alpha ^ w.1 := by
    exact pow_nonneg hprob_nonneg _
  have htail : 0 ≤ (1 - coherentDickeProb n alpha) ^ (n - w.1) := by
    exact pow_nonneg (sub_nonneg.mpr hprob_le_one) _
  exact mul_nonneg
    (mul_nonneg hchoose hpow)
    htail

private theorem coherentDickePhase_normSq (alpha : ℂ) (w : Fin (n + 1)) :
    Complex.normSq (coherentDickePhase (n := n) alpha w) = 1 := by
  unfold coherentDickePhase
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  have hre : (Complex.I * ((w.1 : ℝ) : ℂ) * Complex.arg alpha).re = 0 := by
    simp
  rw [hre, Real.exp_zero]
  norm_num

private theorem coherentDickeCoeff_normSq
    (n : ℕ) (alpha : ℂ)
    (hprob : coherentDickeProb n alpha ∈ Set.Icc 0 1)
    (w : Fin (n + 1)) :
    Complex.normSq (coherentDickeCoeff n alpha w) = coherentBornWeight n alpha w := by
  have hnonneg : 0 ≤ coherentBornWeight n alpha w :=
    coherentBornWeight_nonneg n alpha hprob w
  unfold coherentDickeCoeff
  rw [Complex.normSq_mul, coherentDickePhase_normSq, Complex.normSq_ofReal,
    mul_assoc]
  calc
    Real.sqrt (coherentBornWeight n alpha w) *
        (Real.sqrt (coherentBornWeight n alpha w) * 1)
      = Real.sqrt (coherentBornWeight n alpha w) *
          Real.sqrt (coherentBornWeight n alpha w) := by ring
    _ = coherentBornWeight n alpha w := by rw [Real.mul_self_sqrt hnonneg]

private theorem coherentDickeState_split
    (n : ℕ) (S : Finset (Fin (n + 1))) (alpha : ℂ) :
    coherentDickeState n alpha =
      (∑ w ∈ S, coherentDickeCoeff n alpha w • dickeState n w) +
        ∑ w ∈ outsideCodeWeights S, coherentDickeCoeff n alpha w • dickeState n w := by
  classical
  rw [coherentDickeState]
  simpa [outsideCodeWeights] using
    (Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ)
      (p := fun w : Fin (n + 1) => w ∈ S)
      (f := fun w => coherentDickeCoeff n alpha w • dickeState n w)).symm

private theorem outsideCodeSum_inner_eq_zero
    (n : ℕ) (S : Finset (Fin (n + 1))) (alpha : ℂ)
    {w : Fin (n + 1)} (hw : w ∈ S) :
    inner ℂ
      (∑ w' ∈ outsideCodeWeights S, coherentDickeCoeff n alpha w' • dickeState n w')
      (dickeState n w) = 0 := by
  classical
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro w' hw'
  rw [inner_smul_left]
  have hw'_not_mem : w' ∉ S := by
    simpa [outsideCodeWeights] using hw'
  have hw'_ne : w' ≠ w := by
    intro hEq
    exact hw'_not_mem (hEq.symm ▸ hw)
  simp [orthonormal_iff_ite.mp (dickeState_orthonormal n), hw'_ne]

private theorem outsideCodeSum_orthogonal_codeSubspace
    (n : ℕ) (S : Finset (Fin (n + 1))) (alpha : ℂ) :
    ∀ z ∈ codeSubspace n S,
      inner ℂ
        (∑ w ∈ outsideCodeWeights S, coherentDickeCoeff n alpha w • dickeState n w)
        z = 0 := by
  classical
  intro z hz
  unfold codeSubspace at hz
  let outside : QubitRegister n :=
    ∑ w ∈ outsideCodeWeights S, coherentDickeCoeff n alpha w • dickeState n w
  change inner ℂ outside z = 0
  refine Submodule.span_induction
      (p := fun x _ => inner ℂ outside x = 0) ?_ ?_ ?_ ?_ hz
  · intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    simpa [outside] using outsideCodeSum_inner_eq_zero n S alpha hw
  · simp
  · intro x y hx hy hx0 hy0
    simp [inner_add_right, hx0, hy0]
  · intro a x hx hx0
    simp [inner_smul_right, hx0]

private theorem codeSubspaceProjector_coherentDickeState
    (n : ℕ) (S : Finset (Fin (n + 1))) (alpha : ℂ) :
    codeSubspaceProjector n S (coherentDickeState n alpha) =
      ∑ w ∈ S, coherentDickeCoeff n alpha w • dickeState n w := by
  classical
  set inside : QubitRegister n := ∑ w ∈ S, coherentDickeCoeff n alpha w • dickeState n w
  set outside : QubitRegister n :=
    ∑ w ∈ outsideCodeWeights S, coherentDickeCoeff n alpha w • dickeState n w
  have hsplit : coherentDickeState n alpha = inside + outside := by
    simpa [inside, outside] using coherentDickeState_split n S alpha
  have hinside_mem : inside ∈ codeSubspace n S := by
    simpa [inside] using
      (dickeLinearCombo_mem_codeSubspace (n := n) S (coherentDickeCoeff n alpha))
  have hdiff : coherentDickeState n alpha - inside = outside := by
    rw [hsplit]
    simp [sub_eq_add_neg, add_assoc]
  have horth : ∀ z ∈ codeSubspace n S, inner ℂ (coherentDickeState n alpha - inside) z = 0 := by
    intro z hz
    rw [hdiff]
    simpa [outside] using outsideCodeSum_orthogonal_codeSubspace n S alpha z hz
  unfold codeSubspaceProjector
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero hinside_mem horth

private theorem q_abst_eq_sum_outsideCodeWeights
    (n : ℕ) (S : Finset (Fin (n + 1))) (alpha : ℂ)
    (decoder : AbstentionDecoder)
    (posterior : Fin (n + 1) → CalibratedPosterior)
    (hposterior : ∀ w, posterior w = codeMembershipPosterior S w) :
    q_abst decoder (coherentBornWeight n alpha) posterior =
      ∑ w ∈ outsideCodeWeights S, coherentBornWeight n alpha w := by
  classical
  unfold q_abst OperatorKO7.QEC.Bounds.CramerRao.weightedExpectation
  simp_rw [hposterior]
  have hsplit :
      (fun w : Fin (n + 1) =>
        coherentBornWeight n alpha w *
          match decide decoder (codeMembershipPosterior S w) with
          | .U => 1
          | .H => 1
          | .Y => 0
          | .N => 0) =
        fun w : Fin (n + 1) => if w ∈ S then 0 else coherentBornWeight n alpha w := by
    funext w
    by_cases hw : w ∈ S
    · simp [codeMembershipPosterior, hw, decide_inCodePosterior]
    · simp [codeMembershipPosterior, hw, decide_outOfCodePosterior]
  rw [hsplit]
  let f : Fin (n + 1) → ℝ := coherentBornWeight n alpha
  have hsum :
      ∀ t : Finset (Fin (n + 1)),
        (∑ w ∈ t, if w ∈ S then 0 else f w) = ∑ w ∈ t.filter (fun w => w ∉ S), f w := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · simp
    · intro a t ha ht
      by_cases hmem : a ∈ S
      · simp [Finset.filter_insert, ha, hmem, ht]
      · simp [Finset.filter_insert, ha, hmem, ht]
  simpa [f, outsideCodeWeights] using hsum Finset.univ

private theorem q_abst_wf_eq_sum_outsideCodeWeights
    (n : ℕ) (S : Finset (Fin (n + 1))) (alpha : ℂ)
    (hprob : coherentDickeProb n alpha ∈ Set.Icc 0 1) :
    q_abst_wf n S alpha =
      ∑ w ∈ outsideCodeWeights S, coherentBornWeight n alpha w := by
  classical
  set inside : QubitRegister n := ∑ w ∈ S, coherentDickeCoeff n alpha w • dickeState n w
  set outside : QubitRegister n :=
    ∑ w ∈ outsideCodeWeights S, coherentDickeCoeff n alpha w • dickeState n w
  have hsplit : coherentDickeState n alpha = inside + outside := by
    simpa [inside, outside] using coherentDickeState_split n S alpha
  have hproj : codeSubspaceProjector n S (coherentDickeState n alpha) = inside := by
    simpa [inside] using codeSubspaceProjector_coherentDickeState n S alpha
  have hdiff : coherentDickeState n alpha - inside = outside := by
    rw [hsplit]
    simp [sub_eq_add_neg, add_assoc]
  have hcomplement :
      ((Op.id : Op (QubitRegister n)) - codeSubspaceProjector n S) (coherentDickeState n alpha) =
        outside := by
    rw [complement_apply, hproj, hdiff]
  unfold q_abst_wf q_abst_wf_of_projector
  rw [hcomplement]
  apply Complex.ofReal_injective
  have hnorm_cast : ((‖outside‖ ^ 2 : ℝ) : ℂ) = ((‖outside‖ : ℂ) ^ 2) := by
    norm_num
  calc
    (((‖outside‖ ^ 2 : ℝ) : ℂ)) = inner ℂ outside outside := by
      rw [hnorm_cast]
      exact (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) outside).symm
    _ = ↑(∑ w ∈ outsideCodeWeights S, coherentBornWeight n alpha w) := by
      rw [(dickeState_orthonormal n).inner_sum
        (fun w => coherentDickeCoeff n alpha w)
        (fun w => coherentDickeCoeff n alpha w)
        (outsideCodeWeights S)]
      simp_rw [← Complex.normSq_eq_conj_mul_self]
      have hcoeff :
          ∑ w ∈ outsideCodeWeights S, Complex.normSq (coherentDickeCoeff n alpha w) =
            ∑ w ∈ outsideCodeWeights S, coherentBornWeight n alpha w := by
        refine Finset.sum_congr rfl ?_
        intro w hw
        exact coherentDickeCoeff_normSq n alpha hprob w
      simpa using congrArg (fun r : ℝ => (r : ℂ)) hcoeff

/-- Exact projector-overlap identity: the wavefunction abstention rate is the squared norm
of the component of `ψ_alpha` in the orthogonal complement of the code subspace. -/
theorem q_abst_wf_eq_projector_complement (n : ℕ) (S : Finset (Fin (n + 1))) (alpha : ℂ) :
    q_abst_wf n S alpha =
      ‖((Op.id : Op (QubitRegister n)) - codeSubspaceProjector n S)
          (coherentDickeState n alpha)‖ ^ 2 := by
  rfl

/-- Exact projector-overlap identity rewritten by Pythagoras for orthogonal projectors. -/
theorem q_abst_wf_eq_norm_sq_sub_code_overlap
    (n : ℕ) (S : Finset (Fin (n + 1))) (alpha : ℂ) :
    q_abst_wf n S alpha =
      ‖coherentDickeState n alpha‖ ^ 2 -
        ‖codeSubspaceProjector n S (coherentDickeState n alpha)‖ ^ 2 := by
  unfold q_abst_wf q_abst_wf_of_projector
  simpa using
    (complement_norm_sq_eq
      (n := n)
      (P := codeSubspaceProjector n S)
      (codeSubspaceProjector_isProjector n S)
      (coherentDickeState n alpha))

/-- Manuscript label `prop:abstention-as-overlap`, formalized by requiring that
the calibrated posterior agree exactly with the projector-defined code-membership
split on Dicke weights. Physically, the decoder emits N on the in-code support
and abstains on the orthogonal complement, so both operational and wavefunction
rates are the same binomial outside-mass. -/
theorem prop_abstention_as_overlap
    (n : ℕ) (S : Finset (Fin (n + 1))) (alpha : ℂ)
    (decoder : AbstentionDecoder)
    (posterior : Fin (n + 1) → CalibratedPosterior)
    (calibrated : CalibratedConfidence n S alpha posterior) :
    q_abst decoder (coherentBornWeight n alpha) posterior = q_abst_wf n S alpha := by
  rcases calibrated with ⟨hprob, hposterior⟩
  rw [q_abst_eq_sum_outsideCodeWeights n S alpha decoder posterior hposterior,
    q_abst_wf_eq_sum_outsideCodeWeights n S alpha hprob]

end

end QEC.Codes.Abstention
