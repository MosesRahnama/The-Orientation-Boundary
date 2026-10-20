import OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
import OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy

/-!
# Terminal count, conditional entropy, and reading cost

The finite target carrier is the reachable-terminal subtype in the manuscript
application. All information and residual terms use the same ConditionalProtocol.
Relation: finite probability laws with retained histories.
Property: entropy identity and cost bounds in bits.
External trust: none.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.TerminalGapCost

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open scoped BigOperators

noncomputable section

/-- The cardinality envelope of the finite target carrier, in bits. -/
def terminalEnvelope (Z : Type) [Fintype Z] : ℝ :=
  Real.log (Fintype.card Z : ℝ) / Real.log 2

variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

/-- Initial target entropy conditional on the retained initial record. -/
def priorEntropy (p : ConditionalProtocol H0 Z A Y) : ℝ :=
  ∑ u, p.initialRecord.mass u * entropy (p.given u).prior.mass

/-- The terminal envelope minus the actual conditional prior entropy. -/
def priorSlack (p : ConditionalProtocol H0 Z A Y) : ℝ :=
  terminalEnvelope Z - priorEntropy p

/-- The terminal envelope minus information in the actual retained transcript. -/
def terminalGap (p : ConditionalProtocol H0 Z A Y) (n : ℕ) : ℝ :=
  terminalEnvelope Z - conditionalJointInfo p n (historyBank A Y n)

/-- Conditional target entropy in the actual stopped joint law. -/
def residualEntropy (p : ConditionalProtocol H0 Z A Y) (n : ℕ) : ℝ :=
  ∑ u, ∑ h ∈ historySet (A × Y) n,
    massUncertainty (fun z => conditionalStoppedMass p n u z h)

/-- The weighted prior entropy equals the initial joint-entropy difference. -/
theorem priorEntropy_eq_joint_sub (p : ConditionalProtocol H0 Z A Y) :
    priorEntropy p = entropy p.initialJoint.mass - entropy p.initialRecord.mass := by
  rw [conditionalInitial_entropy p]
  simp only [priorEntropy, add_sub_cancel_left]

/-- The residual identity uses the same initial and stopped joint laws. -/
theorem terminalGap_eq_priorSlack_add_residual (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) : terminalGap p n = priorSlack p + residualEntropy p n := by
  unfold terminalGap priorSlack residualEntropy
  rw [conditionalJointInfo_eq_entropy_sub p n _ (historyBank_complete A Y n),
    ← priorEntropy_eq_joint_sub p]
  ring

/-- Every actual stopped conditional cell has nonnegative residual entropy. -/
theorem residualEntropy_nonnegative (p : ConditionalProtocol H0 Z A Y) (n : ℕ) :
    0 ≤ residualEntropy p n := by
  unfold residualEntropy
  apply Finset.sum_nonneg
  intro u _
  apply Finset.sum_nonneg
  intro h _
  change 0 ≤ massUncertainty
    (fun z => p.initialRecord.mass u * stoppedMass (p.given u) n z h)
  rw [massUncertainty_scale]
  exact mul_nonneg (p.initialRecord.nonnegative u)
    (stoppedUncertainty_nonnegative (p.given u) n h)

/-- Finite Shannon entropy bounds every conditional prior by the same envelope. -/
theorem priorEntropy_le_envelope [Nonempty Z] (p : ConditionalProtocol H0 Z A Y) :
    priorEntropy p ≤ terminalEnvelope Z := by
  have hp (u : H0) : entropy (p.given u).prior.mass ≤ terminalEnvelope Z := by
    rw [entropy_eq_HBits]
    exact HBits_le_logb_card (p.given u).prior.mass
      (p.given u).prior.nonnegative (p.given u).prior.total
  unfold priorEntropy
  calc
    (∑ u, p.initialRecord.mass u * entropy (p.given u).prior.mass) ≤
        ∑ u, p.initialRecord.mass u * terminalEnvelope Z :=
      Finset.sum_le_sum (fun u _ =>
        mul_le_mul_of_nonneg_left (hp u) (p.initialRecord.nonnegative u))
    _ = terminalEnvelope Z := by
      rw [← Finset.sum_mul, p.initialRecord.total, one_mul]

/-- The prior correction is nonnegative on a nonempty finite target carrier. -/
theorem priorSlack_nonnegative [Nonempty Z] (p : ConditionalProtocol H0 Z A Y) :
    0 ≤ priorSlack p := sub_nonneg.mpr (priorEntropy_le_envelope p)

/-- Residual entropy places the prior correction below every finite gap. -/
theorem priorSlack_le_terminalGap (p : ConditionalProtocol H0 Z A Y) (n : ℕ) :
    priorSlack p ≤ terminalGap p n := by
  rw [terminalGap_eq_priorSlack_add_residual]
  exact le_add_of_nonneg_right (residualEntropy_nonnegative p n)

/-- The coupled finite gap is nonnegative. -/
theorem terminalGap_nonnegative [Nonempty Z] (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) : 0 ≤ terminalGap p n :=
  (priorSlack_nonnegative p).trans (priorSlack_le_terminalGap p n)

/-- Information in the actual retained law is nonnegative. -/
theorem conditionalInformation_nonnegative (p : ConditionalProtocol H0 Z A Y) (n : ℕ) :
    0 ≤ conditionalJointInfo p n (historyBank A Y n) := by
  rw [conditionalJointInfo_eq_conditionalMI p n _ (historyBank_complete A Y n)]
  exact conditionalMI_nonnegative p n _ (historyBank_complete A Y n)

/-- Nonnegative acquired information places the envelope above every finite gap. -/
theorem terminalGap_le_envelope (p : ConditionalProtocol H0 Z A Y) (n : ℕ) :
    terminalGap p n ≤ terminalEnvelope Z :=
  sub_le_self _ (conditionalInformation_nonnegative p n)

/-- Complete recovery leaves the prior correction. -/
theorem terminalGap_eq_priorSlack_of_zero_residual (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (h : residualEntropy p n = 0) : terminalGap p n = priorSlack p := by
  rw [terminalGap_eq_priorSlack_add_residual, h, add_zero]

/-- A threshold strictly below the prior correction is unattainable. -/
theorem terminalGap_not_le_of_lt_priorSlack (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (g : ℝ) (hg : g < priorSlack p) : ¬ terminalGap p n ≤ g :=
  not_le_of_gt (hg.trans_le (priorSlack_le_terminalGap p n))

/-- Conditional uniformity on positive initial-record cells removes the prior correction. -/
theorem priorSlack_zero_of_uniform [Nonempty Z] (p : ConditionalProtocol H0 Z A Y)
    (hu : ∀ u, 0 < p.initialRecord.mass u →
      (p.given u).prior.mass = uniformMass Z) : priorSlack p = 0 := by
  have hp : priorEntropy p = terminalEnvelope Z := by
    unfold priorEntropy
    calc
      (∑ u, p.initialRecord.mass u * entropy (p.given u).prior.mass) =
          ∑ u, p.initialRecord.mass u * terminalEnvelope Z := by
        apply Finset.sum_congr rfl
        intro u _
        rcases (p.initialRecord.nonnegative u).eq_or_lt with hm | hm
        · simp only [← hm, zero_mul]
        · rw [hu u hm, entropy_eq_HBits, HBits_uniformMass_eq_logb_card]
          rfl
      _ = terminalEnvelope Z := by
        rw [← Finset.sum_mul, p.initialRecord.total, one_mul]
  exact sub_eq_zero.mpr hp.symm

/-- Equality in the finite entropy envelope characterizes the uniform source law. -/
theorem entropy_eq_envelope_iff_uniform [Nonempty Z] (q : FiniteLaw Z) :
    entropy q.mass = terminalEnvelope Z ↔ q.mass = uniformMass Z := by
  constructor
  · intro he
    let n : ℝ := Fintype.card Z
    let w : Z → ℝ := fun _ => 1 / n
    have hn : 0 < n := card_cast_pos Z
    have hw0 : ∀ z ∈ (Finset.univ : Finset Z), 0 < w z := by
      intro z _
      exact one_div_pos.mpr hn
    have hw1 : ∑ z ∈ (Finset.univ : Finset Z), w z = 1 := by
      simp [w, n, hn.ne']
    have hmem : ∀ z ∈ (Finset.univ : Finset Z), q.mass z ∈ Set.Ici (0 : ℝ) := by
      intro z _
      exact q.nonnegative z
    have havg : (∑ z : Z, w z * q.mass z) = 1 / n := by
      simp only [w]
      rw [← Finset.mul_sum, q.total, mul_one]
    have hH : H q.mass = Real.log n := by
      rw [entropy_eq_HBits] at he
      change H q.mass / Real.log 2 = Real.log n / Real.log 2 at he
      have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
      exact le_antisymm ((div_le_div_iff_of_pos_right hlog).mp he.le)
        ((div_le_div_iff_of_pos_right hlog).mp he.ge)
    have hsum : (∑ z : Z, w z * Real.negMulLog (q.mass z)) = (1 / n) * H q.mass := by
      simp only [w, H, Finset.mul_sum]
    have hscalar : Real.negMulLog (1 / n) = (1 / n) * Real.log n := by
      rw [Real.negMulLog_def]
      change -(1 / n) * Real.log (1 / n) = (1 / n) * Real.log n
      have hlog : Real.log (1 / n) = - Real.log n := by
        rw [one_div, Real.log_inv]
      rw [hlog]
      ring
    have hj : Real.negMulLog (∑ z : Z, w z • q.mass z) =
        ∑ z : Z, w z • Real.negMulLog (q.mass z) := by
      simp only [smul_eq_mul]
      rw [havg, hsum, hH]
      exact hscalar
    have hu := (Real.strictConcaveOn_negMulLog.map_sum_eq_iff
      (t := (Finset.univ : Finset Z)) (w := w) (p := q.mass) hw0 hw1 hmem).mp hj
    funext z
    have hz := hu z (Finset.mem_univ z)
    simpa only [smul_eq_mul, havg, uniformMass, n] using hz
  · intro hu
    rw [hu, entropy_eq_HBits, HBits_uniformMass_eq_logb_card]
    rfl

/-- Prior slack is the weighted sum of the conditional finite-envelope deficits. -/
theorem priorSlack_eq_weighted_deficits (p : ConditionalProtocol H0 Z A Y) :
    priorSlack p = ∑ u, p.initialRecord.mass u *
      (terminalEnvelope Z - entropy (p.given u).prior.mass) := by
  unfold priorSlack priorEntropy
  calc
    terminalEnvelope Z - (∑ u, p.initialRecord.mass u * entropy (p.given u).prior.mass) =
        (∑ u, p.initialRecord.mass u) * terminalEnvelope Z -
          (∑ u, p.initialRecord.mass u * entropy (p.given u).prior.mass) := by
      rw [p.initialRecord.total, one_mul]
    _ = _ := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro u _
      ring

/-- Prior slack vanishes precisely for uniform conditional priors on positive record cells. -/
theorem priorSlack_zero_iff_uniform [Nonempty Z] (p : ConditionalProtocol H0 Z A Y) :
    priorSlack p = 0 ↔ ∀ u, 0 < p.initialRecord.mass u →
      (p.given u).prior.mass = uniformMass Z := by
  constructor
  · intro hz u hu
    have hcell (v : H0) : 0 ≤ terminalEnvelope Z - entropy (p.given v).prior.mass := by
      apply sub_nonneg.mpr
      rw [entropy_eq_HBits]
      exact HBits_le_logb_card (p.given v).prior.mass
        (p.given v).prior.nonnegative (p.given v).prior.total
    have hle : p.initialRecord.mass u *
        (terminalEnvelope Z - entropy (p.given u).prior.mass) ≤ 0 := by
      calc
        p.initialRecord.mass u * (terminalEnvelope Z - entropy (p.given u).prior.mass) ≤
            ∑ v, p.initialRecord.mass v *
              (terminalEnvelope Z - entropy (p.given v).prior.mass) :=
          Finset.single_le_sum
            (fun v _ => mul_nonneg (p.initialRecord.nonnegative v) (hcell v))
            (Finset.mem_univ u)
        _ = 0 := by rw [← priorSlack_eq_weighted_deficits p, hz]
    have hprod : p.initialRecord.mass u *
        (terminalEnvelope Z - entropy (p.given u).prior.mass) = 0 :=
      le_antisymm hle (mul_nonneg hu.le (hcell u))
    have hzero : terminalEnvelope Z - entropy (p.given u).prior.mass = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hu.ne'
    exact (entropy_eq_envelope_iff_uniform (p.given u).prior).mp
      (sub_eq_zero.mp hzero).symm
  · exact priorSlack_zero_of_uniform p

/-- The law-derived capacity bound becomes a lower bound for the terminal gap. -/
theorem terminalGap_lower_of_localCapacity (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (κ : ℝ)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ) :
    terminalEnvelope Z - κ * conditionalExpectedCost p n (historyBank A Y n) ≤
      terminalGap p n := by
  unfold terminalGap
  apply sub_le_sub_left
  rw [conditionalJointInfo_eq_conditionalMI p n _ (historyBank_complete A Y n)]
  exact conditionalMI_le_expectedCost p n _ (historyBank_complete A Y n) κ hc

/-- A gap threshold charges the positive part of the missing envelope to actual reading cost. -/
theorem cost_lower_of_terminalGap_le (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (κ g : ℝ) (hk : 0 < κ)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ)
    (hg : terminalGap p n ≤ g) :
    max (terminalEnvelope Z - g) 0 / κ ≤
      conditionalExpectedCost p n (historyBank A Y n) := by
  have hb := terminalGap_lower_of_localCapacity p n κ hc
  have hcost := conditionalExpectedCost_nonnegative p n _ (historyBank_complete A Y n)
  apply (div_le_iff₀ hk).mpr
  apply max_le
  · calc
      terminalEnvelope Z - g ≤
          κ * conditionalExpectedCost p n (historyBank A Y n) := by linarith
      _ = conditionalExpectedCost p n (historyBank A Y n) * κ := mul_comm _ _
  · exact mul_nonneg hcost hk.le

/-- A zero local capacity preserves the whole finite terminal envelope. -/
theorem terminalGap_zero_capacity (p : ConditionalProtocol H0 Z A Y) (n : ℕ)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) 0) :
    terminalGap p n = terminalEnvelope Z := by
  rw [terminalGap, conditionalJointInfo_zero_capacity p n _
    (historyBank_complete A Y n) hc, sub_zero]

/-! ## Retained horizons

The accumulated difference between allowed information and acquired information
is a sum of nonnegative local charges. Its monotonicity supplies the incremental
bound without an additional information-balance premise.
-/

/-- Local capacity leaves a nonnegative accumulated slack at every added history. -/
theorem protocolCapacitySlack_mono (p : FiniteProtocol Z A Y) (κ : ℝ)
    (hc : LocalCapacityBound p κ) :
    Monotone (fun n => κ * expectedCost p n (historyBank A Y n) -
      terminalMI p n (historyBank A Y n)) := by
  let f : List (A × Y) → ℝ := fun h =>
    if p.stop h = false then
      κ * (historyMass p h * ∑ a, (p.policy h).mass a * p.cost h a) -
        historyMass p h * ∑ a, (p.policy h).mass a * localGain p h a
    else 0
  have hf (h : List (A × Y)) : 0 ≤ f h := by
    dsimp only [f]
    split_ifs with hs
    · exact sub_nonneg.mpr (weightedGain_le_cost p κ hc h hs)
    · exact le_rfl
  have heq (n : ℕ) :
      κ * expectedCost p n (historyBank A Y n) -
          terminalMI p n (historyBank A Y n) =
        ∑ h ∈ historySet (A × Y) n, activeValue p.stop n f h := by
    rw [terminalMI_eq_gain_sum p n _ (historyBank_complete A Y n), expectedCost]
    simp only [(historyBank_complete A Y n).sum_eq]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : h.length < n ∧ p.stop h = false
    · simp only [if_pos hh, activeValue, f, if_pos hh.2]
    · simp only [if_neg hh, activeValue, mul_zero, sub_self]
  intro n m hnm
  change κ * expectedCost p n (historyBank A Y n) - terminalMI p n (historyBank A Y n) ≤
    κ * expectedCost p m (historyBank A Y m) - terminalMI p m (historyBank A Y m)
  rw [heq n, heq m]
  exact historySet_active_sum_mono p.stop f hf hnm

/-- Additional retained information is bounded by the cost of the added histories. -/
theorem protocolInformation_increase_le_costIncrease (p : FiniteProtocol Z A Y)
    (κ : ℝ) (hc : LocalCapacityBound p κ) (n m : ℕ) (hnm : n ≤ m) :
    terminalMI p m (historyBank A Y m) - terminalMI p n (historyBank A Y n) ≤
      κ * (expectedCost p m (historyBank A Y m) -
        expectedCost p n (historyBank A Y n)) := by
  have hs := protocolCapacitySlack_mono p κ hc hnm
  dsimp only at hs
  -- Rearrangement of the accumulated-slack inequality gives the cost difference.
  linarith only [hs]

/-- Retaining a longer transcript increases the information after the initial record. -/
theorem conditionalInformation_mono (p : ConditionalProtocol H0 Z A Y) :
    Monotone (fun n => conditionalJointInfo p n (historyBank A Y n)) := by
  intro n m hnm
  change conditionalJointInfo p n (historyBank A Y n) ≤
    conditionalJointInfo p m (historyBank A Y m)
  rw [conditionalJointInfo_eq_conditionalMI p n _ (historyBank_complete A Y n),
    conditionalJointInfo_eq_conditionalMI p m _ (historyBank_complete A Y m)]
  unfold conditionalMI
  exact Finset.sum_le_sum (fun u _ =>
    mul_le_mul_of_nonneg_left (terminalMI_mono (p.given u) hnm)
      (p.initialRecord.nonnegative u))

/-- The initial-record law preserves the monotonicity of actual paid cost. -/
theorem conditionalCost_mono (p : ConditionalProtocol H0 Z A Y) :
    Monotone (fun n => conditionalExpectedCost p n (historyBank A Y n)) := by
  intro n m hnm
  unfold conditionalExpectedCost
  exact Finset.sum_le_sum (fun u _ =>
    mul_le_mul_of_nonneg_left (expectedCost_mono (p.given u) hnm)
      (p.initialRecord.nonnegative u))

/-- Conditional continuation is charged only for the histories added after the earlier horizon. -/
theorem conditionalInformation_increase_le_costIncrease
    (p : ConditionalProtocol H0 Z A Y) (κ : ℝ)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ)
    (n m : ℕ) (hnm : n ≤ m) :
    conditionalJointInfo p m (historyBank A Y m) -
        conditionalJointInfo p n (historyBank A Y n) ≤
      κ * (conditionalExpectedCost p m (historyBank A Y m) -
        conditionalExpectedCost p n (historyBank A Y n)) := by
  calc
    conditionalJointInfo p m (historyBank A Y m) -
        conditionalJointInfo p n (historyBank A Y n) =
      ∑ u, p.initialRecord.mass u *
        (terminalMI (p.given u) m (historyBank A Y m) -
          terminalMI (p.given u) n (historyBank A Y n)) := by
      rw [conditionalJointInfo_eq_conditionalMI p m _ (historyBank_complete A Y m),
        conditionalJointInfo_eq_conditionalMI p n _ (historyBank_complete A Y n)]
      simp only [conditionalMI, mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ u, p.initialRecord.mass u *
        (κ * (expectedCost (p.given u) m (historyBank A Y m) -
          expectedCost (p.given u) n (historyBank A Y n))) := by
      apply Finset.sum_le_sum
      intro u _
      rcases (p.initialRecord.nonnegative u).eq_or_lt with hu | hu
      · simp only [← hu, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left
          (protocolInformation_increase_le_costIncrease (p.given u) κ (hc u hu)
            n m hnm) hu.le
    _ = κ * (conditionalExpectedCost p m (historyBank A Y m) -
        conditionalExpectedCost p n (historyBank A Y n)) := by
      unfold conditionalExpectedCost
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring

/-- The coupled gap decreases as retained observations accumulate. -/
theorem terminalGap_antitone (p : ConditionalProtocol H0 Z A Y) :
    Antitone (terminalGap p) := by
  intro n m hnm
  exact sub_le_sub_left (conditionalInformation_mono p hnm) (terminalEnvelope Z)

/-- Retained-horizon gap decrease is nonnegative and bounded by additional paid cost. -/
theorem terminalGap_drop_bounds (p : ConditionalProtocol H0 Z A Y) (κ : ℝ)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ)
    (n m : ℕ) (hnm : n ≤ m) :
    0 ≤ terminalGap p n - terminalGap p m ∧
      terminalGap p n - terminalGap p m ≤
        κ * (conditionalExpectedCost p m (historyBank A Y m) -
          conditionalExpectedCost p n (historyBank A Y n)) := by
  refine ⟨sub_nonneg.mpr (terminalGap_antitone p hnm), ?_⟩
  calc
    terminalGap p n - terminalGap p m =
        conditionalJointInfo p m (historyBank A Y m) -
          conditionalJointInfo p n (historyBank A Y n) := by
      unfold terminalGap
      ring
    _ ≤ _ := conditionalInformation_increase_le_costIncrease p κ hc n m hnm

/-- A continuation threshold charges only the additional cost after the retained horizon. -/
theorem continuation_cost_lower_of_terminalGap_le
    (p : ConditionalProtocol H0 Z A Y) (κ g : ℝ) (hk : 0 < κ)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ)
    (n m : ℕ) (hnm : n ≤ m) (hg : terminalGap p m ≤ g) :
    max (terminalGap p n - g) 0 / κ ≤
      conditionalExpectedCost p m (historyBank A Y m) -
        conditionalExpectedCost p n (historyBank A Y n) := by
  have hdrop := (terminalGap_drop_bounds p κ hc n m hnm).2
  have hcost := sub_nonneg.mpr (conditionalCost_mono p hnm)
  apply (div_le_iff₀ hk).mpr
  apply max_le
  · calc
      terminalGap p n - g ≤ terminalGap p n - terminalGap p m :=
        sub_le_sub_left hg _
      _ ≤ κ * (conditionalExpectedCost p m (historyBank A Y m) -
          conditionalExpectedCost p n (historyBank A Y n)) := hdrop
      _ = _ := mul_comm _ _
  · exact mul_nonneg hcost hk.le

/-! ## Limits of the same retained experiments -/

open Filter
open scoped Topology ENNReal

/-- The limit gap uses the source-defined information limit of the same protocol. -/
def terminalGapLimit (p : ConditionalProtocol H0 Z A Y) : ℝ :=
  terminalEnvelope Z - conditionalInformationLimit p

/-- Limiting residual entropy is the conditional prior entropy left after all finite prefixes. -/
def residualEntropyLimit (p : ConditionalProtocol H0 Z A Y) : ℝ :=
  priorEntropy p - conditionalInformationLimit p

/-- The retained finite gaps converge to the source-defined limit gap. -/
theorem terminalGap_tendsto (p : ConditionalProtocol H0 Z A Y) :
    Tendsto (terminalGap p) atTop (𝓝 (terminalGapLimit p)) := by
  exact tendsto_const_nhds.sub (conditionalJointInfo_tendsto p)

/-- The prior correction and residual identity persist at the information limit. -/
theorem terminalGapLimit_eq_priorSlack_add_residual (p : ConditionalProtocol H0 Z A Y) :
    terminalGapLimit p = priorSlack p + residualEntropyLimit p := by
  unfold terminalGapLimit priorSlack residualEntropyLimit
  ring

/-- Source entropy bounds make the limiting residual nonnegative. -/
theorem residualEntropyLimit_nonnegative (p : ConditionalProtocol H0 Z A Y) :
    0 ≤ residualEntropyLimit p := by
  unfold residualEntropyLimit
  apply sub_nonneg.mpr
  rw [priorEntropy_eq_joint_sub]
  exact conditionalInformationLimit_le_initial_entropy p

/-- Stopped residual entropies converge without a finite expected-cost assumption. -/
theorem residualEntropy_tendsto (p : ConditionalProtocol H0 Z A Y) :
    Tendsto (residualEntropy p) atTop (𝓝 (residualEntropyLimit p)) := by
  have heq (n : ℕ) : residualEntropy p n =
      priorEntropy p - conditionalJointInfo p n (historyBank A Y n) := by
    have h := terminalGap_eq_priorSlack_add_residual p n
    unfold terminalGap priorSlack at h
    -- The finite residual identity is rearranged without a new entropy premise.
    linarith only [h]
  change Tendsto (fun n => residualEntropy p n) atTop (𝓝 (residualEntropyLimit p))
  simp_rw [heq]
  exact tendsto_const_nhds.sub (conditionalJointInfo_tendsto p)

/-- The prior correction remains a lower bound after unbounded retained observation. -/
theorem priorSlack_le_terminalGapLimit (p : ConditionalProtocol H0 Z A Y) :
    priorSlack p ≤ terminalGapLimit p := by
  rw [terminalGapLimit_eq_priorSlack_add_residual]
  exact le_add_of_nonneg_right (residualEntropyLimit_nonnegative p)

/-- Every finite gap is above the limit gap. -/
theorem terminalGapLimit_le_terminalGap (p : ConditionalProtocol H0 Z A Y) (n : ℕ) :
    terminalGapLimit p ≤ terminalGap p n := by
  unfold terminalGapLimit terminalGap
  apply sub_le_sub_left
  rw [conditionalJointInfo_eq_conditionalMI p n _ (historyBank_complete A Y n)]
  unfold conditionalMI conditionalInformationLimit
  exact Finset.sum_le_sum (fun u _ =>
    mul_le_mul_of_nonneg_left (terminalMI_le_informationLimit (p.given u) n)
      (p.initialRecord.nonnegative u))

/-- The limiting gap is nonnegative on a nonempty finite target carrier. -/
theorem terminalGapLimit_nonnegative [Nonempty Z] (p : ConditionalProtocol H0 Z A Y) :
    0 ≤ terminalGapLimit p :=
  (priorSlack_nonnegative p).trans (priorSlack_le_terminalGapLimit p)

/-- The same terminal envelope bounds the limiting gap from above. -/
theorem terminalGapLimit_le_envelope (p : ConditionalProtocol H0 Z A Y) :
    terminalGapLimit p ≤ terminalEnvelope Z :=
  sub_le_self _ (conditionalInformationLimit_nonnegative p)

/-- The recovered envelope at the limit is bounded by extended actual reading cost. -/
theorem terminalGapLimit_extendedCost_bound (p : ConditionalProtocol H0 Z A Y)
    (κ : ℝ) (hk : 0 ≤ κ)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ) :
    ENNReal.ofReal (terminalEnvelope Z - terminalGapLimit p) ≤
      ENNReal.ofReal κ * conditionalExtendedCost p := by
  simpa only [terminalGapLimit, sub_sub_cancel] using
    conditionalInformationLimit_le_extendedCost p κ hk hc

/-- A limiting gap threshold imposes an extended-cost bound, including infinite cost. -/
theorem extendedCost_bound_of_terminalGapLimit_le
    (p : ConditionalProtocol H0 Z A Y) (κ g : ℝ) (hk : 0 ≤ κ)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ)
    (hg : terminalGapLimit p ≤ g) :
    ENNReal.ofReal (max (terminalEnvelope Z - g) 0) ≤
      ENNReal.ofReal κ * conditionalExtendedCost p := by
  have hinfo : max (terminalEnvelope Z - g) 0 ≤ conditionalInformationLimit p := by
    apply max_le
    · calc
        terminalEnvelope Z - g ≤ terminalEnvelope Z - terminalGapLimit p :=
          sub_le_sub_left hg _
        _ = conditionalInformationLimit p := sub_sub_cancel _ _
    · exact conditionalInformationLimit_nonnegative p
  exact (ENNReal.ofReal_le_ofReal hinfo).trans
    (conditionalInformationLimit_le_extendedCost p κ hk hc)

/-- Every finite budget supporting a limiting gap threshold satisfies the same price bound. -/
theorem budget_lower_of_terminalGapLimit_le
    (p : ConditionalProtocol H0 Z A Y) (κ g budget : ℝ) (hk : 0 < κ)
    (hb : 0 ≤ budget)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ)
    (hcost : conditionalExtendedCost p ≤ ENNReal.ofReal budget)
    (hg : terminalGapLimit p ≤ g) :
    max (terminalEnvelope Z - g) 0 / κ ≤ budget := by
  have hinfo := conditionalInformationLimit_le_budget p κ budget hk.le hb hc hcost
  apply (div_le_iff₀ hk).mpr
  apply max_le
  · calc
      terminalEnvelope Z - g ≤ terminalEnvelope Z - terminalGapLimit p :=
        sub_le_sub_left hg _
      _ = conditionalInformationLimit p := sub_sub_cancel _ _
      _ ≤ κ * budget := hinfo
      _ = budget * κ := mul_comm _ _
  · exact mul_nonneg hb hk.le

/-- A zero-capacity protocol preserves the terminal envelope at the information limit. -/
theorem terminalGapLimit_zero_capacity (p : ConditionalProtocol H0 Z A Y)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) 0) :
    terminalGapLimit p = terminalEnvelope Z := by
  rw [terminalGapLimit, conditionalInformationLimit_zero_capacity p hc, sub_zero]

end

end OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
