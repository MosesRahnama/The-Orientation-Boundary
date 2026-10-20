import OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
import OperatorKO7.Meta.BoundaryObserver.TranscriptLaw
import OperatorKO7.Meta.BoundaryObserver.InstrumentDivision
import OperatorKO7.Meta.BoundaryObserver.PairResolution

/-!
# Explicit uniform relative entropy and source controls

The logarithmic divergence is defined independently of the entropy deficit.
The controls retain the actual initial joint law and finite-protocol histories.
Relation: normalized finite probability laws and retained observation protocols.
Property: relative-entropy identity and nonvacuous cost witnesses.
External trust: none.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open scoped BigOperators

noncomputable section

variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

/-- Uniform relative entropy in bits is the explicit probability-weighted logarithmic sum. -/
def uniformRelativeEntropy (q : FiniteLaw Z) : ℝ :=
  (∑ z, q.mass z * Real.log (q.mass z / uniformMass Z z)) / Real.log 2

/-- The explicit relative-entropy sum equals the entropy deficit on the same finite carrier. -/
theorem uniformRelativeEntropy_eq_envelope_sub_entropy [Nonempty Z] (q : FiniteLaw Z) :
    uniformRelativeEntropy q = terminalEnvelope Z - entropy q.mass := by
  have hcell (z : Z) : q.mass z * Real.log (q.mass z / uniformMass Z z) =
      -Real.negMulLog (q.mass z) + q.mass z * Real.log (Fintype.card Z : ℝ) := by
    by_cases hz : q.mass z = 0
    · simp only [hz, zero_mul, Real.negMulLog_zero, neg_zero, zero_add]
    · have hu : uniformMass Z z ≠ 0 := (one_div_pos.mpr (card_cast_pos Z)).ne'
      rw [Real.log_div hz hu]
      simp only [uniformMass, one_div, Real.log_inv, Real.negMulLog_def]
      ring
  have hsum : (∑ z, q.mass z * Real.log (q.mass z / uniformMass Z z)) =
      Real.log (Fintype.card Z : ℝ) - H q.mass := by
    simp only [hcell, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [← Finset.sum_mul, q.total, one_mul]
    unfold H
    ring
  unfold uniformRelativeEntropy
  rw [hsum, entropy_eq_HBits]
  unfold terminalEnvelope HBits
  ring

/-- Uniform relative entropy is nonnegative for every normalized source law. -/
theorem uniformRelativeEntropy_nonnegative [Nonempty Z] (q : FiniteLaw Z) :
    0 ≤ uniformRelativeEntropy q := by
  rw [uniformRelativeEntropy_eq_envelope_sub_entropy]
  apply sub_nonneg.mpr
  rw [entropy_eq_HBits]
  exact HBits_le_logb_card q.mass q.nonnegative q.total

/-- Vanishing uniform relative entropy characterizes the uniform source law. -/
theorem uniformRelativeEntropy_eq_zero_iff_uniform [Nonempty Z] (q : FiniteLaw Z) :
    uniformRelativeEntropy q = 0 ↔ q.mass = uniformMass Z := by
  rw [uniformRelativeEntropy_eq_envelope_sub_entropy]
  constructor
  · intro h
    exact (entropy_eq_envelope_iff_uniform q).mp (sub_eq_zero.mp h).symm
  · intro h
    exact sub_eq_zero.mpr ((entropy_eq_envelope_iff_uniform q).mpr h).symm

/-- The actual initial-record law weights the explicit conditional divergences. -/
theorem priorSlack_eq_weighted_uniformRelativeEntropy [Nonempty Z]
    (p : ConditionalProtocol H0 Z A Y) :
    priorSlack p = ∑ u, p.initialRecord.mass u * uniformRelativeEntropy (p.given u).prior := by
  rw [priorSlack_eq_weighted_deficits]
  apply Finset.sum_congr rfl
  intro u _
  rw [uniformRelativeEntropy_eq_envelope_sub_entropy]

/-- The stopped gap splits into explicit prior divergence and actual residual entropy. -/
theorem terminalGap_eq_weighted_uniformRelativeEntropy_add_residual [Nonempty Z]
    (p : ConditionalProtocol H0 Z A Y) (n : ℕ) :
    terminalGap p n =
      (∑ u, p.initialRecord.mass u * uniformRelativeEntropy (p.given u).prior) +
        residualEntropy p n := by
  rw [terminalGap_eq_priorSlack_add_residual, priorSlack_eq_weighted_uniformRelativeEntropy]

/-- Zero gap requires both conditional prior uniformity and zero actual stopped residual entropy. -/
theorem terminalGap_zero_iff_uniform_and_zero_residual [Nonempty Z]
    (p : ConditionalProtocol H0 Z A Y) (n : ℕ) :
    terminalGap p n = 0 ↔
      (∀ u, 0 < p.initialRecord.mass u → (p.given u).prior.mass = uniformMass Z) ∧
        residualEntropy p n = 0 := by
  constructor
  · intro hg
    have hs : priorSlack p = 0 :=
      le_antisymm ((priorSlack_le_terminalGap p n).trans hg.le) (priorSlack_nonnegative p)
    have hr : residualEntropy p n = 0 := by
      have h := terminalGap_eq_priorSlack_add_residual p n
      rw [hg, hs, zero_add] at h
      exact h.symm
    exact ⟨(priorSlack_zero_iff_uniform p).mp hs, hr⟩
  · rintro ⟨hu, hr⟩
    rw [terminalGap_eq_priorSlack_add_residual, (priorSlack_zero_iff_uniform p).mpr hu,
      hr, add_zero]

/-! ## Concrete conditional source laws and finite reading controls -/

/-- A constant initial record retains the original protocol and its normalized target law. -/
def unitRecordProtocol (p : FiniteProtocol Z A Y) : ConditionalProtocol Unit Z A Y where
  initialRecord := unitLaw
  initialJoint := {
    mass := fun uz => p.prior.mass uz.2
    nonnegative := fun uz => p.prior.nonnegative uz.2
    total := by
      rw [Fintype.sum_prod_type]
      simpa only [Fintype.sum_unique] using p.prior.total }
  given _ := p
  initial_joint := by
    intro u z
    change p.prior.mass z = 1 * p.prior.mass z
    exact (one_mul _).symm

/-- A constant initial record preserves the information computed from the stopped law. -/
theorem unitRecordProtocol_information (p : FiniteProtocol Z A Y) (n : ℕ) :
    conditionalJointInfo (unitRecordProtocol p) n (historyBank A Y n) =
      terminalMI p n (historyBank A Y n) := by
  rw [conditionalJointInfo_eq_conditionalMI _ n _ (historyBank_complete A Y n)]
  simp [conditionalMI, unitRecordProtocol, unitLaw]

/-- A constant initial record preserves the actual expected reading cost. -/
theorem unitRecordProtocol_cost (p : FiniteProtocol Z A Y) (n : ℕ) :
    conditionalExpectedCost (unitRecordProtocol p) n (historyBank A Y n) =
      expectedCost p n (historyBank A Y n) := by
  simp [conditionalExpectedCost, unitRecordProtocol, unitLaw]

/-- The empty retained history has unit mass under every normalized protocol prior. -/
theorem historyMass_nil_eq_one (p : FiniteProtocol Z A Y) : historyMass p [] = 1 := by
  unfold historyMass
  simp only [prefixMass_nil]
  exact p.prior.total

/-- Only the empty history can carry an active charge before horizon one. -/
theorem historySet_active_one {E : Type} [Fintype E]
    (stop : List E → Bool) (f : List E → ℝ) :
    (∑ h ∈ historySet E 1, activeValue stop 1 f h) =
      if stop [] = false then f [] else 0 := by
  classical
  have hz : ([] : List E) ∈ historySet E 1 := (mem_historySet 1 []).mpr (by simp)
  calc
    (∑ h ∈ historySet E 1, activeValue stop 1 f h) = activeValue stop 1 f [] := by
      apply Finset.sum_eq_single []
      · intro h _ hne
        have hlen : ¬ h.length < 1 := by
          intro hh
          exact hne (List.length_eq_zero_iff.mp
            (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hh)))
        simp only [activeValue, hlen, false_and, if_false]
      · intro hnot
        exact False.elim (hnot hz)
    _ = _ := by simp [activeValue]

/-- At horizon one the finite information is the initial active reading gain. -/
theorem terminalMI_horizon_one (p : FiniteProtocol Z A Y) :
    terminalMI p 1 (historyBank A Y 1) =
      if p.stop [] = false then ∑ a, (p.policy []).mass a * localGain p [] a else 0 := by
  rw [terminalMI_eq_gain_sum p 1 _ (historyBank_complete A Y 1),
    (historyBank_complete A Y 1).sum_eq]
  change (∑ h ∈ historySet (A × Y) 1, activeValue p.stop 1
    (fun h => historyMass p h * ∑ a, (p.policy h).mass a * localGain p h a) h) = _
  rw [historySet_active_one, historyMass_nil_eq_one]
  simp only [one_mul]

/-- At horizon one the finite cost is the initial active reading charge. -/
theorem expectedCost_horizon_one (p : FiniteProtocol Z A Y) :
    expectedCost p 1 (historyBank A Y 1) =
      if p.stop [] = false then ∑ a, (p.policy []).mass a * p.cost [] a else 0 := by
  unfold expectedCost
  rw [(historyBank_complete A Y 1).sum_eq]
  change (∑ h ∈ historySet (A × Y) 1, activeValue p.stop 1
    (fun h => historyMass p h * ∑ a, (p.policy h).mass a * p.cost h a) h) = _
  rw [historySet_active_one, historyMass_nil_eq_one]
  simp only [one_mul]

/-- The binary target carrier has a one-bit terminal envelope. -/
theorem terminalEnvelope_bool : terminalEnvelope Bool = 1 := by
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
  norm_num [terminalEnvelope, hlog]

/-- A fair binary source is read through the specified signed-bias channel at unit price. -/
def binaryReadingProtocol (δ : ℝ) (hδ : |δ| ≤ 1 / 2) : FiniteProtocol Bool Unit Bool where
  prior := binaryPriorLaw (1 / 2) (by norm_num) (by norm_num)
  policy _ := unitLaw
  observation _ _ z := binaryKernelLaw δ hδ z
  stop _ := false
  cost _ _ := 1
  cost_nonnegative _ _ := zero_le_one

/-- The concrete reading family satisfies the source and price fields of the binary menu. -/
def binaryReadingMenu (δ : ℝ) (hδ : |δ| ≤ 1 / 2) :
    BinaryMenu (binaryReadingProtocol δ hδ) |δ| where
  bias _ _ := δ
  bound _ _ := le_rfl
  source _ _ _ _ := rfl
  reading_cost _ _ := le_rfl

/-- The binary reading has a constant retained initial record and its actual target prior. -/
def binaryReadingConditional (δ : ℝ) (hδ : |δ| ≤ 1 / 2) :
    ConditionalProtocol Unit Bool Unit Bool :=
  unitRecordProtocol (binaryReadingProtocol δ hδ)

/-- The concrete binary prior is uniform on the target carrier. -/
theorem binaryReading_prior_uniform (δ : ℝ) (hδ : |δ| ≤ 1 / 2) :
    (binaryReadingProtocol δ hδ).prior.mass = uniformMass Bool := by
  funext b
  cases b <;> norm_num [binaryReadingProtocol, binaryPriorLaw, binaryPrior, uniformMass]

/-- The concrete fair source has zero prior slack. -/
theorem binaryReading_slack_zero (δ : ℝ) (hδ : |δ| ≤ 1 / 2) :
    priorSlack (binaryReadingConditional δ hδ) = 0 := by
  apply priorSlack_zero_of_uniform
  intro u _
  exact binaryReading_prior_uniform δ hδ

/-- The initial reading has positive history and action masses and an active unit charge. -/
theorem binaryReading_initial_active (δ : ℝ) (hδ : |δ| ≤ 1 / 2) :
    0 < historyMass (binaryReadingProtocol δ hδ) [] ∧
      (binaryReadingProtocol δ hδ).stop [] = false ∧
      0 < ((binaryReadingProtocol δ hδ).policy []).mass () ∧
      (binaryReadingProtocol δ hδ).cost [] () = 1 := by
  refine ⟨?_, rfl, zero_lt_one, rfl⟩
  rw [historyMass_nil_eq_one]
  exact zero_lt_one

/-- Every concrete binary channel pays one unit by horizon one. -/
theorem binaryReading_cost_one (δ : ℝ) (hδ : |δ| ≤ 1 / 2) :
    conditionalExpectedCost (binaryReadingConditional δ hδ) 1 (historyBank Unit Bool 1) = 1 := by
  rw [binaryReadingConditional, unitRecordProtocol_cost, expectedCost_horizon_one]
  simp [binaryReadingProtocol, unitLaw]

/-- The first retained reading has the information of its actual binary joint law. -/
theorem binaryReading_information_one (δ : ℝ) (hδ : |δ| ≤ 1 / 2) :
    conditionalJointInfo (binaryReadingConditional δ hδ) 1 (historyBank Unit Bool 1) =
      jointMI (binaryJoint (1 / 2) δ) := by
  rw [binaryReadingConditional, unitRecordProtocol_information, terminalMI_horizon_one]
  have hs : (binaryReadingProtocol δ hδ).stop [] = false := rfl
  rw [if_pos hs, Fintype.sum_unique]
  change 1 * localGain (binaryReadingProtocol δ hδ) [] () = _
  rw [one_mul]
  have hw : 0 < historyMass (binaryReadingProtocol δ hδ) [] := by
    rw [historyMass_nil_eq_one]
    exact zero_lt_one
  have hp : posterior (binaryReadingProtocol δ hδ) [] true = 1 / 2 := by
    rw [posterior, prefixMass_nil, historyMass_nil_eq_one, div_one]
    rfl
  rw [binaryMenu_localGain _ |δ| (binaryReadingMenu δ hδ) [] () hw, hp]
  rfl

/-- The zero-signal control performs paid active readings whose outcome is independent of the target. -/
def zeroSignalConditional : ConditionalProtocol Unit Bool Unit Bool :=
  binaryReadingConditional 0 (by norm_num)

/-- The zero-signal control satisfies zero local capacity at every positive conditional history. -/
theorem zeroSignalConditional_capacity :
    ∀ u, 0 < zeroSignalConditional.initialRecord.mass u →
      LocalCapacityBound (zeroSignalConditional.given u) 0 := by
  intro u _
  change LocalCapacityBound (binaryReadingProtocol 0 (by norm_num)) 0
  have h := binaryMenu_capacity (binaryReadingProtocol 0 (by norm_num)) |(0 : ℝ)|
    (binaryReadingMenu 0 (by norm_num)) (by norm_num)
  simpa using h

/-- Every finite retained horizon of the zero-signal control has gap one. -/
theorem zeroSignalConditional_gap (n : ℕ) : terminalGap zeroSignalConditional n = 1 := by
  rw [terminalGap_zero_capacity _ n zeroSignalConditional_capacity, terminalEnvelope_bool]

/-- The active zero-capacity control has positive premise masses, paid cost, and full residual gap. -/
theorem zeroSignalConditional_control :
    LocalCapacityBound (zeroSignalConditional.given ()) 0 ∧
      0 < historyMass (zeroSignalConditional.given ()) [] ∧
      (zeroSignalConditional.given ()).stop [] = false ∧
      0 < ((zeroSignalConditional.given ()).policy []).mass () ∧
      conditionalExpectedCost zeroSignalConditional 1 (historyBank Unit Bool 1) = 1 ∧
      priorSlack zeroSignalConditional = 0 ∧
      terminalGap zeroSignalConditional 1 = 1 ∧
      residualEntropy zeroSignalConditional 1 = 1 := by
  have hc := zeroSignalConditional_capacity () zero_lt_one
  have ha := binaryReading_initial_active 0 (by norm_num)
  have hcost : conditionalExpectedCost zeroSignalConditional 1 (historyBank Unit Bool 1) = 1 :=
    binaryReading_cost_one 0 (by norm_num)
  have hs : priorSlack zeroSignalConditional = 0 := binaryReading_slack_zero 0 (by norm_num)
  have hg := zeroSignalConditional_gap 1
  have hr : residualEntropy zeroSignalConditional 1 = 1 := by
    have h := terminalGap_eq_priorSlack_add_residual zeroSignalConditional 1
    rw [hg, hs, zero_add] at h
    exact h.symm
  exact ⟨hc, ha.1, ha.2.1, ha.2.2.1, hcost, hs, hg, hr⟩

/-- The perfect-reading control reveals the fair target through the noiseless binary channel. -/
def perfectReadingConditional : ConditionalProtocol Unit Bool Unit Bool :=
  binaryReadingConditional (1 / 2) (by norm_num [abs_le])

/-- The perfect-reading control satisfies unit local information capacity. -/
theorem perfectReadingConditional_capacity :
    ∀ u, 0 < perfectReadingConditional.initialRecord.mass u →
      LocalCapacityBound (perfectReadingConditional.given u) 1 := by
  intro u _
  change LocalCapacityBound (binaryReadingProtocol (1 / 2) (by norm_num [abs_le])) 1
  have h := binaryMenu_capacity (binaryReadingProtocol (1 / 2) (by norm_num [abs_le])) |(1 / 2 : ℝ)|
    (binaryReadingMenu (1 / 2) (by norm_num [abs_le])) (by norm_num [abs_le])
  norm_num at h
  exact h

/-- One perfect retained reading acquires one bit from the actual joint law. -/
theorem perfectReadingConditional_information_one :
    conditionalJointInfo perfectReadingConditional 1 (historyBank Unit Bool 1) = 1 := by
  rw [perfectReadingConditional, binaryReading_information_one,
    binaryJoint_information_positive_endpoint]
  have hh : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
    simpa only [one_div] using Real.binEntropy_two_inv
  rw [hh, div_self (Real.log_pos one_lt_two).ne']

/-- One perfect retained reading reaches gap zero. -/
theorem perfectReadingConditional_gap_one : terminalGap perfectReadingConditional 1 = 0 := by
  rw [terminalGap, perfectReadingConditional_information_one, terminalEnvelope_bool, sub_self]

/-- A concrete positive-capacity protocol attains the one-unit price of a zero-gap threshold. -/
theorem perfectReadingConditional_control :
    LocalCapacityBound (perfectReadingConditional.given ()) 1 ∧
      conditionalJointInfo perfectReadingConditional 1 (historyBank Unit Bool 1) = 1 ∧
      conditionalExpectedCost perfectReadingConditional 1 (historyBank Unit Bool 1) = 1 ∧
      priorSlack perfectReadingConditional = 0 ∧
      terminalGap perfectReadingConditional 1 = 0 ∧
      residualEntropy perfectReadingConditional 1 = 0 ∧
      1 ≤ conditionalExpectedCost perfectReadingConditional 1 (historyBank Unit Bool 1) := by
  have hc := perfectReadingConditional_capacity () zero_lt_one
  have hi := perfectReadingConditional_information_one
  have hcost : conditionalExpectedCost perfectReadingConditional 1 (historyBank Unit Bool 1) = 1 :=
    binaryReading_cost_one (1 / 2) (by norm_num [abs_le])
  have hs : priorSlack perfectReadingConditional = 0 :=
    binaryReading_slack_zero (1 / 2) (by norm_num [abs_le])
  have hg := perfectReadingConditional_gap_one
  have hr : residualEntropy perfectReadingConditional 1 = 0 := by
    have h := terminalGap_eq_priorSlack_add_residual perfectReadingConditional 1
    rw [hg, hs, zero_add] at h
    exact h.symm
  have hprice := cost_lower_of_terminalGap_le perfectReadingConditional 1 1 0
    (by norm_num) perfectReadingConditional_capacity hg.le
  have hprice' : 1 ≤ conditionalExpectedCost perfectReadingConditional 1
      (historyBank Unit Bool 1) := by
    simpa [terminalEnvelope_bool] using hprice
  exact ⟨hc, hi, hcost, hs, hg, hr, hprice'⟩

/-- A biased binary source supplies a normalized nonuniform law with full target support. -/
def biasedBinaryPrior : FiniteLaw Bool :=
  binaryPriorLaw (1 / 4) (by norm_num) (by norm_num)

/-- The biased prior has positive explicit divergence and the same one-bit envelope. -/
theorem biasedBinaryPrior_control :
    (∀ z, 0 < biasedBinaryPrior.mass z) ∧
      0 < uniformRelativeEntropy biasedBinaryPrior ∧
      uniformRelativeEntropy biasedBinaryPrior = 1 - entropy biasedBinaryPrior.mass := by
  have hu : biasedBinaryPrior.mass ≠ uniformMass Bool := by
    intro h
    have ht := congrFun h true
    norm_num [biasedBinaryPrior, binaryPriorLaw, binaryPrior, uniformMass] at ht
  have hn := uniformRelativeEntropy_nonnegative biasedBinaryPrior
  have hne : uniformRelativeEntropy biasedBinaryPrior ≠ 0 :=
    fun h => hu ((uniformRelativeEntropy_eq_zero_iff_uniform biasedBinaryPrior).mp h)
  have hp : 0 < uniformRelativeEntropy biasedBinaryPrior := by
    rcases hn.eq_or_lt with h | h
    · exact False.elim (hne h.symm)
    · exact h
  refine ⟨?_, hp, ?_⟩
  · intro z
    cases z <;> norm_num [biasedBinaryPrior, binaryPriorLaw, binaryPrior]
  · rw [uniformRelativeEntropy_eq_envelope_sub_entropy, terminalEnvelope_bool]

/-! ## Finite budgets for actual decreases

Nonnegative antitone
deficits bound every finite collection of drops; positive payment floors
therefore permit only finitely many paid events.
-/

/-- The decrease between consecutive observations of one deficit. -/
def deficitDrop (d : ℕ → ℝ) (n : ℕ) : ℝ := d n - d (n + 1)

theorem deficitDrop_nonnegative (d : ℕ → ℝ) (hd : Antitone d) (n : ℕ) :
    0 ≤ deficitDrop d n :=
  sub_nonneg.mpr (hd (Nat.le_succ n))

/-- The actual drops telescope without an asymptotic assumption. -/
theorem deficitDrop_sum_range (d : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, deficitDrop d n = d 0 - d N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      unfold deficitDrop
      ring

/-- Every finite collection of drops fits inside the same initial budget. -/
theorem deficitDrop_sum_le_initial (d : ℕ → ℝ) (h0 : ∀ n, 0 ≤ d n)
    (hd : Antitone d) (A : Finset ℕ) :
    ∑ n ∈ A, deficitDrop d n ≤ d 0 := by
  have hsub : A ⊆ Finset.range (A.sup id + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => deficitDrop_nonnegative d hd n)
  rw [deficitDrop_sum_range] at hs
  exact hs.trans (sub_le_self _ (h0 _))

/-- Nonnegative antitone deficits have a summable sequence of decreases. -/
theorem deficitDrop_summable (d : ℕ → ℝ) (h0 : ∀ n, 0 ≤ d n)
    (hd : Antitone d) : Summable (deficitDrop d) :=
  summable_of_sum_le (deficitDrop_nonnegative d hd)
    (deficitDrop_sum_le_initial d h0 hd)

theorem deficitDrop_tsum_le_initial (d : ℕ → ℝ) (h0 : ∀ n, 0 ≤ d n)
    (hd : Antitone d) : ∑' n, deficitDrop d n ≤ d 0 :=
  (deficitDrop_summable d h0 hd).tsum_le_of_sum_le
    (deficitDrop_sum_le_initial d h0 hd)

/-- A common payment floor bounds the number of selected paid events. -/
theorem paidDrop_card_bound (d : ℕ → ℝ) (h0 : ∀ n, 0 ≤ d n)
    (hd : Antitone d) (c : ℝ) (A : Finset ℕ)
    (paid : ∀ n ∈ A, c ≤ deficitDrop d n) :
    c * (A.card : ℝ) ≤ d 0 := by
  calc
    c * (A.card : ℝ) = ∑ _n ∈ A, c := by simp [nsmul_eq_mul, mul_comm]
    _ ≤ ∑ n ∈ A, deficitDrop d n := Finset.sum_le_sum paid
    _ ≤ d 0 := deficitDrop_sum_le_initial d h0 hd A

theorem paidDrop_card_le_div (d : ℕ → ℝ) (h0 : ∀ n, 0 ≤ d n)
    (hd : Antitone d) (c : ℝ) (hc : 0 < c) (A : Finset ℕ)
    (paid : ∀ n ∈ A, c ≤ deficitDrop d n) :
    (A.card : ℝ) ≤ d 0 / c := by
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm] using paidDrop_card_bound d h0 hd c A paid

/-- Positive payment floors exclude infinitely many such drops. -/
theorem finite_paidDrop_events (d : ℕ → ℝ) (h0 : ∀ n, 0 ≤ d n)
    (hd : Antitone d) (c : ℝ) (hc : 0 < c) :
    Set.Finite {n | c ≤ deficitDrop d n} := by
  have ht := (deficitDrop_summable d h0 hd).tendsto_atTop_zero
  have he : ∀ᶠ n in Filter.atTop, deficitDrop d n < c :=
    (tendsto_order.mp ht).2 c hc
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  apply (Finset.range N).finite_toSet.subset
  intro n hn
  change n ∈ Finset.range N
  apply Finset.mem_range.mpr
  by_contra hnot
  exact (not_lt_of_ge hn) (hN n (Nat.le_of_not_gt hnot))

/-- A deficit that decreases by c exactly N times. -/
def linearDeficit (c : ℝ) (N n : ℕ) : ℝ := c * (N - n : ℕ)

theorem linearDeficit_nonnegative (c : ℝ) (hc : 0 ≤ c) (N n : ℕ) :
    0 ≤ linearDeficit c N n :=
  mul_nonneg hc (Nat.cast_nonneg _)

theorem linearDeficit_antitone (c : ℝ) (hc : 0 ≤ c) (N : ℕ) :
    Antitone (linearDeficit c N) := by
  intro i j hij
  apply mul_le_mul_of_nonneg_left _ hc
  exact_mod_cast Nat.sub_le_sub_left hij N

theorem linearDeficit_drop (c : ℝ) (N n : ℕ) :
    deficitDrop (linearDeficit c N) n = if n < N then c else 0 := by
  by_cases hn : n < N
  · have hs : N - n = (N - (n + 1)) + 1 := by omega
    simp only [if_pos hn, deficitDrop, linearDeficit, hs, Nat.cast_add, Nat.cast_one]
    ring
  · have hN : N ≤ n := Nat.le_of_not_gt hn
    have hNs : N ≤ n + 1 := hN.trans (Nat.le_succ n)
    simp [deficitDrop, linearDeficit, Nat.sub_eq_zero_of_le hN,
      Nat.sub_eq_zero_of_le hNs, hn]

/-- The finite event bound is attained for every horizon and nonnegative charge. -/
theorem linearDeficit_attains_budget (c : ℝ) (N : ℕ) :
    (∀ n ∈ Finset.range N, deficitDrop (linearDeficit c N) n = c) ∧
      c * ((Finset.range N).card : ℝ) = linearDeficit c N 0 ∧
      (∑ n ∈ Finset.range N, deficitDrop (linearDeficit c N) n) =
        linearDeficit c N 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [linearDeficit_drop, if_pos (Finset.mem_range.mp hn)]
  · simp [linearDeficit]
  · rw [deficitDrop_sum_range]
    simp [linearDeficit]

/-- At a zero payment floor even the zero deficit has infinitely many qualifying events. -/
theorem zero_floor_infinitely_many_events :
    Set.Infinite {n : ℕ | (0 : ℝ) ≤ deficitDrop (fun _ => 0) n} := by
  simpa [deficitDrop] using (Set.infinite_univ : Set.Infinite (Set.univ : Set ℕ))

/-- The event budget applies to the actual retained-transcript gap. -/
theorem terminalGap_paid_event_bound [Nonempty Z] (p : ConditionalProtocol H0 Z A Y)
    (c : ℝ) (events : Finset ℕ)
    (paid : ∀ n ∈ events, c ≤ terminalGap p n - terminalGap p (n + 1)) :
    c * (events.card : ℝ) ≤ terminalGap p 0 :=
  paidDrop_card_bound (terminalGap p) (terminalGap_nonnegative p)
    (terminalGap_antitone p) c events paid

theorem terminalGap_finite_paid_events [Nonempty Z] (p : ConditionalProtocol H0 Z A Y)
    (c : ℝ) (hc : 0 < c) :
    Set.Finite {n | c ≤ terminalGap p n - terminalGap p (n + 1)} :=
  finite_paidDrop_events (terminalGap p) (terminalGap_nonnegative p)
    (terminalGap_antitone p) c hc

#check @deficitDrop
#print axioms deficitDrop
#check @deficitDrop_nonnegative
#print axioms deficitDrop_nonnegative
#check @deficitDrop_sum_range
#print axioms deficitDrop_sum_range
#check @deficitDrop_sum_le_initial
#print axioms deficitDrop_sum_le_initial
#check @deficitDrop_summable
#print axioms deficitDrop_summable
#check @deficitDrop_tsum_le_initial
#print axioms deficitDrop_tsum_le_initial
#check @paidDrop_card_bound
#print axioms paidDrop_card_bound
#check @paidDrop_card_le_div
#print axioms paidDrop_card_le_div
#check @finite_paidDrop_events
#print axioms finite_paidDrop_events
#check @linearDeficit
#print axioms linearDeficit
#check @linearDeficit_nonnegative
#print axioms linearDeficit_nonnegative
#check @linearDeficit_antitone
#print axioms linearDeficit_antitone
#check @linearDeficit_drop
#print axioms linearDeficit_drop
#check @linearDeficit_attains_budget
#print axioms linearDeficit_attains_budget
#check @zero_floor_infinitely_many_events
#print axioms zero_floor_infinitely_many_events
#check @terminalGap_paid_event_bound
#print axioms terminalGap_paid_event_bound
#check @terminalGap_finite_paid_events
#print axioms terminalGap_finite_paid_events

end

end OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

namespace OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open scoped BigOperators Classical

noncomputable section

variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

/-- Actual target uncertainty in the source stopped-transcript cells. -/
def conditionalTranscriptResidual (p : ConditionalProtocol H0 Z A Y) : ℝ :=
  ∑ u, p.initialRecord.mass u * TranscriptLaw.transcriptUncertainty (p.given u)

theorem conditionalInformationLimit_eq_prior_sub_transcript [Nonempty Z]
    (p : ConditionalProtocol H0 Z A Y)
    (hstop : TranscriptLaw.PositiveBranchStopping p) :
    conditionalInformationLimit p =
      priorEntropy p - conditionalTranscriptResidual p := by
  unfold conditionalInformationLimit priorEntropy conditionalTranscriptResidual
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : 0 < p.initialRecord.mass u
  · have hs := TranscriptLaw.stops_of_positive_prior (p.given u)
      (fun z hz => hstop u z hu hz)
    rw [TranscriptLaw.informationLimit_eq_transcriptInformation (p.given u) hs]
    unfold TranscriptLaw.transcriptInformation
    ring
  · have hz : p.initialRecord.mass u = 0 :=
      le_antisymm (le_of_not_gt hu) (p.initialRecord.nonnegative u)
    simp [hz]

theorem residualEntropyLimit_eq_transcript [Nonempty Z]
    (p : ConditionalProtocol H0 Z A Y)
    (hstop : TranscriptLaw.PositiveBranchStopping p) :
    residualEntropyLimit p = conditionalTranscriptResidual p := by
  unfold residualEntropyLimit
  rw [conditionalInformationLimit_eq_prior_sub_transcript p hstop]
  ring

theorem terminalGapLimit_eq_slack_add_transcript [Nonempty Z]
    (p : ConditionalProtocol H0 Z A Y)
    (hstop : TranscriptLaw.PositiveBranchStopping p) :
    terminalGapLimit p = priorSlack p + conditionalTranscriptResidual p := by
  unfold terminalGapLimit priorSlack
  rw [conditionalInformationLimit_eq_prior_sub_transcript p hstop]
  ring

/-- The limit uses actual countable joint/product log ratios. -/
theorem terminalGapLimit_eq_countable_logRatio [Nonempty Z]
    (p : ConditionalProtocol H0 Z A Y)
    (hstop : TranscriptLaw.PositiveBranchStopping p) :
    terminalGapLimit p = terminalEnvelope Z -
      TranscriptLaw.conditionalCountableTranscriptInformation p hstop := by
  unfold terminalGapLimit
  rw [TranscriptLaw.conditionalInformationLimit_eq_countable_of_positive p hstop]

#check @conditionalTranscriptResidual
#print axioms conditionalTranscriptResidual
#check @conditionalInformationLimit_eq_prior_sub_transcript
#print axioms conditionalInformationLimit_eq_prior_sub_transcript
#check @residualEntropyLimit_eq_transcript
#print axioms residualEntropyLimit_eq_transcript
#check @terminalGapLimit_eq_slack_add_transcript
#print axioms terminalGapLimit_eq_slack_add_transcript
#check @terminalGapLimit_eq_countable_logRatio
#print axioms terminalGapLimit_eq_countable_logRatio

end

end OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

namespace OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open scoped BigOperators Classical

noncomputable section

variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

section PairedInitialRecord

variable {W E : Type} [Fintype W] [Fintype E]

/-- The actual initial target joint law after retaining only W. -/
def pairedCoarseJoint (p : ConditionalProtocol (W × E) Z A Y) :
    FiniteLaw (W × Z) where
  mass wz := ∑ e, p.initialJoint.mass ((wz.1, e), wz.2)
  nonnegative wz := Finset.sum_nonneg (fun e _ => p.initialJoint.nonnegative _)
  total := by
    calc
      (∑ wz : W × Z, ∑ e, p.initialJoint.mass ((wz.1, e), wz.2)) =
          ∑ we : W × E, ∑ z, p.initialJoint.mass (we, z) := by
        simp only [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro w _
        exact Finset.sum_comm
      _ = 1 := by
        simpa only [Fintype.sum_prod_type] using p.initialJoint.total

/-- The actual W marginal of the retained pair (W,E). -/
def pairedCoarseRecord (p : ConditionalProtocol (W × E) Z A Y) :
    FiniteLaw W where
  mass w := ∑ e, p.initialRecord.mass (w, e)
  nonnegative w := Finset.sum_nonneg (fun e _ => p.initialRecord.nonnegative _)
  total := by
    simpa only [Fintype.sum_prod_type] using p.initialRecord.total

/-- Four joint-law entropies giving I(Z;E|W). -/
def pairedInitialInformation (p : ConditionalProtocol (W × E) Z A Y) : ℝ :=
  entropy (pairedCoarseJoint p).mass + entropy p.initialRecord.mass -
    entropy (pairedCoarseRecord p).mass - entropy p.initialJoint.mass

/-- Four actual stopped-law entropies giving I(Z;(E,T_n)|W). -/
def pairedRetainedInformation (p : ConditionalProtocol (W × E) Z A Y)
    (n : ℕ) : ℝ :=
  entropy (pairedCoarseJoint p).mass +
    (∑ u, ((historyBank A Y n).map
      (fun h => entropyTerm (∑ z, conditionalStoppedMass p n u z h))).sum) -
    entropy (pairedCoarseRecord p).mass -
    ∑ u, ∑ z, ((historyBank A Y n).map
      (fun h => entropyTerm (conditionalStoppedMass p n u z h))).sum

theorem pairedRetainedInformation_chain
    (p : ConditionalProtocol (W × E) Z A Y) (n : ℕ) :
    pairedRetainedInformation p n = pairedInitialInformation p +
      conditionalJointInfo p n (historyBank A Y n) := by
  unfold pairedRetainedInformation pairedInitialInformation conditionalJointInfo
  ring

theorem pairedRetainedInformation_increment_bounds
    (p : ConditionalProtocol (W × E) Z A Y) (n : ℕ) (κ : ℝ)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ) :
    0 ≤ pairedRetainedInformation p n - pairedInitialInformation p ∧
      pairedRetainedInformation p n - pairedInitialInformation p ≤
        κ * conditionalExpectedCost p n (historyBank A Y n) := by
  rw [pairedRetainedInformation_chain]
  simp only [add_sub_cancel_left]
  exact (conditionalJointInfo_bounds p n _ (historyBank_complete A Y n) κ hc).2.2.2

/-- Both envelopes use the same finite target carrier and initial joint law. -/
theorem pairedRetainedGap_drop
    (p : ConditionalProtocol (W × E) Z A Y) (n : ℕ) :
    (terminalEnvelope Z - pairedInitialInformation p) -
      (terminalEnvelope Z - pairedRetainedInformation p n) =
        conditionalJointInfo p n (historyBank A Y n) := by
  rw [pairedRetainedInformation_chain]
  ring

end PairedInitialRecord

#check @pairedCoarseJoint
#print axioms pairedCoarseJoint
#check @pairedCoarseRecord
#print axioms pairedCoarseRecord
#check @pairedInitialInformation
#print axioms pairedInitialInformation
#check @pairedRetainedInformation
#print axioms pairedRetainedInformation
#check @pairedRetainedInformation_chain
#print axioms pairedRetainedInformation_chain
#check @pairedRetainedInformation_increment_bounds
#print axioms pairedRetainedInformation_increment_bounds
#check @pairedRetainedGap_drop
#print axioms pairedRetainedGap_drop

end

end OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

namespace OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open scoped BigOperators Classical

noncomputable section

variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

/-- Testing the later stopped law by any function of the retained prefix
gives the earlier stopped law. This is derived from source tree conservation. -/
theorem stoppedMass_take_test (p : FiniteProtocol Z A Y) (z : Z)
    (m n : ℕ) (hmn : m ≤ n) (φ : List (A × Y) → ℝ) :
    (∑ h ∈ historySet (A × Y) n,
      stoppedMass p n z h * φ (h.take m)) =
    ∑ h ∈ historySet (A × Y) m, stoppedMass p m z h * φ h := by
  classical
  let f : List (A × Y) → ℝ := fun h => prefixMass p z h * φ (h.take m)
  let d : List (A × Y) → ℝ := fun h => f h - ∑ e, f (h ++ [e])
  have hs : ∀ h, p.stop h = true → ∀ e, f (h ++ [e]) = 0 := by
    intro h hh e
    obtain ⟨a, y⟩ := e
    simp [f, prefixMass_append, hh]
  have hd (h : List (A × Y)) (hm : m ≤ h.length)
      (hh : p.stop h = false) : d h = 0 := by
    change prefixMass p z h * φ (h.take m) -
      (∑ e, prefixMass p z (h ++ [e]) * φ ((h ++ [e]).take m)) = 0
    simp_rw [List.take_append_of_le_length hm]
    rw [← Finset.sum_mul]
    have hc : (∑ e : A × Y, prefixMass p z (h ++ [e])) = prefixMass p z h := by
      rw [Fintype.sum_prod_type]
      simpa [hh] using prefixMass_children p h z
    rw [hc, sub_self]
  have ha :
      (∑ h ∈ historySet (A × Y) n, activeValue p.stop n d h) =
      ∑ h ∈ historySet (A × Y) m, activeValue p.stop m d h := by
    calc
      _ = ∑ h ∈ historySet (A × Y) m, activeValue p.stop n d h := by
        symm
        apply Finset.sum_subset (historySet_mono hmn)
        intro h _ hh
        have hl : ¬ h.length ≤ m := by simpa only [mem_historySet] using hh
        have hm : m ≤ h.length := by omega
        cases hh : p.stop h with
        | false => simp [activeValue, hh, hd h hm hh]
        | true => simp [activeValue, hh]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h _
        by_cases hl : h.length < m
        · have hn : h.length < n := lt_of_lt_of_le hl hmn
          simp [activeValue, hl, hn]
        · have hm : m ≤ h.length := le_of_not_gt hl
          cases hh : p.stop h with
          | false => simp [activeValue, hh, hd h hm hh]
          | true => simp [activeValue, hh]
  have hb (k : ℕ) :
      (∑ h ∈ historySet (A × Y) k, boundaryValue p.stop k f h) =
      ∑ h ∈ historySet (A × Y) k, stoppedMass p k z h * φ (h.take m) := by
    apply Finset.sum_congr rfl
    intro h _
    unfold boundaryValue stoppedMass
    split_ifs <;> simp [f]
  have hbn := historySet_boundary_balance p.stop n f hs
  have hbm := historySet_boundary_balance p.stop m f hs
  change (∑ h ∈ historySet (A × Y) n, boundaryValue p.stop n f h) +
    (∑ h ∈ historySet (A × Y) n, activeValue p.stop n d h) = f [] at hbn
  change (∑ h ∈ historySet (A × Y) m, boundaryValue p.stop m f h) +
    (∑ h ∈ historySet (A × Y) m, activeValue p.stop m d h) = f [] at hbm
  rw [hb n, ha] at hbn
  rw [hb m] at hbm
  have hm :
      (∑ h ∈ historySet (A × Y) m, stoppedMass p m z h * φ (h.take m)) =
      ∑ h ∈ historySet (A × Y) m, stoppedMass p m z h * φ h := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [List.take_of_length_le ((mem_historySet m h).mp hh)]
  rw [hm] at hbm
  linarith

/-- The earlier stopped law is the actual pushforward under List.take. -/
theorem stoppedMass_take_marginal (p : FiniteProtocol Z A Y) (z : Z)
    (m n : ℕ) (hmn : m ≤ n) (g : historySet (A × Y) m) :
    (∑ h ∈ historySet (A × Y) n,
      if h.take m = g.val then stoppedMass p n z h else 0) =
      stoppedMass p m z g.val := by
  classical
  have ht := stoppedMass_take_test p z m n hmn
    (fun h => if h = g.val then 1 else 0)
  simpa [mul_ite, g.property] using ht

theorem conditionalStoppedMass_take_marginal
    (p : ConditionalProtocol H0 Z A Y) (u : H0) (z : Z)
    (m n : ℕ) (hmn : m ≤ n) (g : historySet (A × Y) m) :
    (∑ h ∈ historySet (A × Y) n,
      if h.take m = g.val then conditionalStoppedMass p n u z h else 0) =
      conditionalStoppedMass p m u z g.val := by
  classical
  unfold conditionalStoppedMass
  simpa only [Finset.mul_sum, mul_ite, mul_zero] using
    congrArg (fun x : ℝ => p.initialRecord.mass u * x)
      (stoppedMass_take_marginal (p.given u) z m n hmn g)

#check @stoppedMass_take_test
#print axioms stoppedMass_take_test
#check @stoppedMass_take_marginal
#print axioms stoppedMass_take_marginal
#check @conditionalStoppedMass_take_marginal
#print axioms conditionalStoppedMass_take_marginal

end

end OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

namespace OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open scoped BigOperators Classical

noncomputable section

variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

/-- Actual joint cells for the initial record, target, old retained prefix
and later stopped history. The old prefix is retained as a deterministic record. -/
def retainedContinuationMass (p : ConditionalProtocol H0 Z A Y) (m n : ℕ)
    (u : H0) (z : Z) (g h : List (A × Y)) : ℝ :=
  if h.take m = g then conditionalStoppedMass p n u z h else 0

theorem retainedContinuationMass_nonnegative
    (p : ConditionalProtocol H0 Z A Y) (m n : ℕ)
    (u : H0) (z : Z) (g h : List (A × Y)) :
    0 ≤ retainedContinuationMass p m n u z g h := by
  unfold retainedContinuationMass
  split_ifs
  · exact conditionalStoppedMass_nonnegative p n u z h
  · exact le_rfl

theorem retainedContinuationMass_later_marginal
    (p : ConditionalProtocol H0 Z A Y) (m n : ℕ)
    (u : H0) (z : Z) (h : List (A × Y)) :
    (∑ g ∈ historySet (A × Y) m, retainedContinuationMass p m n u z g h) =
      conditionalStoppedMass p n u z h := by
  simp [retainedContinuationMass, mem_historySet, List.length_take]

theorem retainedContinuationMass_earlier_marginal
    (p : ConditionalProtocol H0 Z A Y) (m n : ℕ) (hmn : m ≤ n)
    (u : H0) (z : Z) (g : historySet (A × Y) m) :
    (∑ h ∈ historySet (A × Y) n,
      retainedContinuationMass p m n u z g.val h) =
      conditionalStoppedMass p m u z g.val :=
  conditionalStoppedMass_take_marginal p u z m n hmn g

theorem retainedContinuationMass_total
    (p : ConditionalProtocol H0 Z A Y) (m n : ℕ) :
    (∑ u, ∑ z, ∑ h ∈ historySet (A × Y) n,
      ∑ g ∈ historySet (A × Y) m, retainedContinuationMass p m n u z g h) = 1 := by
  simp only [retainedContinuationMass_later_marginal]
  have ht := conditionalStoppedMass_total p n _ (historyBank_complete A Y n)
  simpa only [(historyBank_complete A Y n).sum_eq] using ht

/-- Conditional mutual information of the actual retained joint cells.
Each massUncertainty is the entropy of its target slice minus its record mass term. -/
def retainedContinuationInformation (p : ConditionalProtocol H0 Z A Y)
    (m n : ℕ) : ℝ :=
  ∑ u, ∑ g ∈ historySet (A × Y) m,
    (massUncertainty (fun z => ∑ h ∈ historySet (A × Y) n,
      retainedContinuationMass p m n u z g h) -
    ∑ h ∈ historySet (A × Y) n,
      massUncertainty (fun z => retainedContinuationMass p m n u z g h))

theorem retainedContinuationMass_uncertainty_marginal
    (p : ConditionalProtocol H0 Z A Y) (m n : ℕ)
    (u : H0) (h : List (A × Y)) :
    (∑ g ∈ historySet (A × Y) m,
      massUncertainty (fun z => retainedContinuationMass p m n u z g h)) =
      massUncertainty (fun z => conditionalStoppedMass p n u z h) := by
  have he (g : List (A × Y)) :
      massUncertainty (fun z => retainedContinuationMass p m n u z g h) =
        if h.take m = g then
          massUncertainty (fun z => conditionalStoppedMass p n u z h) else 0 := by
    by_cases hg : h.take m = g
    · simp [retainedContinuationMass, hg]
    · simp [retainedContinuationMass, hg, massUncertainty_zero]
  simp_rw [he]
  simp [mem_historySet, List.length_take]

theorem retainedContinuationInformation_eq_residual_sub
    (p : ConditionalProtocol H0 Z A Y) (m n : ℕ) (hmn : m ≤ n) :
    retainedContinuationInformation p m n = residualEntropy p m - residualEntropy p n := by
  have he (u : H0) :
      (∑ g ∈ historySet (A × Y) m,
        massUncertainty (fun z => ∑ h ∈ historySet (A × Y) n,
          retainedContinuationMass p m n u z g h)) =
      ∑ g ∈ historySet (A × Y) m,
        massUncertainty (fun z => conditionalStoppedMass p m u z g) := by
    apply Finset.sum_congr rfl
    intro g hg
    congr 1
    funext z
    exact retainedContinuationMass_earlier_marginal p m n hmn u z ⟨g, hg⟩
  have hl (u : H0) :
      (∑ g ∈ historySet (A × Y) m, ∑ h ∈ historySet (A × Y) n,
        massUncertainty (fun z => retainedContinuationMass p m n u z g h)) =
      ∑ h ∈ historySet (A × Y) n,
        massUncertainty (fun z => conditionalStoppedMass p n u z h) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    exact retainedContinuationMass_uncertainty_marginal p m n u h
  unfold retainedContinuationInformation residualEntropy
  simp_rw [Finset.sum_sub_distrib, he, hl]

/-- The gap decrease is the conditional information of the actual retained joint law. -/
theorem terminalGap_drop_eq_retainedInformation
    (p : ConditionalProtocol H0 Z A Y) (m n : ℕ) (hmn : m ≤ n) :
    terminalGap p m - terminalGap p n = retainedContinuationInformation p m n := by
  rw [retainedContinuationInformation_eq_residual_sub p m n hmn,
    terminalGap_eq_priorSlack_add_residual p m,
    terminalGap_eq_priorSlack_add_residual p n]
  ring

theorem retainedContinuationInformation_chain
    (p : ConditionalProtocol H0 Z A Y) (m n : ℕ) (hmn : m ≤ n) :
    conditionalJointInfo p n (historyBank A Y n) =
      conditionalJointInfo p m (historyBank A Y m) +
        retainedContinuationInformation p m n := by
  have h := terminalGap_drop_eq_retainedInformation p m n hmn
  unfold terminalGap at h
  linarith

theorem retainedContinuationInformation_cost_bounds
    (p : ConditionalProtocol H0 Z A Y) (κ : ℝ)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ)
    (m n : ℕ) (hmn : m ≤ n) :
    0 ≤ retainedContinuationInformation p m n ∧
      retainedContinuationInformation p m n ≤
        κ * (conditionalExpectedCost p n (historyBank A Y n) -
          conditionalExpectedCost p m (historyBank A Y m)) := by
  rw [← terminalGap_drop_eq_retainedInformation p m n hmn]
  exact terminalGap_drop_bounds p κ hc m n hmn

#check @retainedContinuationMass
#print axioms retainedContinuationMass
#check @retainedContinuationMass_nonnegative
#print axioms retainedContinuationMass_nonnegative
#check @retainedContinuationMass_later_marginal
#print axioms retainedContinuationMass_later_marginal
#check @retainedContinuationMass_earlier_marginal
#print axioms retainedContinuationMass_earlier_marginal
#check @retainedContinuationMass_total
#print axioms retainedContinuationMass_total
#check @retainedContinuationInformation
#print axioms retainedContinuationInformation
#check @retainedContinuationMass_uncertainty_marginal
#print axioms retainedContinuationMass_uncertainty_marginal
#check @retainedContinuationInformation_eq_residual_sub
#print axioms retainedContinuationInformation_eq_residual_sub
#check @terminalGap_drop_eq_retainedInformation
#print axioms terminalGap_drop_eq_retainedInformation
#check @retainedContinuationInformation_chain
#print axioms retainedContinuationInformation_chain
#check @retainedContinuationInformation_cost_bounds
#print axioms retainedContinuationInformation_cost_bounds

end

end OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

namespace OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open scoped BigOperators Classical

noncomputable section

variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

/-- Only actual positive-probability active readings require the row and price cap.
Stopped padding and impossible actions impose no extra hypotheses. -/
structure ActivePairMenu (p : FiniteProtocol Bool A Y) (δ : ℝ) : Prop where
  rows : ∀ h a, 0 < historyMass p h → p.stop h = false →
    0 < (p.policy h).mass a →
    BoundarySingularity.discrimination (p.observation h a true).mass
      (p.observation h a false).mass ≤ δ
  reading_cost : ∀ h a, 0 < historyMass p h → p.stop h = false →
    0 < (p.policy h).mass a → 1 ≤ p.cost h a

def activePairMenu_of_pairMenu (p : FiniteProtocol Bool A Y) (δ : ℝ)
    (menu : BoundarySingularity.PairMenu p δ) : ActivePairMenu p δ where
  rows h a _ _ _ := menu.rows h a
  reading_cost h a _ _ _ := menu.reading_cost h a

/-- Actual one-reading information cannot exceed the binary posterior entropy. -/
theorem binary_localGain_le_one (p : FiniteProtocol Bool A Y)
    (h : List (A × Y)) (a : A) (hw : 0 < historyMass p h) :
    localGain p h a ≤ 1 := by
  have hu : 0 ≤ ∑ y, massUncertainty
      (fun z => posterior p h z * (p.observation h a z).mass y) := by
    apply Finset.sum_nonneg
    intro y _
    exact InstrumentDivision.massUncertainty_bool_nonneg _
      (fun z => mul_nonneg (posterior_nonnegative p h z)
        ((p.observation h a z).nonnegative y))
  have hd := massUncertainty_kernel_sum (posterior p h)
    (fun z y => (p.observation h a z).mass y)
    (fun z => (p.observation h a z).total)
  change (∑ y, massUncertainty
      (fun z => posterior p h z * (p.observation h a z).mass y)) =
    entropy (posterior p h) - localGain p h a at hd
  have he : entropy (posterior p h) ≤ 1 := by
    calc
      entropy (posterior p h) ≤ terminalEnvelope Bool := by
        rw [entropy_eq_HBits]
        exact HBits_le_logb_card (posterior p h)
          (posterior_nonnegative p h) (posterior_total p h hw)
      _ = 1 := terminalEnvelope_bool
  linarith

theorem binary_localGain_le_discrimination (p : FiniteProtocol Bool A Y)
    (h : List (A × Y)) (a : A) (hw : 0 < historyMass p h) :
    localGain p h a ≤
      BoundarySingularity.discrimination (p.observation h a true).mass
        (p.observation h a false).mass / Real.log 2 := by
  unfold localGain
  rw [BoundarySingularity.posterior_eq_binaryPrior_of_pos p h hw]
  exact BoundarySingularity.binary_information_le_discrimination
    (posterior p h true) (posterior_nonnegative p h true) (posterior_le_one p h true)
    (fun z y => (p.observation h a z).mass y)
    (fun z y => (p.observation h a z).nonnegative y)
    (fun z => (p.observation h a z).total)

def binaryDiscriminationCapacity (δ : ℝ) : ℝ := min 1 (δ / Real.log 2)

theorem binaryDiscriminationCapacity_nonnegative (δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ binaryDiscriminationCapacity δ :=
  le_min zero_le_one (div_nonneg hδ (Real.log_pos one_lt_two).le)

theorem binaryDiscriminationCapacity_positive (δ : ℝ) (hδ : 0 < δ) :
    0 < binaryDiscriminationCapacity δ :=
  lt_min zero_lt_one (div_pos hδ (Real.log_pos one_lt_two))

theorem activePairMenu_capacity (p : FiniteProtocol Bool A Y) (δ : ℝ)
    (hδ : 0 ≤ δ) (menu : ActivePairMenu p δ) :
    LocalCapacityBound p (binaryDiscriminationCapacity δ) := by
  intro h a hw hs ha
  have hd : localGain p h a ≤ δ / Real.log 2 :=
    (binary_localGain_le_discrimination p h a hw).trans
      (div_le_div_of_nonneg_right (menu.rows h a hw hs ha)
        (Real.log_pos one_lt_two).le)
  calc
    localGain p h a ≤ binaryDiscriminationCapacity δ :=
      le_min (binary_localGain_le_one p h a hw) hd
    _ ≤ binaryDiscriminationCapacity δ * p.cost h a :=
      le_mul_of_one_le_right (binaryDiscriminationCapacity_nonnegative δ hδ)
        (menu.reading_cost h a hw hs ha)

theorem pairMenu_capped_capacity (p : FiniteProtocol Bool A Y) (δ : ℝ)
    (hδ : 0 ≤ δ) (menu : BoundarySingularity.PairMenu p δ) :
    LocalCapacityBound p (binaryDiscriminationCapacity δ) :=
  activePairMenu_capacity p δ hδ (activePairMenu_of_pairMenu p δ menu)

theorem binary_terminalGap_bounds (p : ConditionalProtocol H0 Bool A Y)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (menu : ∀ u, 0 < p.initialRecord.mass u → ActivePairMenu (p.given u) δ)
    (fair : ∀ u, 0 < p.initialRecord.mass u →
      (p.given u).prior.mass = uniformMass Bool) (n : ℕ) :
    terminalGap p n = residualEntropy p n ∧
      max 0 (1 - binaryDiscriminationCapacity δ *
        conditionalExpectedCost p n (historyBank A Y n)) ≤ terminalGap p n := by
  constructor
  · rw [terminalGap_eq_priorSlack_add_residual, priorSlack_zero_of_uniform p fair,
      zero_add]
  · apply max_le (terminalGap_nonnegative p n)
    have hb := terminalGap_lower_of_localCapacity p n (binaryDiscriminationCapacity δ)
      (fun u hu => activePairMenu_capacity (p.given u) δ hδ (menu u hu))
    simpa only [terminalEnvelope_bool] using hb

theorem binary_terminalGap_price (p : ConditionalProtocol H0 Bool A Y)
    (δ : ℝ) (hδ : 0 < δ)
    (menu : ∀ u, 0 < p.initialRecord.mass u → ActivePairMenu (p.given u) δ)
    (n : ℕ) (g : ℝ) (hg : g < 1) (hgap : terminalGap p n ≤ g) :
    (1 - g) * Real.log 2 / δ ≤ (1 - g) / binaryDiscriminationCapacity δ ∧
      (1 - g) / binaryDiscriminationCapacity δ ≤
        conditionalExpectedCost p n (historyBank A Y n) := by
  have hk := binaryDiscriminationCapacity_positive δ hδ
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  constructor
  · calc
      (1 - g) * Real.log 2 / δ = (1 - g) / (δ / Real.log 2) := by
        field_simp
      _ ≤ (1 - g) / binaryDiscriminationCapacity δ := by
        apply (div_le_div_iff₀ (div_pos hδ hlog) hk).mpr
        exact mul_le_mul_of_nonneg_left (min_le_right 1 (δ / Real.log 2))
          (sub_nonneg.mpr hg.le)
  · have hb := cost_lower_of_terminalGap_le p n (binaryDiscriminationCapacity δ) g hk
      (fun u hu => activePairMenu_capacity (p.given u) δ hδ.le (menu u hu)) hgap
    simpa only [terminalEnvelope_bool, max_eq_left (sub_nonneg.mpr hg.le)] using hb

theorem binary_terminalGap_zero_discrimination (p : ConditionalProtocol H0 Bool A Y)
    (menu : ∀ u, 0 < p.initialRecord.mass u → ActivePairMenu (p.given u) 0)
    (n : ℕ) : terminalGap p n = 1 := by
  have hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) 0 := by
    intro u hu
    simpa [binaryDiscriminationCapacity] using
      activePairMenu_capacity (p.given u) 0 le_rfl (menu u hu)
  simpa only [terminalEnvelope_bool] using terminalGap_zero_capacity p n hc

#check @ActivePairMenu
#print axioms ActivePairMenu
#check @activePairMenu_of_pairMenu
#print axioms activePairMenu_of_pairMenu
#check @binary_localGain_le_one
#print axioms binary_localGain_le_one
#check @binary_localGain_le_discrimination
#print axioms binary_localGain_le_discrimination
#check @binaryDiscriminationCapacity
#print axioms binaryDiscriminationCapacity
#check @binaryDiscriminationCapacity_nonnegative
#print axioms binaryDiscriminationCapacity_nonnegative
#check @binaryDiscriminationCapacity_positive
#print axioms binaryDiscriminationCapacity_positive
#check @activePairMenu_capacity
#print axioms activePairMenu_capacity
#check @pairMenu_capped_capacity
#print axioms pairMenu_capped_capacity
#check @binary_terminalGap_bounds
#print axioms binary_terminalGap_bounds
#check @binary_terminalGap_price
#print axioms binary_terminalGap_price
#check @binary_terminalGap_zero_discrimination
#print axioms binary_terminalGap_zero_discrimination

end

end OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

namespace OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open scoped BigOperators Classical

noncomputable section

variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

def repeatGapCount (P Q : FiniteLaw Y) (η : ℝ) : ℕ :=
  ⌈4 * Real.log (1 / (2 * η)) /
    BoundarySingularity.discrimination P.mass Q.mass⌉₊

/-- The actual independent repetition protocol, with a constant initial record. -/
def repeatGapProtocol (P Q : FiniteLaw Y) (N : ℕ) :
    ConditionalProtocol Unit Bool Unit Y :=
  unitRecordProtocol (PairResolution.repeatProtocol P Q N)

theorem repeatGapProtocol_uniform (P Q : FiniteLaw Y) (N : ℕ) :
    ∀ u, 0 < (repeatGapProtocol P Q N).initialRecord.mass u →
      ((repeatGapProtocol P Q N).given u).prior.mass = uniformMass Bool := by
  intro u _
  funext z
  norm_num [repeatGapProtocol, unitRecordProtocol, PairResolution.repeatProtocol,
    ResolutionAttainment.fairLaw, uniformMass]

theorem repeatGapProtocol_cost (P Q : FiniteLaw Y) (N : ℕ) :
    conditionalExpectedCost (repeatGapProtocol P Q N) N (historyBank Unit Y N) = N := by
  unfold repeatGapProtocol
  rw [unitRecordProtocol_cost]
  exact PairResolution.repeat_cost P Q N

/-- The actual retained record attains the binary entropy gap at its counted cost. -/
theorem repeatGap_target (P Q : FiniteLaw Y)
    (hd : 0 < BoundarySingularity.discrimination P.mass Q.mass)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) :
    terminalGap (repeatGapProtocol P Q (repeatGapCount P Q η))
        (repeatGapCount P Q η) ≤ Real.binEntropy η / Real.log 2 ∧
      conditionalExpectedCost (repeatGapProtocol P Q (repeatGapCount P Q η))
        (repeatGapCount P Q η) (historyBank Unit Y (repeatGapCount P Q η)) =
          (repeatGapCount P Q η : ℝ) ∧
      (repeatGapCount P Q η : ℝ) ≤
        4 * Real.log (1 / (2 * η)) /
          BoundarySingularity.discrimination P.mass Q.mass + 1 := by
  have ht := PairResolution.repeat_target P Q hd η hη0 hη1
  refine ⟨?_, repeatGapProtocol_cost P Q _, ?_⟩
  · unfold terminalGap repeatGapProtocol
    rw [unitRecordProtocol_information, terminalEnvelope_bool]
    have hi : 1 - Real.binEntropy η / Real.log 2 ≤
        terminalMI (PairResolution.repeatProtocol P Q (repeatGapCount P Q η))
          (repeatGapCount P Q η) (historyBank Unit Y (repeatGapCount P Q η)) := ht.1
    linarith
  · exact ht.2.2

#check @repeatGapCount
#print axioms repeatGapCount
#check @repeatGapProtocol
#print axioms repeatGapProtocol
#check @repeatGapProtocol_uniform
#print axioms repeatGapProtocol_uniform
#check @repeatGapProtocol_cost
#print axioms repeatGapProtocol_cost
#check @repeatGap_target
#print axioms repeatGap_target

end

end OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

namespace OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open scoped BigOperators Classical

noncomputable section

variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

/-- A finite experiment includes every finite retained seed, action and outcome type. -/
structure BinaryGapExperiment where
  H0 : Type
  A : Type
  Y : Type
  fintypeH0 : Fintype H0
  fintypeA : Fintype A
  fintypeY : Fintype Y
  protocol : @ConditionalProtocol H0 Bool A Y fintypeH0 inferInstance fintypeA fintypeY
  horizon : ℕ

attribute [instance] BinaryGapExperiment.fintypeH0 BinaryGapExperiment.fintypeA
  BinaryGapExperiment.fintypeY

def BinaryGapExperiment.cost (e : BinaryGapExperiment) : ℝ :=
  conditionalExpectedCost e.protocol e.horizon (historyBank e.A e.Y e.horizon)

def BinaryGapExperiment.gap (e : BinaryGapExperiment) : ℝ :=
  terminalGap e.protocol e.horizon

def BinaryGapExperiment.Fair (e : BinaryGapExperiment) : Prop :=
  ∀ u, 0 < e.protocol.initialRecord.mass u →
    (e.protocol.given u).prior.mass = uniformMass Bool

def BinaryGapExperiment.HasCap (e : BinaryGapExperiment) (δ : ℝ) : Prop :=
  ∀ u, 0 < e.protocol.initialRecord.mass u → ActivePairMenu (e.protocol.given u) δ

/-- The cost set consists only of actual permitted fair experiments attaining the gap. -/
def binaryGapCosts (menu : Set BinaryGapExperiment) (g : ℝ) : Set ℝ :=
  {c | ∃ e ∈ menu, e.Fair ∧ e.gap ≤ g ∧ e.cost = c}

def optimalGapCost (menu : Set BinaryGapExperiment) (g : ℝ) : ℝ :=
  sInf (binaryGapCosts menu g)

theorem binaryGapCosts_bddBelow (menu : Set BinaryGapExperiment) (g : ℝ) :
    BddBelow (binaryGapCosts menu g) := by
  refine ⟨0, ?_⟩
  rintro c ⟨e, _, _, _, rfl⟩
  exact conditionalExpectedCost_nonnegative e.protocol e.horizon _
    (historyBank_complete e.A e.Y e.horizon)

def repeatGapExperiment (P Q : FiniteLaw Y) (N : ℕ) : BinaryGapExperiment where
  H0 := Unit
  A := Unit
  Y := Y
  fintypeH0 := inferInstance
  fintypeA := inferInstance
  fintypeY := inferInstance
  protocol := repeatGapProtocol P Q N
  horizon := N

theorem repeatGapExperiment_fair (P Q : FiniteLaw Y) (N : ℕ) :
    (repeatGapExperiment P Q N).Fair :=
  repeatGapProtocol_uniform P Q N

theorem repeatGapExperiment_cost (P Q : FiniteLaw Y) (N : ℕ) :
    (repeatGapExperiment P Q N).cost = N :=
  repeatGapProtocol_cost P Q N

theorem repeatGapCost_mem (menu : Set BinaryGapExperiment) (P Q : FiniteLaw Y)
    (hd : 0 < BoundarySingularity.discrimination P.mass Q.mass)
    (g η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hηg : Real.binEntropy η / Real.log 2 ≤ g)
    (permitted : repeatGapExperiment P Q (repeatGapCount P Q η) ∈ menu) :
    (repeatGapCount P Q η : ℝ) ∈ binaryGapCosts menu g := by
  refine ⟨repeatGapExperiment P Q (repeatGapCount P Q η), permitted,
    repeatGapExperiment_fair P Q _, ?_, repeatGapExperiment_cost P Q _⟩
  exact (repeatGap_target P Q hd η hη0 hη1).1.trans hηg

theorem optimalGapCost_lower (menu : Set BinaryGapExperiment) (δ g : ℝ)
    (hδ : 0 < δ) (hg : g < 1)
    (cap : ∀ e ∈ menu, e.HasCap δ) (hne : (binaryGapCosts menu g).Nonempty) :
    (1 - g) * Real.log 2 / δ ≤ optimalGapCost menu g := by
  apply le_csInf hne
  rintro c ⟨e, he, _, hgap, rfl⟩
  have hb := binary_terminalGap_price e.protocol δ hδ (cap e he)
    e.horizon g hg hgap
  exact hb.1.trans hb.2

theorem optimalGapCost_le_repeat (menu : Set BinaryGapExperiment) (P Q : FiniteLaw Y)
    (hd : 0 < BoundarySingularity.discrimination P.mass Q.mass)
    (g η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hηg : Real.binEntropy η / Real.log 2 ≤ g)
    (permitted : repeatGapExperiment P Q (repeatGapCount P Q η) ∈ menu) :
    optimalGapCost menu g ≤ (repeatGapCount P Q η : ℝ) :=
  csInf_le (binaryGapCosts_bddBelow menu g)
    (repeatGapCost_mem menu P Q hd g η hη0 hη1 hηg permitted)

#check @BinaryGapExperiment
#print axioms BinaryGapExperiment
#check @BinaryGapExperiment.cost
#print axioms BinaryGapExperiment.cost
#check @BinaryGapExperiment.gap
#print axioms BinaryGapExperiment.gap
#check @BinaryGapExperiment.Fair
#print axioms BinaryGapExperiment.Fair
#check @BinaryGapExperiment.HasCap
#print axioms BinaryGapExperiment.HasCap
#check @binaryGapCosts
#print axioms binaryGapCosts
#check @optimalGapCost
#print axioms optimalGapCost
#check @binaryGapCosts_bddBelow
#print axioms binaryGapCosts_bddBelow
#check @repeatGapExperiment
#print axioms repeatGapExperiment
#check @repeatGapExperiment_fair
#print axioms repeatGapExperiment_fair
#check @repeatGapExperiment_cost
#print axioms repeatGapExperiment_cost
#check @repeatGapCost_mem
#print axioms repeatGapCost_mem
#check @optimalGapCost_lower
#print axioms optimalGapCost_lower
#check @optimalGapCost_le_repeat
#print axioms optimalGapCost_le_repeat

end

end OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

namespace OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open scoped BigOperators Classical

noncomputable section

variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

theorem exists_small_binary_entropy (g : ℝ) (hg : 0 < g) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ Real.binEntropy η / Real.log 2 ≤ g := by
  have hc : ContinuousAt (fun η : ℝ => Real.binEntropy η / Real.log 2) 0 :=
    (Real.binEntropy_continuous.div_const (Real.log 2)).continuousAt
  obtain ⟨ε, hε, hbound⟩ := Metric.continuousAt_iff.mp hc g hg
  let η : ℝ := min (ε / 2) (1 / 4)
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηq : η ≤ 1 / 4 := min_le_right _ _
  have hi := hbound (x := η) (by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hη0] using hηε)
  simp only [Real.binEntropy_zero, zero_div, Real.dist_eq, sub_zero] at hi
  exact ⟨η, hη0, by linarith, (le_abs_self _).trans hi.le⟩

theorem binaryGapCosts_nonempty_of_repeat (menu : Set BinaryGapExperiment)
    (P Q : FiniteLaw Y) (hd : 0 < BoundarySingularity.discrimination P.mass Q.mass)
    (g : ℝ) (hg : 0 < g)
    (permitted : ∀ N, repeatGapExperiment P Q N ∈ menu) :
    (binaryGapCosts menu g).Nonempty := by
  obtain ⟨η, hη0, hη1, hηg⟩ := exists_small_binary_entropy g hg
  exact ⟨_, repeatGapCost_mem menu P Q hd g η hη0 hη1.le hηg (permitted _)⟩

/-- The exact menu infimum is bounded by the cap price and an available repeat count. -/
theorem optimalGapCost_two_sided (menu : Set BinaryGapExperiment)
    (P Q : FiniteLaw Y) (δ a g η : ℝ) (hδ : 0 < δ) (ha : 0 < a)
    (hg : g < 1) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hηg : Real.binEntropy η / Real.log 2 ≤ g)
    (hd : a * δ ≤ BoundarySingularity.discrimination P.mass Q.mass)
    (cap : ∀ e ∈ menu, e.HasCap δ)
    (permitted : repeatGapExperiment P Q (repeatGapCount P Q η) ∈ menu) :
    (1 - g) * Real.log 2 / δ ≤ optimalGapCost menu g ∧
      optimalGapCost menu g ≤
        ((⌈4 * Real.log (1 / (2 * η)) / (a * δ)⌉₊ : ℕ) : ℝ) := by
  have hd0 : 0 < BoundarySingularity.discrimination P.mass Q.mass :=
    lt_of_lt_of_le (mul_pos ha hδ) hd
  have hmem := repeatGapCost_mem menu P Q hd0 g η hη0 hη1 hηg permitted
  have hL : 0 ≤ Real.log (1 / (2 * η)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith
  refine ⟨optimalGapCost_lower menu δ g hδ hg cap ⟨_, hmem⟩, ?_⟩
  calc
    optimalGapCost menu g ≤ (repeatGapCount P Q η : ℝ) :=
      optimalGapCost_le_repeat menu P Q hd0 g η hη0 hη1 hηg permitted
    _ ≤ ((⌈4 * Real.log (1 / (2 * η)) / (a * δ)⌉₊ : ℕ) : ℝ) := by
      have hdiv :
          4 * Real.log (1 / (2 * η)) /
              BoundarySingularity.discrimination P.mass Q.mass ≤
            4 * Real.log (1 / (2 * η)) / (a * δ) :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hL) (mul_pos ha hδ) hd
      exact_mod_cast Nat.ceil_mono hdiv

/-- Uniform positive constants for every capped menu and every 0 < δ ≤ 1.
The constants depend only on the fixed target and repeatability ratio. -/
theorem optimalGapCost_inverse_bounds (menu : Set BinaryGapExperiment)
    (P Q : FiniteLaw Y) (δ a g η : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 < a)
    (hg : g < 1) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hηg : Real.binEntropy η / Real.log 2 ≤ g)
    (hd : a * δ ≤ BoundarySingularity.discrimination P.mass Q.mass)
    (cap : ∀ e ∈ menu, e.HasCap δ)
    (permitted : repeatGapExperiment P Q (repeatGapCount P Q η) ∈ menu) :
    0 < (1 - g) * Real.log 2 ∧
      0 < 4 * Real.log (1 / (2 * η)) / a + 1 ∧
      ((1 - g) * Real.log 2) / δ ≤ optimalGapCost menu g ∧
      optimalGapCost menu g ≤
        (4 * Real.log (1 / (2 * η)) / a + 1) / δ := by
  have hL : 0 ≤ Real.log (1 / (2 * η)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hK : 0 ≤ 4 * Real.log (1 / (2 * η)) := mul_nonneg (by norm_num) hL
  have hb := optimalGapCost_two_sided menu P Q δ a g η hδ ha hg hη0 hη1 hηg
    hd cap permitted
  refine ⟨mul_pos (sub_pos.mpr hg) (Real.log_pos one_lt_two),
    by positivity, hb.1, ?_⟩
  calc
    optimalGapCost menu g ≤ ((⌈4 * Real.log (1 / (2 * η)) / (a * δ)⌉₊ : ℕ) : ℝ) :=
      hb.2
    _ ≤ 4 * Real.log (1 / (2 * η)) / (a * δ) + 1 :=
      (Nat.ceil_lt_add_one (div_nonneg hK (mul_pos ha hδ).le)).le
    _ = (4 * Real.log (1 / (2 * η)) / a) / δ + 1 := by rw [div_div]
    _ ≤ (4 * Real.log (1 / (2 * η)) / a) / δ + 1 / δ :=
      add_le_add_left ((le_div_iff₀ hδ).mpr (by simpa using hδ1)) _
    _ = (4 * Real.log (1 / (2 * η)) / a + 1) / δ := by rw [add_div]

#check @exists_small_binary_entropy
#print axioms exists_small_binary_entropy
#check @binaryGapCosts_nonempty_of_repeat
#print axioms binaryGapCosts_nonempty_of_repeat
#check @optimalGapCost_two_sided
#print axioms optimalGapCost_two_sided
#check @optimalGapCost_inverse_bounds
#print axioms optimalGapCost_inverse_bounds

end

end OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

namespace OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open scoped BigOperators Classical

noncomputable section

variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

section TaskChange

variable {H1 Z1 A1 Y1 : Type} [Fintype H1] [Fintype Z1] [Fintype A1] [Fintype Y1]

/-- Changing the task carrier has a separate count term, with no same-law claim. -/
theorem terminalGap_task_change
    (old : ConditionalProtocol H0 Z A Y) (new : ConditionalProtocol H1 Z1 A1 Y1)
    (m n : ℕ) :
    terminalGap old m - terminalGap new n =
      (terminalEnvelope Z - terminalEnvelope Z1) +
      (conditionalJointInfo new n (historyBank A1 Y1 n) -
        conditionalJointInfo old m (historyBank A Y m)) := by
  unfold terminalGap
  ring

/-- Under the same retained joint law, the second term is actual conditional information. -/
theorem task_count_change_with_retained_information
    (p : ConditionalProtocol H0 Z A Y) (m n : ℕ) (hmn : m ≤ n) (Lold Lnew : ℝ) :
    (Lold - conditionalJointInfo p m (historyBank A Y m)) -
      (Lnew - conditionalJointInfo p n (historyBank A Y n)) =
        (Lold - Lnew) + retainedContinuationInformation p m n := by
  rw [retainedContinuationInformation_chain p m n hmn]
  ring

end TaskChange

/-- A constant empty record, zero readings and zero cost for any actual prior. -/
def noReadingProtocol (prior : FiniteLaw Z) : FiniteProtocol Z Unit Unit where
  prior := prior
  policy _ := unitLaw
  observation _ _ _ := unitLaw
  stop _ := true
  cost _ _ := 0
  cost_nonnegative _ _ := le_rfl

def noReadingConditional (prior : FiniteLaw Z) : ConditionalProtocol Unit Z Unit Unit :=
  unitRecordProtocol (noReadingProtocol prior)

theorem noReading_information_cost (prior : FiniteLaw Z) (n : ℕ) :
    conditionalJointInfo (noReadingConditional prior) n (historyBank Unit Unit n) = 0 ∧
      conditionalExpectedCost (noReadingConditional prior) n (historyBank Unit Unit n) = 0 := by
  unfold noReadingConditional
  rw [unitRecordProtocol_information, unitRecordProtocol_cost]
  constructor
  · rw [terminalMI_eq_gain_sum _ _ _ (historyBank_complete Unit Unit n)]
    simp [noReadingProtocol]
  · simp [expectedCost, noReadingProtocol]

theorem noReading_stopped_support (prior : FiniteLaw Z) (n : ℕ) (z : Z)
    (h : List (Unit × Unit)) (hh : h ≠ []) :
    stoppedMass (noReadingProtocol prior) n z h = 0 := by
  have hp : prefixMass (noReadingProtocol prior) z h = 0 := by
    induction h using List.reverseRecOn with
    | nil => exact False.elim (hh rfl)
    | append_singleton h e _ =>
      obtain ⟨a, y⟩ := e
      rw [prefixMass_append]
      simp [noReadingProtocol]
  unfold stoppedMass
  split_ifs <;> simp [hp]

theorem noReading_gap (prior : FiniteLaw Z) (n : ℕ) :
    terminalGap (noReadingConditional prior) n = terminalEnvelope Z := by
  unfold terminalGap
  rw [(noReading_information_cost prior n).1, sub_zero]

/-- The unique surviving terminal is the false branch of the original two-terminal carrier. -/
def survivingTerminal (_ : Unit) : Bool := false

theorem survivingTerminal_range :
    Set.range survivingTerminal = {false} := by
  ext b
  simp [survivingTerminal]

theorem two_to_one_restriction_control (n : ℕ) :
    Fintype.card Bool = 2 ∧ Fintype.card Unit = 1 ∧
      terminalGap (noReadingConditional ResolutionAttainment.fairLaw) n = 1 ∧
      terminalGap (noReadingConditional unitLaw) n = 0 ∧
      conditionalJointInfo (noReadingConditional ResolutionAttainment.fairLaw) n
        (historyBank Unit Unit n) = 0 ∧
      conditionalJointInfo (noReadingConditional unitLaw) n (historyBank Unit Unit n) = 0 ∧
      terminalGap (noReadingConditional ResolutionAttainment.fairLaw) n -
        terminalGap (noReadingConditional unitLaw) n = 1 := by
  have hold : terminalGap (noReadingConditional ResolutionAttainment.fairLaw) n = 1 := by
    rw [noReading_gap, terminalEnvelope_bool]
  have hnew : terminalGap (noReadingConditional unitLaw) n = 0 := by
    rw [noReading_gap]
    simp [terminalEnvelope]
  refine ⟨by simp, by simp, hold, hnew,
    (noReading_information_cost ResolutionAttainment.fairLaw n).1,
    (noReading_information_cost unitLaw n).1, ?_⟩
  rw [hold, hnew, sub_zero]

#check @terminalGap_task_change
#print axioms terminalGap_task_change
#check @task_count_change_with_retained_information
#print axioms task_count_change_with_retained_information
#check @noReadingProtocol
#print axioms noReadingProtocol
#check @noReadingConditional
#print axioms noReadingConditional
#check @noReading_information_cost
#print axioms noReading_information_cost
#check @noReading_stopped_support
#print axioms noReading_stopped_support
#check @noReading_gap
#print axioms noReading_gap
#check @survivingTerminal
#print axioms survivingTerminal
#check @survivingTerminal_range
#print axioms survivingTerminal_range
#check @two_to_one_restriction_control
#print axioms two_to_one_restriction_control

end

end OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

namespace OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open scoped BigOperators Classical

noncomputable section

variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

/-- The actual fair-label joint cells of the existing silent reset instrument. -/
def resetJointMass (z : Bool) (r : Unit) (x : Bool) : ℝ :=
  InstrumentDivision.pairJointMass
    (InstrumentComposition.deterministic InstrumentLoss.silentErase) false true z r x

theorem resetJointMass_eq (z : Bool) (r : Unit) (x : Bool) :
    resetJointMass z r x = if x = false then 1 / 2 else 0 := by
  cases r
  cases x <;> norm_num [resetJointMass, InstrumentDivision.pairJointMass,
    InstrumentComposition.deterministic, InstrumentLoss.silentErase]

def resetJointLaw : FiniteLaw (Bool × (Unit × Bool)) where
  mass zrx := resetJointMass zrx.1 zrx.2.1 zrx.2.2
  nonnegative zrx := InstrumentDivision.pairJointMass_nonneg _ false true _ _ _
  total := by
    simp only [Fintype.sum_prod_type, resetJointMass_eq, Fintype.sum_bool]
    norm_num

/-- Marginalizing the initial label gives the actual recorded outcome and final state. -/
def resetOutputMass (rx : Unit × Bool) : ℝ :=
  ∑ z, resetJointLaw.mass (z, rx)

def resetStateMass (x : Bool) : ℝ :=
  ∑ r : Unit, resetOutputMass (r, x)

theorem resetOutputMass_total : ∑ rx, resetOutputMass rx = 1 := by
  unfold resetOutputMass
  rw [Finset.sum_comm]
  simpa only [Fintype.sum_prod_type] using resetJointLaw.total

theorem resetJointLaw_product :
    resetJointLaw.mass = fun zrx : Bool × (Unit × Bool) =>
      ResolutionAttainment.fairLaw.mass zrx.1 * resetOutputMass zrx.2 := by
  funext zrx
  obtain ⟨z, r, x⟩ := zrx
  cases r
  cases x <;> norm_num [resetOutputMass, resetJointLaw, resetJointMass_eq,
    ResolutionAttainment.fairLaw, Fintype.sum_bool]

theorem reset_joint_information_zero : jointMI resetJointLaw.mass = 0 := by
  rw [resetJointLaw_product]
  exact jointMI_product_zero ResolutionAttainment.fairLaw.mass resetOutputMass
    ResolutionAttainment.fairLaw.total resetOutputMass_total

theorem reset_final_entropy_zero : entropy resetStateMass = 0 := by
  norm_num [entropy_eq_sum, resetStateMass, resetOutputMass, resetJointLaw,
    resetJointMass_eq, Fintype.sum_bool, entropyTerm_zero, entropyTerm_one]

/-- A state-entropy decrease from one bit to zero leaves the original bit unresolved.
The outcome and final state together carry zero actual joint-law information. -/
theorem silent_reset_control :
    (∀ z, InstrumentLoss.silentErase.post z = false) ∧
      (∀ z, InstrumentLoss.silentErase.read z = ()) ∧
      entropy ResolutionAttainment.fairLaw.mass = 1 ∧
      entropy resetStateMass = 0 ∧ jointMI resetJointLaw.mass = 0 ∧
      (∑ rx : Unit × Bool, massUncertainty
        (fun z => resetJointMass z rx.1 rx.2)) = 1 := by
  refine ⟨fun _ => rfl, fun _ => rfl, ResolutionAttainment.fairLaw_entropy,
    reset_final_entropy_zero, reset_joint_information_zero, ?_⟩
  exact InstrumentDivision.keep_erase_division.2.2

#check @resetJointMass
#print axioms resetJointMass
#check @resetJointMass_eq
#print axioms resetJointMass_eq
#check @resetJointLaw
#print axioms resetJointLaw
#check @resetOutputMass
#print axioms resetOutputMass
#check @resetStateMass
#print axioms resetStateMass
#check @resetOutputMass_total
#print axioms resetOutputMass_total
#check @resetJointLaw_product
#print axioms resetJointLaw_product
#check @reset_joint_information_zero
#print axioms reset_joint_information_zero
#check @reset_final_entropy_zero
#print axioms reset_final_entropy_zero
#check @silent_reset_control
#print axioms silent_reset_control

end

end OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions
