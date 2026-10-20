import OperatorKO7.Meta.BoundaryObserver.PersistentBinaryEvidence
import OperatorKO7.Meta.BoundaryObserver.PairResolution
import OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

/-!
# Actual reading cost for persistent decaying binary evidence

The information target is tested against the actual stopped law of a normalized
FiniteProtocol. The cost is the actual sum of its retained-history charges.
Relation: source-linked binary observations with history-dependent protocols.
Property: finite reading-cost growth under a positive acquired-information target.
External trust: none.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.PersistentBinaryCost

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.PersistentBinaryEvidence
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions
open Filter
open scoped Topology

noncomputable section

variable {A : Type} [Fintype A]

/-- The declared geometric signal family has the stated reciprocal-capacity price. -/
theorem geometric_price_identity (n : ℕ) (c : ℝ) :
    c / (4 * epsilon n ^ 2) = 4 * c * (4 : ℝ) ^ n := by
  have hden : 0 < 4 * epsilon n ^ 2 :=
    mul_pos (by norm_num) (pow_pos (epsilon_pos n) 2)
  have hscale : (4 * c * (4 : ℝ) ^ n) * (4 * epsilon n ^ 2) = c := by
    calc
      (4 * c * (4 : ℝ) ^ n) * (4 * epsilon n ^ 2) =
          16 * c * (epsilon n ^ 2 * (4 : ℝ) ^ n) := by ring
      _ = c := by
        rw [epsilon_sq_mul_four_pow]
        ring
  exact (div_eq_iff hden.ne').mpr hscale.symm

/-- Every actual finite protocol attaining a positive target pays the geometric reading price. -/
theorem finite_cost_lower (n : ℕ) (p : FiniteProtocol Bool A Bool)
    (menu : BinaryMenu p (epsilon n)) (horizon : ℕ)
    (bank : List (List (A × Bool))) (hb : HistoryBank horizon bank)
    (c : ℝ) (htarget : 0 < c ∧ c ≤ terminalMI p horizon bank) :
    4 * c * (4 : ℝ) ^ n ≤ expectedCost p horizon bank := by
  have h := binaryMenu_cost_lower_bound p (epsilon n) c menu
    (epsilon_pos n) (epsilon_le_half n) horizon bank hb htarget.2
  rw [geometric_price_identity] at h
  exact h

/-- The attained positive information target forces strictly positive actual reading cost. -/
theorem finite_cost_positive (n : ℕ) (p : FiniteProtocol Bool A Bool)
    (menu : BinaryMenu p (epsilon n)) (horizon : ℕ)
    (bank : List (List (A × Bool))) (hb : HistoryBank horizon bank)
    (c : ℝ) (htarget : 0 < c ∧ c ≤ terminalMI p horizon bank) :
    0 < expectedCost p horizon bank := by
  have hprice : 0 < 4 * c * (4 : ℝ) ^ n :=
    mul_pos (mul_pos (by norm_num) htarget.1) (pow_pos (by norm_num) n)
  exact hprice.trans_le (finite_cost_lower n p menu horizon bank hb c htarget)

/-- Acquisition of one fixed positive target at every state excludes a common finite cost budget. -/
theorem no_uniform_finite_budget (c : ℝ) (hc : 0 < c)
    (p : ℕ → FiniteProtocol Bool A Bool) (horizon : ℕ → ℕ)
    (menu : ∀ n, BinaryMenu (p n) (epsilon n))
    (hinfo : ∀ n, c ≤ terminalMI (p n) (horizon n) (historyBank A Bool (horizon n))) :
    ¬ ∃ budget : ℝ, ∀ n,
      expectedCost (p n) (horizon n) (historyBank A Bool (horizon n)) ≤ budget := by
  rintro ⟨budget, hbudget⟩
  have hcap (n : ℕ) : c ≤ (4 * epsilon n ^ 2) * budget := by
    have h := (binaryMenu_information_bound (p n) (epsilon n) (menu n)
      (epsilon_le_half n) (horizon n) (historyBank A Bool (horizon n))
      (historyBank_complete A Bool (horizon n))).2
    exact (hinfo n).trans (h.trans (mul_le_mul_of_nonneg_left (hbudget n)
      (mul_nonneg (by norm_num) (sq_nonneg (epsilon n)))))
  have hlim0 : Tendsto (fun n : ℕ => (4 * epsilon n ^ 2) * budget) atTop
      (𝓝 ((4 : ℝ) * (0 : ℝ) ^ 2 * budget)) :=
    (tendsto_const_nhds.mul (epsilon_tendsto_zero.pow 2)).mul tendsto_const_nhds
  have hlim : Tendsto (fun n : ℕ => (4 * epsilon n ^ 2) * budget) atTop (𝓝 (0 : ℝ)) := by
    simpa using hlim0
  have hremaining : Tendsto (fun n : ℕ => c - (4 * epsilon n ^ 2) * budget)
      atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.sub hlim
  have hnonpos : c ≤ 0 :=
    le_of_tendsto' hremaining (fun n => sub_nonpos.mpr (hcap n))
  exact (not_le_of_gt hc) hnonpos

/-! ## Source witnesses for positive attained targets -/

/-- The concrete protocol repeatedly reads the actual binary channel at its fixed state. -/
def readingProtocol (n : ℕ) : FiniteProtocol Bool Unit Bool :=
  binaryReadingProtocol (epsilon n) (epsilon_abs_le_half n)

/-- Every concrete reading uses the same normalized output row as the persistent evidence model. -/
theorem readingProtocol_source (n : ℕ) (h : List (Unit × Bool)) (a : Unit) (z y : Bool) :
    ((readingProtocol n).observation h a z).mass y = answer n z y := rfl

/-- The concrete reading protocol satisfies the state's positive binary-menu cap. -/
def readingProtocol_menu (n : ℕ) : BinaryMenu (readingProtocol n) (epsilon n) := by
  change BinaryMenu (binaryReadingProtocol (epsilon n) (epsilon_abs_le_half n)) (epsilon n)
  simpa only [abs_of_pos (epsilon_pos n)] using
    binaryReadingMenu (epsilon n) (epsilon_abs_le_half n)

/-- One retained reading realizes the actual fair binary joint law of the same state. -/
theorem readingProtocol_information_one (n : ℕ) :
    terminalMI (readingProtocol n) 1 (historyBank Unit Bool 1) =
      jointMI (fairJointLaw n).mass := by
  have h := binaryReading_information_one (epsilon n) (epsilon_abs_le_half n)
  rw [binaryReadingConditional, unitRecordProtocol_information] at h
  change terminalMI (binaryReadingProtocol (epsilon n) (epsilon_abs_le_half n)) 1
      (historyBank Unit Bool 1) = jointMI (binaryJoint (1 / 2) (epsilon n))
  exact h

/-- The actual information attained by one reading is positive at every finite state. -/
theorem readingProtocol_information_positive (n : ℕ) :
    0 < terminalMI (readingProtocol n) 1 (historyBank Unit Bool 1) := by
  rw [readingProtocol_information_one]
  exact fair_information_pos n

/-- One retained reading pays one unit under the concrete source protocol. -/
theorem readingProtocol_cost_one (n : ℕ) :
    expectedCost (readingProtocol n) 1 (historyBank Unit Bool 1) = 1 := by
  have h := binaryReading_cost_one (epsilon n) (epsilon_abs_le_half n)
  rw [binaryReadingConditional, unitRecordProtocol_cost] at h
  exact h

/-- Positive attained targets satisfy the geometric lower bound in the concrete source family. -/
theorem positive_target_control (n : ℕ) :
    0 < terminalMI (readingProtocol n) 1 (historyBank Unit Bool 1) ∧
      4 * terminalMI (readingProtocol n) 1 (historyBank Unit Bool 1) * (4 : ℝ) ^ n ≤
        expectedCost (readingProtocol n) 1 (historyBank Unit Bool 1) ∧
      expectedCost (readingProtocol n) 1 (historyBank Unit Bool 1) = 1 := by
  have hp := readingProtocol_information_positive n
  refine ⟨hp, ?_, readingProtocol_cost_one n⟩
  exact finite_cost_lower n (readingProtocol n) (readingProtocol_menu n) 1
    (historyBank Unit Bool 1) (historyBank_complete Unit Bool 1)
    (terminalMI (readingProtocol n) 1 (historyBank Unit Bool 1)) ⟨hp, le_rfl⟩

/-! ## Fixed-state repetitions and the actual optimal-cost infimum

The admissible set contains actual finite stopped protocols, including an
independent retained random seed. Every active observation uses the same
frozen state's output law and costs one.
-/

open PairResolution ResolutionAttainment
open scoped BigOperators

/-- Only the stated frozen-state channel is read; the fair target is fixed. -/
structure FrozenReading (n : ℕ) (p : FiniteProtocol Bool A Bool) : Prop where
  fair : p.prior.mass = binaryPrior (1 / 2)
  source : ∀ h a z y, (p.observation h a z).mass y = answer n z y
  unit_cost : ∀ h a, p.cost h a = 1

/-- The actual frozen reading is a binary menu, at every retained history. -/
def FrozenReading.menu {n : ℕ} {p : FiniteProtocol Bool A Bool}
    (h : FrozenReading n p) : BinaryMenu p (epsilon n) where
  bias _ _ := epsilon n
  bound _ _ := (abs_of_pos (epsilon_pos n)).le
  source hst a z y := h.source hst a z y
  reading_cost hst a := (h.unit_cost hst a).ge

/-- A positive-weight initial record may select policy randomness, never a different target law. -/
def FrozenExperiment {H0 : Type} [Fintype H0] (n : ℕ)
    (p : ConditionalProtocol H0 Bool A Bool) : Prop :=
  ∀ u, 0 < p.initialRecord.mass u → FrozenReading n (p.given u)

/-- Attainment is tested against the actual stopped information and paid cost. -/
def attainedFrozenCost (H0 B : Type) [Fintype H0] [Fintype B]
    (n : ℕ) (c r : ℝ) : Prop :=
  ∃ (p : ConditionalProtocol H0 Bool B Bool) (N : ℕ),
    FrozenExperiment n p ∧
      c ≤ conditionalJointInfo p N (historyBank B Bool N) ∧
      r = conditionalExpectedCost p N (historyBank B Bool N)

/-- All finite action alphabets and finite independent initial seeds are admitted. -/
def frozenCosts (n : ℕ) (c : ℝ) : Set ℝ :=
  {r | ∃ (H0 B : Type) (hH0 : Fintype H0) (hB : Fintype B),
    @attainedFrozenCost H0 B hH0 hB n c r}

/-- The manuscript's K_n(c), formed from actual attaining protocols. -/
def optimalFrozenCost (n : ℕ) (c : ℝ) : ℝ := sInf (frozenCosts n c)

theorem frozenCost_nonnegative (n : ℕ) (c : ℝ) {r : ℝ}
    (hr : r ∈ frozenCosts n c) : 0 ≤ r := by
  obtain ⟨H0, B, hH0, hB, p, N, _, _, rfl⟩ := hr
  letI := hH0
  letI := hB
  exact conditionalExpectedCost_nonnegative p N _ (historyBank_complete B Bool N)

theorem frozenCosts_bddBelow (n : ℕ) (c : ℝ) : BddBelow (frozenCosts n c) :=
  ⟨0, fun _ hr => frozenCost_nonnegative n c hr⟩

/-- The lower bound covers all admissible randomization and stopping policies. -/
theorem frozenCost_ge_geometric (n : ℕ) (c : ℝ) {r : ℝ}
    (hr : r ∈ frozenCosts n c) : 4 * c * (4 : ℝ) ^ n ≤ r := by
  obtain ⟨H0, B, hH0, hB, p, N, hp, hc, rfl⟩ := hr
  letI := hH0
  letI := hB
  have h := conditional_binaryMenu_cost_lower_bound p (epsilon n) c
    (fun u hu => (hp u hu).menu) (epsilon_pos n) (epsilon_le_half n)
    N _ (historyBank_complete B Bool N) hc
  rwa [geometric_price_identity] at h

/-- The concrete repetition uses exactly the two rows of the fixed-state answer map. -/
def frozenRepeat (n N : ℕ) : FiniteProtocol Bool Unit Bool :=
  repeatProtocol
    (binaryKernelLaw (epsilon n) (epsilon_abs_le_half n) true)
    (binaryKernelLaw (epsilon n) (epsilon_abs_le_half n) false) N

theorem frozenRepeat_frozen (n N : ℕ) : FrozenReading n (frozenRepeat n N) := by
  constructor
  · funext b
    cases b <;> norm_num [frozenRepeat, repeatProtocol, fairLaw, binaryPrior]
  · intro h a z y
    cases z <;> rfl
  · intro h a
    rfl

theorem frozenRepeat_discrimination (n : ℕ) :
    BoundarySingularity.discrimination
      (binaryKernelLaw (epsilon n) (epsilon_abs_le_half n) true).mass
      (binaryKernelLaw (epsilon n) (epsilon_abs_le_half n) false).mass =
        PersistentBinaryEvidence.discrimination n := by
  change BoundarySingularity.discrimination (binaryKernel (epsilon n) true)
    (binaryKernel (epsilon n) false) = _
  rw [BoundarySingularity.discrimination_binaryKernel,
    PersistentBinaryEvidence.discrimination_eq_eight_mul_sq]

def frozenRepeatCount (n : ℕ) (η : ℝ) : ℕ :=
  ⌈4 * Real.log (1 / (2 * η)) / PersistentBinaryEvidence.discrimination n⌉₊

/-- The prescribed ceiling number of repetitions attains the fixed information target. -/
theorem frozenRepeat_attainment (n : ℕ) (c η : ℝ)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hentropy : Real.binEntropy η / Real.log 2 ≤ 1 - c) :
    ((frozenRepeatCount n η : ℕ) : ℝ) ∈ frozenCosts n c ∧
      ((frozenRepeatCount n η : ℕ) : ℝ) ≤
        4 * Real.log (1 / (2 * η)) /
          PersistentBinaryEvidence.discrimination n + 1 := by
  let P := binaryKernelLaw (epsilon n) (epsilon_abs_le_half n) true
  let Q := binaryKernelLaw (epsilon n) (epsilon_abs_le_half n) false
  have hd : 0 < BoundarySingularity.discrimination P.mass Q.mass := by
    rw [frozenRepeat_discrimination]
    exact PersistentBinaryEvidence.discrimination_pos n
  have ht := repeat_target P Q hd η hη0 hη1
  rw [frozenRepeat_discrimination] at ht
  change 1 - Real.binEntropy η / Real.log 2 ≤
      terminalMI (frozenRepeat n (frozenRepeatCount n η)) (frozenRepeatCount n η)
        (historyBank Unit Bool (frozenRepeatCount n η)) ∧ _ at ht
  refine ⟨?_, ht.2.2⟩
  refine ⟨Unit, Unit, inferInstance, inferInstance,
    unitRecordProtocol (frozenRepeat n (frozenRepeatCount n η)),
    frozenRepeatCount n η, ?_, ?_, ?_⟩
  · intro u _
    exact frozenRepeat_frozen n _
  · rw [unitRecordProtocol_information]
    linarith [ht.1]
  · rw [unitRecordProtocol_cost]
    exact ht.2.1.symm

/-- A positive error tolerance meeting any target below one bit exists by continuity. -/
theorem exists_error_tolerance (c : ℝ) (hc : c < 1) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
      Real.binEntropy η / Real.log 2 ≤ 1 - c := by
  have hlim : Tendsto (fun k : ℕ => Real.binEntropy (epsilon k) / Real.log 2)
      atTop (𝓝 0) := by
    simpa using ((Real.binEntropy_continuous.tendsto 0).comp epsilon_tendsto_zero).div_const
      (Real.log 2)
  have hev : ∀ᶠ k : ℕ in atTop,
      Real.binEntropy (epsilon k) / Real.log 2 < 1 - c :=
    (tendsto_order.1 hlim).2 (1 - c) (sub_pos.mpr hc)
  obtain ⟨k, hk⟩ := hev.exists
  exact ⟨epsilon k, epsilon_pos k, (epsilon_le_quarter k).trans_lt (by norm_num), hk.le⟩

theorem frozenCosts_nonempty (n : ℕ) (c : ℝ) (hc : c < 1) :
    (frozenCosts n c).Nonempty := by
  obtain ⟨η, hη0, hη1, he⟩ := exists_error_tolerance c hc
  exact ⟨_, (frozenRepeat_attainment n c η hη0 hη1.le he).1⟩

/-- Passing to the infimum retains the lower bound for actual attaining experiments. -/
theorem optimalFrozenCost_lower (n : ℕ) (c : ℝ) (hc : c < 1) :
    4 * c * (4 : ℝ) ^ n ≤ optimalFrozenCost n c :=
  le_csInf (frozenCosts_nonempty n c hc) (fun _ hr => frozenCost_ge_geometric n c hr)

/-- The explicit repetition protocol bounds the same infimum from above. -/
theorem optimalFrozenCost_upper (n : ℕ) (c η : ℝ)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (he : Real.binEntropy η / Real.log 2 ≤ 1 - c) :
    optimalFrozenCost n c ≤ frozenRepeatCount n η :=
  csInf_le (frozenCosts_bddBelow n c) (frozenRepeat_attainment n c η hη0 hη1 he).1

theorem frozen_repeat_geometric_price (n : ℕ) (η : ℝ) :
    4 * Real.log (1 / (2 * η)) / PersistentBinaryEvidence.discrimination n =
      8 * Real.log (1 / (2 * η)) * (4 : ℝ) ^ n := by
  rw [PersistentBinaryEvidence.discrimination_eq_eight_mul_sq]
  have h := geometric_price_identity n (2 * Real.log (1 / (2 * η)))
  have hε : epsilon n ≠ 0 := (epsilon_pos n).ne'
  convert h using 1 <;> field_simp [hε] <;> ring

/-- The full two-sided 4^n growth holds uniformly over every frozen state. -/
theorem optimalFrozenCost_two_sided (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ n : ℕ,
      a * (4 : ℝ) ^ n ≤ optimalFrozenCost n c ∧
        optimalFrozenCost n c ≤ b * (4 : ℝ) ^ n + 1 := by
  obtain ⟨η, hη0, hη1, he⟩ := exists_error_tolerance c hc1
  have hlog : 0 < Real.log (1 / (2 * η)) := by
    apply Real.log_pos
    apply (lt_div_iff₀ (by positivity : 0 < 2 * η)).mpr
    linarith
  refine ⟨4 * c, 8 * Real.log (1 / (2 * η)), by positivity, by positivity, ?_⟩
  intro n
  refine ⟨optimalFrozenCost_lower n c hc1, ?_⟩
  have hu := (optimalFrozenCost_upper n c η hη0 hη1.le he).trans
    (frozenRepeat_attainment n c η hη0 hη1.le he).2
  rwa [frozen_repeat_geometric_price] at hu

#check @FrozenReading
#print axioms FrozenReading
#check @FrozenReading.menu
#print axioms FrozenReading.menu
#check @FrozenExperiment
#print axioms FrozenExperiment
#check @attainedFrozenCost
#print axioms attainedFrozenCost
#check @frozenCosts
#print axioms frozenCosts
#check @optimalFrozenCost
#print axioms optimalFrozenCost
#check @frozenCost_nonnegative
#print axioms frozenCost_nonnegative
#check @frozenCosts_bddBelow
#print axioms frozenCosts_bddBelow
#check @frozenCost_ge_geometric
#print axioms frozenCost_ge_geometric
#check @frozenRepeat
#print axioms frozenRepeat
#check @frozenRepeat_frozen
#print axioms frozenRepeat_frozen
#check @frozenRepeat_discrimination
#print axioms frozenRepeat_discrimination
#check @frozenRepeatCount
#print axioms frozenRepeatCount
#check @frozenRepeat_attainment
#print axioms frozenRepeat_attainment
#check @exists_error_tolerance
#print axioms exists_error_tolerance
#check @frozenCosts_nonempty
#print axioms frozenCosts_nonempty
#check @optimalFrozenCost_lower
#print axioms optimalFrozenCost_lower
#check @optimalFrozenCost_upper
#print axioms optimalFrozenCost_upper
#check @frozen_repeat_geometric_price
#print axioms frozen_repeat_geometric_price
#check @optimalFrozenCost_two_sided
#print axioms optimalFrozenCost_two_sided

end

end OperatorKO7.Meta.BoundaryObserver.PersistentBinaryCost
