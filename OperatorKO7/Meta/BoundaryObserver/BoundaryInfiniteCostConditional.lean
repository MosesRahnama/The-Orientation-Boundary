import OperatorKO7.Meta.BoundaryObserver.ErasurePriorCompletion
import OperatorKO7.Meta.BoundaryObserver.BoundaryInfiniteCost
import OperatorKO7.Meta.BoundaryObserver.SeedFrontier

set_option autoImplicit false

/-!
# Conditional retained-record boundary and limiting cost

Every branch uses the original stopped law. Zero-information
claims require no unit charge; positive-cost comparisons retain it.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryInfiniteCostConditional

open scoped BigOperators ENNReal
open Filter Topology ProtocolResolution TranscriptLaw ErasureReading
open ErasurePriorCompletion BoundaryInfiniteCost BoundaryPole
open BoundaryThreeGeneral PairResolution MergedPair SeedFrontier

noncomputable section

/-! ## Independent retained seed and arbitrary-prior exclusive readings -/

/-- A normalized retained seed independent of the label. Every conditional
branch is the original first-exclusive repeated-reading protocol. -/
def independentExclusiveSeed {H0 Y : Type} [Fintype H0] [Fintype Y]
    (ν : FiniteLaw H0) (μ : FiniteLaw Bool) (P Q : FiniteLaw Y) :
    ConditionalProtocol H0 Bool Unit Y where
  initialRecord := ν
  initialJoint := {
    mass := fun uz => ν.mass uz.1 * μ.mass uz.2
    nonnegative := fun uz => mul_nonneg (ν.nonnegative uz.1) (μ.nonnegative uz.2)
    total := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, μ.total, mul_one]
      exact ν.total
  }
  given _ := firstExclusiveWith μ P Q
  initial_joint _ _ := rfl

theorem independentExclusiveSeed_joint {H0 Y : Type} [Fintype H0] [Fintype Y]
    (ν : FiniteLaw H0) (μ : FiniteLaw Bool) (P Q : FiniteLaw Y) (u : H0) (z : Bool) :
    (independentExclusiveSeed ν μ P Q).initialJoint.mass (u, z) =
      ν.mass u * μ.mass z := rfl

theorem independentExclusiveSeed_branch_survival {H0 Y : Type} [Fintype H0] [Fintype Y]
    (ν : FiniteLaw H0) (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (u : H0) (n : ℕ) :
    activeMass ((independentExclusiveSeed ν μ P Q).given u) n true =
        μ.mass true * (1 - exclusiveMass P Q) ^ n ∧
      activeMass ((independentExclusiveSeed ν μ P Q).given u) n false =
        μ.mass false * (1 - exclusiveMass Q P) ^ n :=
  firstExclusiveWith_survival_law μ P Q n

/-- Both strict exclusive probabilities ensure stopping on every supported
branch and label, without an assumption about impossible seed values. -/
theorem independentExclusiveSeed_positive_stopping
    {H0 Y : Type} [Fintype H0] [Fintype Y]
    (ν : FiniteLaw H0) (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (ha : 0 < exclusiveMass P Q) (hb : 0 < exclusiveMass Q P) :
    PositiveBranchStopping (independentExclusiveSeed ν μ P Q) := by
  intro u z _ _
  change Tendsto (fun n => activeMass (firstExclusiveWith μ P Q) n z) atTop (𝓝 0)
  cases z with
  | false => exact firstExclusiveWith_stops μ P Q false hb
  | true => exact firstExclusiveWith_stops μ P Q true ha

/-- The independent seed preserves the exact entropy of the binary source. -/
theorem independentExclusiveSeed_limit_information
    {H0 Y : Type} [Fintype H0] [Fintype Y]
    (ν : FiniteLaw H0) (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (ha : 0 < exclusiveMass P Q) (hb : 0 < exclusiveMass Q P) :
    conditionalInformationLimit (independentExclusiveSeed ν μ P Q) =
      entropy μ.mass := by
  change (∑ u : H0, ν.mass u * informationLimit (firstExclusiveWith μ P Q)) =
    entropy μ.mass
  rw [firstExclusiveWith_information μ P Q
    (fun z _ => by cases z with | false => exact hb | true => exact ha)]
  rw [← Finset.sum_mul, ν.total, one_mul]

/-- The same limit equals information of the normalized countable stopped
law, including correct treatment of initial records of zero mass. -/
theorem independentExclusiveSeed_countable_information
    {H0 Y : Type} [Fintype H0] [Fintype Y]
    (ν : FiniteLaw H0) (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (ha : 0 < exclusiveMass P Q) (hb : 0 < exclusiveMass Q P) :
    conditionalCountableTranscriptInformation (independentExclusiveSeed ν μ P Q)
        (independentExclusiveSeed_positive_stopping ν μ P Q ha hb) =
      entropy μ.mass := by
  rw [← conditionalInformationLimit_eq_countable_of_positive
    (independentExclusiveSeed ν μ P Q)
    (independentExclusiveSeed_positive_stopping ν μ P Q ha hb)]
  exact independentExclusiveSeed_limit_information ν μ P Q ha hb

/-- The exact expected cost is w/a+(1-w)/b after averaging an independent
finite seed. No second notion of cost is introduced. -/
theorem independentExclusiveSeed_exact_cost
    {H0 Y : Type} [Fintype H0] [Fintype Y]
    (ν : FiniteLaw H0) (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (ha : 0 < exclusiveMass P Q) (hb : 0 < exclusiveMass Q P) :
    conditionalExtendedCost (independentExclusiveSeed ν μ P Q) =
      ENNReal.ofReal
        (μ.mass true / exclusiveMass P Q +
          (1 - μ.mass true) / exclusiveMass Q P) := by
  change (∑ u : H0, ENNReal.ofReal (ν.mass u) *
      extendedCost (firstExclusiveWith μ P Q)) = _
  rw [← Finset.sum_mul]
  have htotal : (∑ u : H0, ENNReal.ofReal (ν.mass u)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => ν.nonnegative u),
      ν.total]
    norm_num
  rw [htotal, one_mul]
  exact firstExclusiveWith_weighted_cost μ P Q ha hb

/-- Binary outcomes yield at most one bit per unit of positive cost at
the actual information limit, for any finite target alphabet. -/
theorem binary_output_limiting_information_le_cost
    {Z A : Type} [Fintype Z] [Fintype A]
    (p : FiniteProtocol Z A Bool) (hcost : ∀ h a, 1 ≤ p.cost h a) :
    ENNReal.ofReal (informationLimit p) ≤ extendedCost p := by
  simpa only [ENNReal.ofReal_one, one_mul] using
    informationLimit_le_extendedCost p 1 zero_le_one
      (binary_output_capacity p hcost)

/-- The initial-record conditional limit has the same sharp binary-output
cost bound, with the charge premise only at positive-mass records. -/
theorem conditional_binary_output_limiting_information_le_cost
    {H0 Z A : Type} [Fintype H0] [Fintype Z] [Fintype A]
    (p : ConditionalProtocol H0 Z A Bool)
    (hcost : ∀ u, 0 < p.initialRecord.mass u →
      ∀ h a, 1 ≤ (p.given u).cost h a) :
    ENNReal.ofReal (conditionalInformationLimit p) ≤ conditionalExtendedCost p := by
  simpa only [ENNReal.ofReal_one, one_mul] using
    conditionalInformationLimit_le_extendedCost p 1 zero_le_one
      (fun u hu => binary_output_capacity (p.given u) (hcost u hu))

/-! ## Conditional merged-pair blindness -/

/-- A merged pair supplies no new conditional information at any initial
record, even with correlated initial records and arbitrary reading charges. -/
theorem conditional_record_blind_of_merged
    {X Q H0 A Y : Type} [Fintype H0] [Fintype A] [Fintype Y]
    (q : X → Q) {x₀ x₁ : X} (hm : IsMergedPair q x₀ x₁)
    (p : ConditionalProtocol H0 Bool A Y)
    (K : H0 → List (A × Y) → A → Reading X Y)
    (hdet : ∀ u h a, RecordDetermined q (K u h a))
    (hobs : ∀ u h a b, (p.given u).observation h a b =
      K u h a (pairState x₀ x₁ b)) :
    (∀ n bank, HistoryBank n bank → conditionalMI p n bank = 0) ∧
      conditionalInformationLimit p = 0 := by
  have hbranch (u : H0) :=
    recordProtocol_blind_of_merged q hm A Y (p.given u) (K u)
      (hdet u) (hobs u)
  constructor
  · intro n bank hb
    unfold conditionalMI
    apply Finset.sum_eq_zero
    intro u _
    rw [(hbranch u).1 n bank hb, mul_zero]
  · unfold conditionalInformationLimit
    apply Finset.sum_eq_zero
    intro u _
    rw [(hbranch u).2, mul_zero]

/-! ## A split-pair record indicator with an independent retained seed -/

/-- Every seed value executes the actual one-reading indicatorProtocol.
The label is fair and independent of this normalized finite seed. -/
def conditionalIndicatorProtocol {X Q H0 : Type} [Fintype H0]
    (ν : FiniteLaw H0) (q : X → Q) (x₀ x₁ : X) :
    ConditionalProtocol H0 Bool Unit Bool where
  initialRecord := ν
  initialJoint := {
    mass := fun uz => ν.mass uz.1 * ResolutionAttainment.fairLaw.mass uz.2
    nonnegative := fun uz => mul_nonneg (ν.nonnegative uz.1)
      (ResolutionAttainment.fairLaw.nonnegative uz.2)
    total := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ResolutionAttainment.fairLaw.total, mul_one]
      exact ν.total
  }
  given _ := indicatorProtocol q x₀ x₁
  initial_joint _ _ := rfl

theorem conditionalIndicatorProtocol_independent {X Q H0 : Type} [Fintype H0]
    (ν : FiniteLaw H0) (q : X → Q) (x₀ x₁ : X) (u : H0) (z : Bool) :
    (conditionalIndicatorProtocol ν q x₀ x₁).initialJoint.mass (u, z) =
      ν.mass u * ResolutionAttainment.fairLaw.mass z := rfl

/-- The donor's bound is exact because the source prior has one bit. -/
theorem indicatorProtocol_split_exact_information {X Q : Type}
    (q : X → Q) {x₀ x₁ : X} (hq : q x₀ ≠ q x₁) :
    terminalMI (indicatorProtocol q x₀ x₁) 1 (historyBank Unit Bool 1) = 1 := by
  have hlow := (indicator_protocol_split q hq).2.2.2.2.1
  have hu := terminalMI_le_prior_entropy
    (indicatorProtocol q x₀ x₁) 1 (historyBank Unit Bool 1)
    (historyBank_complete Unit Bool 1)
  have he : entropy (indicatorProtocol q x₀ x₁).prior.mass = 1 := by
    change entropy ResolutionAttainment.fairLaw.mass = 1
    exact ResolutionAttainment.fairLaw_entropy
  exact le_antisymm (hu.trans_eq he) hlow

/-- Every independent seed gives exactly one conditional bit at horizon one. -/
theorem conditionalIndicator_split_information
    {X Q H0 : Type} [Fintype H0]
    (ν : FiniteLaw H0) (q : X → Q) {x₀ x₁ : X}
    (hq : q x₀ ≠ q x₁) :
    conditionalMI (conditionalIndicatorProtocol ν q x₀ x₁)
      1 (historyBank Unit Bool 1) = 1 := by
  change (∑ u : H0, ν.mass u *
    terminalMI (indicatorProtocol q x₀ x₁) 1 (historyBank Unit Bool 1)) = 1
  rw [indicatorProtocol_split_exact_information q hq]
  simp only [mul_one, ν.total]

/-- Every independent seed gives exactly one expected unit of charge. -/
theorem conditionalIndicator_split_cost
    {X Q H0 : Type} [Fintype H0]
    (ν : FiniteLaw H0) (q : X → Q) {x₀ x₁ : X}
    (hq : q x₀ ≠ q x₁) :
    conditionalExpectedCost (conditionalIndicatorProtocol ν q x₀ x₁)
      1 (historyBank Unit Bool 1) = 1 := by
  obtain ⟨_, _, _, _, _, hpaid⟩ := indicator_protocol_split q hq
  change (∑ u : H0, ν.mass u *
    expectedCost (indicatorProtocol q x₀ x₁) 1 (historyBank Unit Bool 1)) = 1
  rw [hpaid]
  simp only [mul_one, ν.total]

/-- The one-bit finite witness reaches exactly the one-bit limit. -/
theorem indicatorProtocol_split_exact_limit_information {X Q : Type}
    (q : X → Q) {x₀ x₁ : X} (hq : q x₀ ≠ q x₁) :
    informationLimit (indicatorProtocol q x₀ x₁) = 1 := by
  have hlow : 1 ≤ informationLimit (indicatorProtocol q x₀ x₁) :=
    (indicatorProtocol_split_exact_information q hq).ge.trans
      (terminalMI_le_informationLimit (indicatorProtocol q x₀ x₁) 1)
  have hu := informationLimit_le_prior_entropy (indicatorProtocol q x₀ x₁)
  have he : entropy (indicatorProtocol q x₀ x₁).prior.mass = 1 := by
    change entropy ResolutionAttainment.fairLaw.mass = 1
    exact ResolutionAttainment.fairLaw_entropy
  exact le_antisymm (hu.trans_eq he) hlow

theorem conditionalIndicator_split_limit_information
    {X Q H0 : Type} [Fintype H0]
    (ν : FiniteLaw H0) (q : X → Q) {x₀ x₁ : X}
    (hq : q x₀ ≠ q x₁) :
    conditionalInformationLimit (conditionalIndicatorProtocol ν q x₀ x₁) = 1 := by
  change (∑ u : H0, ν.mass u *
    informationLimit (indicatorProtocol q x₀ x₁)) = 1
  rw [indicatorProtocol_split_exact_limit_information q hq]
  simp only [mul_one, ν.total]

/-! ## Conditional boundary equivalence with an actual split witness -/

/-- Distinct pairs are merged precisely if every adaptive retained-record
protocol whose conditional readings factor through the record has zero
acquired information, both at every finite horizon and in the limit. -/
theorem boundary_iff_conditional_blind
    {X Q : Type} (q : X → Q) {x₀ x₁ : X} (hne : x₀ ≠ x₁) :
    IsMergedPair q x₀ x₁ ↔
      ∀ (H0 A Y : Type) [Fintype H0] [Fintype A] [Fintype Y]
        (p : ConditionalProtocol H0 Bool A Y)
        (K : H0 → List (A × Y) → A → Reading X Y),
        (∀ u h a, RecordDetermined q (K u h a)) →
        (∀ u h a b, (p.given u).observation h a b =
          K u h a (pairState x₀ x₁ b)) →
        (∀ n bank, HistoryBank n bank → conditionalMI p n bank = 0) ∧
          conditionalInformationLimit p = 0 := by
  constructor
  · intro hm H0 A Y _ _ _ p K hdet hobs
    exact conditional_record_blind_of_merged q hm p K hdet hobs
  · intro hall
    refine ⟨hne, ?_⟩
    by_contra hq
    let ν : FiniteLaw Unit := unitLaw
    have hz := (hall Unit Unit Bool (conditionalIndicatorProtocol ν q x₀ x₁)
      (fun _ _ _ => indicatorReading q x₀)
      (fun _ _ _ => indicatorReading_recordDetermined q x₀)
      (fun _ h a b => indicatorProtocol_observation q x₀ x₁ h a b)).1
        1 (historyBank Unit Bool 1) (historyBank_complete Unit Bool 1)
    rw [conditionalIndicator_split_information ν q hq] at hz
    norm_num at hz

/-- For every positive target no greater than one bit, a merged pair is
exactly the failure of all finite and limiting retained-record protocols
with unit-or-higher reading cost to attain that target. Only the positive
target comparison, not the zero-capacity proof, uses the cost premise. -/
theorem boundary_iff_conditional_positive_target_infeasible
    {X Q : Type} (q : X → Q) {x₀ x₁ : X}
    (hne : x₀ ≠ x₁) (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    IsMergedPair q x₀ x₁ ↔
      ∀ (H0 A Y : Type) [Fintype H0] [Fintype A] [Fintype Y]
        (p : ConditionalProtocol H0 Bool A Y)
        (K : H0 → List (A × Y) → A → Reading X Y),
        (∀ u h a, RecordDetermined q (K u h a)) →
        (∀ u h a b, (p.given u).observation h a b =
          K u h a (pairState x₀ x₁ b)) →
        (∀ u, 0 < p.initialRecord.mass u →
          ∀ h a, 1 ≤ (p.given u).cost h a) →
        (∀ n bank, HistoryBank n bank → conditionalMI p n bank < c) ∧
          conditionalInformationLimit p < c := by
  constructor
  · intro hm H0 A Y _ _ _ p K hdet hobs _
    obtain ⟨hzero, hlim⟩ := conditional_record_blind_of_merged q hm p K hdet hobs
    constructor
    · intro n bank hb
      rw [hzero n bank hb]
      exact hc0
    · rw [hlim]
      exact hc0
  · intro hall
    refine ⟨hne, ?_⟩
    by_contra hq
    let ν : FiniteLaw Unit := unitLaw
    have hdet : ∀ (u : Unit) (h : List (Unit × Bool)) (a : Unit),
        RecordDetermined q (indicatorReading q x₀) :=
      fun _ _ _ => indicatorReading_recordDetermined q x₀
    have hobs : ∀ (u : Unit) (h : List (Unit × Bool)) (a : Unit) (b : Bool),
        ((conditionalIndicatorProtocol ν q x₀ x₁).given u).observation h a b =
          indicatorReading q x₀ (pairState x₀ x₁ b) :=
      fun _ h a b => indicatorProtocol_observation q x₀ x₁ h a b
    have hcost : ∀ u, 0 <
        (conditionalIndicatorProtocol ν q x₀ x₁).initialRecord.mass u →
        ∀ h a, 1 ≤ ((conditionalIndicatorProtocol ν q x₀ x₁).given u).cost h a :=
      fun _ _ _ _ => le_rfl
    have hlt := (hall Unit Unit Bool (conditionalIndicatorProtocol ν q x₀ x₁)
      (fun _ _ _ => indicatorReading q x₀) hdet hobs hcost).1
      1 (historyBank Unit Bool 1) (historyBank_complete Unit Bool 1)
    rw [conditionalIndicator_split_information ν q hq] at hlt
    linarith

/-! ## Disjoint supports: one reading is enough -/

variable {Y : Type} [Fintype Y]

/-- If no outcome is positive under both laws, every P-positive outcome
is exclusive to P and the whole P-law is exclusive. -/
theorem exclusiveMass_eq_one_of_disjoint
    (P Q : FiniteLaw Y) (h : ∀ y, P.mass y = 0 ∨ Q.mass y = 0) :
    exclusiveMass P Q = 1 := by
  unfold exclusiveMass
  calc
    (∑ y, if Q.mass y = 0 then P.mass y else 0) = ∑ y, P.mass y := by
      apply Finset.sum_congr rfl
      intro y _
      rcases h y with hp | hq
      · by_cases hq' : Q.mass y = 0 <;> simp [hp, hq']
      · simp [hq]
    _ = 1 := P.total

theorem reverse_exclusiveMass_eq_one_of_disjoint
    (P Q : FiniteLaw Y) (h : ∀ y, P.mass y = 0 ∨ Q.mass y = 0) :
    exclusiveMass Q P = 1 :=
  exclusiveMass_eq_one_of_disjoint Q P (fun y => Or.elim (h y) Or.inr Or.inl)

/-- The very same first-exclusive protocol needs no second reading for
disjoint rows. It stops after the first sample under every binary prior. -/
theorem disjoint_firstExclusiveWith_one_reading
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (h : ∀ y, P.mass y = 0 ∨ Q.mass y = 0) :
    (∀ z, activeMass (firstExclusiveWith μ P Q) 1 z = 0) ∧
    ZeroError (firstExclusiveWith μ P Q) (firstExclusiveDecoder Q) ∧
    informationLimit (firstExclusiveWith μ P Q) = entropy μ.mass ∧
    extendedCost (firstExclusiveWith μ P Q) = ENNReal.ofReal 1 ∧
    expectedCost (firstExclusiveWith μ P Q) 1 (historyBank Unit Y 1) = 1 := by
  have ha1 := exclusiveMass_eq_one_of_disjoint P Q h
  have hb1 := reverse_exclusiveMass_eq_one_of_disjoint P Q h
  have ha : 0 < exclusiveMass P Q := by rw [ha1]; norm_num
  have hb : 0 < exclusiveMass Q P := by rw [hb1]; norm_num
  refine ⟨?_, (fun z h hw => firstExclusiveWith_zero_error μ P Q z h hw),
    firstExclusiveWith_information μ P Q
      (fun z _ => by cases z with | false => exact hb | true => exact ha),
    ?_, ?_⟩
  · intro z
    rw [firstExclusiveWith_activeMass]
    cases z <;> simp [labelExclusive_true, labelExclusive_false, ha1, hb1]
  · simpa [ha1, hb1] using firstExclusiveWith_weighted_cost μ P Q ha hb
  · rw [firstExclusiveWith_expectedCost_at]
    simp only [Finset.sum_range_one, pow_zero, mul_one]
    exact μ.total

/-- A Boolean target has zero active uncertainty as soon as every target
has zero active mass; this is an actual stopped-law equality. -/
theorem activeUncertainty_zero_of_activeMass_zero
    (p : FiniteProtocol Bool Unit Y) (n : ℕ)
    (hzero : ∀ z, activeMass p n z = 0) :
    activeUncertainty p n = 0 := by
  have hbound := activeUncertainty_le_activeMass p n
  have hsum : (∑ z : Bool, activeMass p n z) = 0 := by
    simp [hzero]
  rw [hsum, zero_mul] at hbound
  exact le_antisymm hbound (activeUncertainty_nonneg p n)

/-- The disjoint-row first reading already acquires the entire prior entropy,
not merely as the limit of later horizon informations. -/
theorem disjoint_firstExclusiveWith_finite_information
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (h : ∀ y, P.mass y = 0 ∨ Q.mass y = 0) :
    terminalMI (firstExclusiveWith μ P Q) 1 (historyBank Unit Y 1) =
      entropy μ.mass := by
  rw [terminalMI_eq_transcript_sub_active]
  simp_rw [firstExclusiveWith_transcript_uncertainty_zero μ P Q]
  have hz := (disjoint_firstExclusiveWith_one_reading μ P Q h).1
  rw [activeUncertainty_zero_of_activeMass_zero (firstExclusiveWith μ P Q) 1 hz]
  simp
  rfl

/-! ## The existing Bernoulli-seeded perfect reading at its true limit -/

/-- The seed-true branch has exactly one bit in the limiting law, because
one real reading supplies one bit and no binary prior exceeds one bit. -/
theorem seedBranch_true_limit_information :
    informationLimit (seedBranch true) = 1 := by
  have hlo : 1 ≤ informationLimit (seedBranch true) :=
    seedBranch_true_information.ge.trans
      (terminalMI_le_informationLimit (seedBranch true) 1)
  have hm : (seedBranch true).prior.mass true +
      (seedBranch true).prior.mass false = 1 := by
    simpa only [Fintype.sum_bool] using (seedBranch true).prior.total
  exact le_antisymm
    ((informationLimit_le_prior_entropy (seedBranch true)).trans
      (entropy_bool_le_one (seedBranch true).prior.mass hm)) hlo

/-- The zero-reading branch has no information at any horizon or limit. -/
theorem seedBranch_false_limit_information :
    informationLimit (seedBranch false) = 0 := by
  apply le_antisymm _ (informationLimit_nonnegative (seedBranch false))
  apply ciSup_le
  intro n
  exact (seedBranch_false_information n (historyBank Unit Bool n)
    (historyBank_complete Unit Bool n)).le

/-- The original seed-true protocol is charged at the empty history and
never charged at a later, already stopped history. -/
theorem seedBranch_true_historyCost (h : List (Unit × Bool)) :
    historyCost (seedBranch true) h = if h = [] then 1 else 0 := by
  cases h with
  | nil =>
    simp [historyCost, seedBranch, historyMass, prefixMass_nil,
      fairLabel, binaryPriorLaw, binaryPrior, unitLaw]
  | cons x xs =>
    simp [historyCost, seedBranch]

/-- The true branch pays exactly one unit over the whole countable stopped
law, not merely at horizon one. -/
theorem seedBranch_true_extendedCost :
    extendedCost (seedBranch true) = ENNReal.ofReal 1 := by
  rw [extendedCost_eq_tsum_historyCost]
  have heq : (fun h : List (Unit × Bool) =>
      ENNReal.ofReal (historyCost (seedBranch true) h)) =
      fun h => if h = [] then ENNReal.ofReal 1 else 0 := by
    funext h
    rw [seedBranch_true_historyCost]
    split_ifs <;> simp
  rw [heq]
  simp

/-- The seed-false branch takes no reading, and its countable total cost is zero. -/
theorem seedBranch_false_extendedCost :
    extendedCost (seedBranch false) = 0 := by
  unfold extendedCost
  simp [seedBranch_false_cost]

/-- The old seeded protocol, unchanged, acquires exactly c bits in the
limit; the conditional initial-record law is the one already constructed. -/
theorem seedProtocol_limit_information (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    conditionalInformationLimit (seedProtocol c hc0 hc1) = c := by
  change (∑ u : Bool, binaryPrior c u * informationLimit (seedBranch u)) = c
  rw [Fintype.sum_bool, seedBranch_true_limit_information,
    seedBranch_false_limit_information]
  simp [binaryPrior]

/-- The same seed protocol has total expected cost c, with exact
conditioning on the initial record and no invented cost coordinate. -/
theorem seedProtocol_extendedCost (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    conditionalExtendedCost (seedProtocol c hc0 hc1) = ENNReal.ofReal c := by
  change (∑ u : Bool, ENNReal.ofReal (binaryPrior c u) *
    extendedCost (seedBranch u)) = ENNReal.ofReal c
  rw [Fintype.sum_bool, seedBranch_true_extendedCost,
    seedBranch_false_extendedCost]
  simp [binaryPrior]

/-- Exact finite and limiting seeded-frontier attainment plus a limiting
lower bound for every conditional binary-output protocol with positive
record branches of unit-or-higher cost. -/
theorem seeded_finite_limiting_frontier (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (∃ p : ConditionalProtocol Bool Bool Unit Bool,
      (∀ u z, p.initialJoint.mass (u, z) =
        p.initialRecord.mass u * binaryPrior (1 / 2) z) ∧
      (∀ u h a z y, ((p.given u).observation h a z).mass y =
        if y = z then 1 else 0) ∧
      (∀ u h a, (p.given u).cost h a = 1) ∧
      conditionalMI p 1 (historyBank Unit Bool 1) = c ∧
      conditionalExpectedCost p 1 (historyBank Unit Bool 1) = c ∧
      conditionalInformationLimit p = c ∧
      conditionalExtendedCost p = ENNReal.ofReal c) ∧
    (∀ (H0 Z A : Type) [Fintype H0] [Fintype Z] [Fintype A]
      (p : ConditionalProtocol H0 Z A Bool),
      (∀ u, 0 < p.initialRecord.mass u →
        ∀ h a, 1 ≤ (p.given u).cost h a) →
      ENNReal.ofReal (conditionalInformationLimit p) ≤ conditionalExtendedCost p) := by
  refine ⟨⟨seedProtocol c hc0 hc1, seedProtocol_independent c hc0 hc1,
    (fun _ _ _ z y => perfectReading_mass z y),
    (fun _ _ _ => rfl), seedProtocol_information c hc0 hc1,
    seedProtocol_cost c hc0 hc1, seedProtocol_limit_information c hc0 hc1,
    seedProtocol_extendedCost c hc0 hc1⟩, ?_⟩
  intro H0 Z A _ _ _ p hcost
  exact conditional_binary_output_limiting_information_le_cost p hcost

/-! ## Arbitrary-output disjoint-row Bernoulli seed -/

/-- The original first-exclusive protocol stopped before any reading.
All policies, row laws and charges are inherited unchanged. -/
def idleExclusive (μ : FiniteLaw Bool) (P Q : FiniteLaw Y) :
    FiniteProtocol Bool Unit Y :=
  { firstExclusiveWith μ P Q with stop := fun _ => true }

/-- The idle branch gains no information at any finite horizon. -/
theorem idleExclusive_zero_information
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y) (n : ℕ)
    (bank : List (List (Unit × Y))) (hb : HistoryBank n bank) :
    terminalMI (idleExclusive μ P Q) n bank = 0 := by
  rw [terminalMI_eq_gain_sum (idleExclusive μ P Q) n bank hb]
  simp [idleExclusive]

/-- The idle branch has zero limiting information without any cost premise. -/
theorem idleExclusive_zero_informationLimit
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y) :
    informationLimit (idleExclusive μ P Q) = 0 := by
  apply le_antisymm _ (informationLimit_nonnegative (idleExclusive μ P Q))
  apply ciSup_le
  intro n
  exact (idleExclusive_zero_information μ P Q n (historyBank Unit Y n)
    (historyBank_complete Unit Y n)).le

theorem idleExclusive_zero_expectedCost
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (n : ℕ) (bank : List (List (Unit × Y))) :
    expectedCost (idleExclusive μ P Q) n bank = 0 := by
  simp [expectedCost, idleExclusive]

theorem idleExclusive_zero_extendedCost
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y) :
    extendedCost (idleExclusive μ P Q) = 0 := by
  unfold extendedCost
  simp [idleExclusive_zero_expectedCost]

/-- Initial Bernoulli seed U of chance c to read, independent of the
actual binary target prior. The retained seed chooses between the
existing first-exclusive protocol and its stop-before-first-reading branch.
No binary-output substitute for the original arbitrary Y rows is used. -/
def seededDisjointReading (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y) :
    ConditionalProtocol Bool Bool Unit Y where
  initialRecord := binaryPriorLaw c hc0 hc1
  initialJoint := {
    mass := fun uz => binaryPrior c uz.1 * μ.mass uz.2
    nonnegative := fun uz => mul_nonneg (binaryPrior_nonnegative c hc0 hc1 uz.1)
      (μ.nonnegative uz.2)
    total := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, μ.total, mul_one]
      exact binaryPrior_total c
  }
  given u := if u then firstExclusiveWith μ P Q else idleExclusive μ P Q
  initial_joint u z := by cases u <;> rfl

/-- Source mass is exactly a product of the seed and binary prior. -/
theorem seededDisjointReading_independent
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y) (u z : Bool) :
    (seededDisjointReading c hc0 hc1 μ P Q).initialJoint.mass (u, z) =
      (seededDisjointReading c hc0 hc1 μ P Q).initialRecord.mass u * μ.mass z := rfl

/-- Either seed branch reads precisely the original rows, not an
artificial binary-valued replacement of the output alphabet. -/
theorem seededDisjointReading_actual_rows
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (u : Bool) (h : List (Unit × Y)) (a : Unit) (z : Bool) :
    ((seededDisjointReading c hc0 hc1 μ P Q).given u).observation h a z =
      PairResolution.row P Q z := by
  cases u <;> rfl

/-! ## Exact finite and limiting attainment on the original output alphabet -/

/-- The reading branch decodes without error when the two output supports
are disjoint; the idle branch makes no zero-error claim. -/
theorem seededDisjointReading_true_zeroError
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (h : ∀ y, P.mass y = 0 ∨ Q.mass y = 0) :
    ZeroError ((seededDisjointReading c hc0 hc1 μ P Q).given true)
      (firstExclusiveDecoder Q) :=
  (disjoint_firstExclusiveWith_one_reading μ P Q h).2.1

/-- The independent seed of chance c buys exactly c times the prior
entropy by horizon one, on the actual arbitrary finite output alphabet. -/
theorem seededDisjointReading_finite_information
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (h : ∀ y, P.mass y = 0 ∨ Q.mass y = 0) :
    conditionalMI (seededDisjointReading c hc0 hc1 μ P Q)
      1 (historyBank Unit Y 1) = c * entropy μ.mass := by
  unfold conditionalMI
  rw [Fintype.sum_bool]
  change binaryPrior c true *
      terminalMI (firstExclusiveWith μ P Q) 1 (historyBank Unit Y 1) +
      binaryPrior c false *
      terminalMI (idleExclusive μ P Q) 1 (historyBank Unit Y 1) =
        c * entropy μ.mass
  rw [disjoint_firstExclusiveWith_finite_information μ P Q h,
    idleExclusive_zero_information μ P Q 1 (historyBank Unit Y 1)
      (historyBank_complete Unit Y 1)]
  simp [binaryPrior]

/-- The exact acquired-information amount has finite expected charge c,
not a charge inferred from a limit or an information proxy. -/
theorem seededDisjointReading_finite_cost
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (h : ∀ y, P.mass y = 0 ∨ Q.mass y = 0) :
    conditionalExpectedCost (seededDisjointReading c hc0 hc1 μ P Q)
      1 (historyBank Unit Y 1) = c := by
  unfold conditionalExpectedCost
  rw [Fintype.sum_bool]
  change binaryPrior c true *
      expectedCost (firstExclusiveWith μ P Q) 1 (historyBank Unit Y 1) +
      binaryPrior c false *
      expectedCost (idleExclusive μ P Q) 1 (historyBank Unit Y 1) = c
  rw [(disjoint_firstExclusiveWith_one_reading μ P Q h).2.2.2.2,
    idleExclusive_zero_expectedCost μ P Q]
  simp [binaryPrior]

/-- The actual information limit, averaging the positive initial-record
branches, equals c times the source prior entropy. -/
theorem seededDisjointReading_limit_information
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (h : ∀ y, P.mass y = 0 ∨ Q.mass y = 0) :
    conditionalInformationLimit (seededDisjointReading c hc0 hc1 μ P Q) =
      c * entropy μ.mass := by
  unfold conditionalInformationLimit
  rw [Fintype.sum_bool]
  change binaryPrior c true * informationLimit (firstExclusiveWith μ P Q) +
      binaryPrior c false * informationLimit (idleExclusive μ P Q) =
        c * entropy μ.mass
  rw [(disjoint_firstExclusiveWith_one_reading μ P Q h).2.2.1,
    idleExclusive_zero_informationLimit μ P Q]
  simp [binaryPrior]

/-- The actual conditional total cost equals the Bernoulli probability c. -/
theorem seededDisjointReading_extendedCost
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (μ : FiniteLaw Bool) (P Q : FiniteLaw Y)
    (h : ∀ y, P.mass y = 0 ∨ Q.mass y = 0) :
    conditionalExtendedCost (seededDisjointReading c hc0 hc1 μ P Q) =
      ENNReal.ofReal c := by
  unfold conditionalExtendedCost
  rw [Fintype.sum_bool]
  change ENNReal.ofReal (binaryPrior c true) *
      extendedCost (firstExclusiveWith μ P Q) +
      ENNReal.ofReal (binaryPrior c false) *
      extendedCost (idleExclusive μ P Q) = ENNReal.ofReal c
  rw [(disjoint_firstExclusiveWith_one_reading μ P Q h).2.2.2.1,
    idleExclusive_zero_extendedCost μ P Q]
  simp [binaryPrior]

/-- With a fair binary label, any disjoint finite-output reading achieves
every target 0 ≤ c ≤ 1, with exact c bits and exact expected cost c
both at finite horizon one and over the countable stopped experiment. -/
theorem seededDisjointReading_fair_frontier
    (P Q : FiniteLaw Y)
    (h : ∀ y, P.mass y = 0 ∨ Q.mass y = 0)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∃ p : ConditionalProtocol Bool Bool Unit Y,
      (∀ u z, p.initialJoint.mass (u, z) =
        p.initialRecord.mass u * ResolutionAttainment.fairLaw.mass z) ∧
      (∀ u hs a z, (p.given u).observation hs a z = PairResolution.row P Q z) ∧
      (∀ u hs a, (p.given u).cost hs a = 1) ∧
      conditionalMI p 1 (historyBank Unit Y 1) = c ∧
      conditionalExpectedCost p 1 (historyBank Unit Y 1) = c ∧
      conditionalInformationLimit p = c ∧
      conditionalExtendedCost p = ENNReal.ofReal c := by
  refine ⟨seededDisjointReading c hc0 hc1 ResolutionAttainment.fairLaw P Q,
    seededDisjointReading_independent c hc0 hc1 ResolutionAttainment.fairLaw P Q,
    (fun u hs a z => seededDisjointReading_actual_rows
      c hc0 hc1 ResolutionAttainment.fairLaw P Q u hs a z),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro u hs a
    cases u <;> rfl
  · simpa only [ResolutionAttainment.fairLaw_entropy, mul_one] using
      seededDisjointReading_finite_information c hc0 hc1
        ResolutionAttainment.fairLaw P Q h
  · exact seededDisjointReading_finite_cost c hc0 hc1 ResolutionAttainment.fairLaw P Q h
  · simpa only [ResolutionAttainment.fairLaw_entropy, mul_one] using
      seededDisjointReading_limit_information c hc0 hc1
        ResolutionAttainment.fairLaw P Q h
  · exact seededDisjointReading_extendedCost c hc0 hc1 ResolutionAttainment.fairLaw P Q h

/-! END_OF_S1 -/

end

end OperatorKO7.Meta.BoundaryObserver.BoundaryInfiniteCostConditional
