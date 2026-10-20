import OperatorKO7.Meta.BoundaryObserver.ResolutionAttainment
import OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
import OperatorKO7.Meta.BoundaryObserver.ResourceFrontier

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.ProtocolFamilyCost

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.ResolutionAttainment
open scoped ENNReal BigOperators

/-- The finite-horizon family frontier is the infimum of costs of qualifying protocol-horizon
pairs, with infinity for a family having no qualifying pair. -/
noncomputable def familyMinCost {H0 Z A Y : Type}
    [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]
    (S : Set (ConditionalProtocol H0 Z A Y)) (c : ℝ) : ℝ≥0∞ :=
  sInf {r : ℝ≥0∞ | ∃ p ∈ S, ∃ n : ℕ,
    c ≤ conditionalJointInfo p n (historyBank A Y n) ∧
    r = ENNReal.ofReal (conditionalExpectedCost p n (historyBank A Y n))}

/-- The limit family frontier is the infimum of extended costs of protocols meeting the
limit information target, with infinity for an empty qualifying family. -/
noncomputable def familyLimitMinCost {H0 Z A Y : Type}
    [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]
    (S : Set (ConditionalProtocol H0 Z A Y)) (c : ℝ) : ℝ≥0∞ :=
  sInf {r : ℝ≥0∞ | ∃ p ∈ S,
    c ≤ conditionalInformationLimit p ∧ r = conditionalExtendedCost p}

/-- Every qualifying horizon in a family of positive-bias binary menus pays at least
the information target divided by four times the squared bias. -/
theorem familyMinCost_lower {H0 A : Type} [Fintype H0] [Fintype A]
    (S : Set (ConditionalProtocol H0 Bool A Bool)) (c ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hmenu : ∀ p ∈ S, ∀ u, 0 < p.initialRecord.mass u →
      BinaryMenu (p.given u) ε) :
    ENNReal.ofReal (c / (4 * ε ^ 2)) ≤ familyMinCost S c := by
  unfold familyMinCost
  apply le_sInf
  intro r hr
  rcases hr with ⟨p, hp, n, hc, rfl⟩
  exact ENNReal.ofReal_le_ofReal
    (conditional_binaryMenu_cost_lower_bound p ε c (hmenu p hp) hε0 hε1 n _
      (historyBank_complete A Bool n) hc)

/-- Every qualifying limit protocol in a family of positive-bias binary menus has
extended cost at least the information target divided by four times the squared bias,
including the case of infinite extended cost. -/
theorem familyLimitMinCost_lower {H0 A : Type} [Fintype H0] [Fintype A]
    (S : Set (ConditionalProtocol H0 Bool A Bool)) (c ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hmenu : ∀ p ∈ S, ∀ u, 0 < p.initialRecord.mass u →
      BinaryMenu (p.given u) ε) :
    ENNReal.ofReal (c / (4 * ε ^ 2)) ≤ familyLimitMinCost S c := by
  unfold familyLimitMinCost
  apply le_sInf
  intro r hr
  rcases hr with ⟨p, hp, hc, rfl⟩
  have hi : ENNReal.ofReal c ≤
      ENNReal.ofReal (4 * ε ^ 2) * conditionalExtendedCost p :=
    (ENNReal.ofReal_le_ofReal hc).trans
      (conditional_binaryMenu_limit_bound p ε (hmenu p hp) hε1)
  rw [ENNReal.ofReal_div_of_pos (by positivity : 0 < 4 * ε ^ 2)]
  apply (ENNReal.div_le_iff (by positivity) (by simp)).2
  simpa only [mul_comm] using hi

/-- A finite protocol becomes a conditional protocol with exactly one initial record,
whose joint initial law is the original prior. -/
noncomputable def onePointLift {Z A Y : Type}
    [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) : ConditionalProtocol Unit Z A Y where
  initialRecord := {
    mass := fun _ => 1
    nonnegative := fun _ => zero_le_one
    total := by simp
  }
  initialJoint := {
    mass := fun uz => p.prior.mass uz.2
    nonnegative := fun uz => p.prior.nonnegative uz.2
    total := by
      rw [Fintype.sum_prod_type]
      simpa using p.prior.total
  }
  given := fun _ => p
  initial_joint := by
    intro _ z
    simp

/-- The one-record lift preserves the acquired information for every complete finite
history bank. -/
theorem onePointLift_jointInfo {Z A Y : Type}
    [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) (n : ℕ) (bank : List (List (A × Y)))
    (hb : HistoryBank n bank) :
    conditionalJointInfo (onePointLift p) n bank = terminalMI p n bank := by
  rw [conditionalJointInfo_eq_conditionalMI _ _ _ hb]
  simp [conditionalMI, onePointLift]

/-- The one-record lift preserves expected cost for every horizon and every finite bank. -/
theorem onePointLift_expectedCost {Z A Y : Type}
    [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) (n : ℕ) (bank : List (List (A × Y))) :
    conditionalExpectedCost (onePointLift p) n bank = expectedCost p n bank := by
  simp [conditionalExpectedCost, onePointLift]

/-- Every family containing the one-record majority protocols reaches the stated
information target within the majority protocol's explicit cost bound. -/
theorem familyMinCost_upper_majority
    (S : Set (ConditionalProtocol Unit Bool Unit Bool)) (ε η c : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hc : c ≤ 1 - Real.binEntropy η / Real.log 2)
    (hmem : ∀ N : ℕ, onePointLift (majorityProtocol ε hε0.le hε1 N) ∈ S) :
    familyMinCost S c ≤
      ENNReal.ofReal (Real.log (1 / (2 * η)) / (2 * ε ^ 2) + 3) := by
  obtain ⟨N, hinfo, hcost, hN⟩ :=
    (resolution_cost_two_sided ε hε0 hε1).2 η hη0 hη1
  have hqual : c ≤ conditionalJointInfo
      (onePointLift (majorityProtocol ε hε0.le hε1 N)) N
      (historyBank Unit Bool N) := by
    rw [onePointLift_jointInfo _ _ _ (historyBank_complete Unit Bool N)]
    exact hc.trans hinfo
  calc
    familyMinCost S c ≤
        ENNReal.ofReal (conditionalExpectedCost
          (onePointLift (majorityProtocol ε hε0.le hε1 N)) N
          (historyBank Unit Bool N)) := by
      unfold familyMinCost
      apply sInf_le
      exact ⟨_, hmem N, N, hqual, rfl⟩
    _ = ENNReal.ofReal (expectedCost
          (majorityProtocol ε hε0.le hε1 N) N (historyBank Unit Bool N)) := by
      rw [onePointLift_expectedCost]
    _ ≤ ENNReal.ofReal (Real.log (1 / (2 * η)) / (2 * ε ^ 2) + 3) := by
      rw [hcost]
      exact ENNReal.ofReal_le_ofReal hN


/-- A one-record lift preserves the limit of the actual stopped information laws. -/
theorem onePointLift_informationLimit {Z A Y : Type}
    [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) :
    conditionalInformationLimit (onePointLift p) = informationLimit p := by
  unfold conditionalInformationLimit
  rw [Fintype.sum_unique]
  change (1 : ℝ) * informationLimit p = informationLimit p
  rw [one_mul]

/-- The one-record lift preserves the extended expected cost, including infinity. -/
theorem onePointLift_extendedCost {Z A Y : Type}
    [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) :
    conditionalExtendedCost (onePointLift p) = extendedCost p := by
  unfold conditionalExtendedCost
  rw [Fintype.sum_unique]
  change ENNReal.ofReal (1 : ℝ) * extendedCost p = extendedCost p
  rw [ENNReal.ofReal_one, one_mul]

/-- A family containing the actual one-record majority protocols also has a finite
limit-information qualifying member with extended cost at most the majority bound. -/
theorem familyLimitMinCost_upper_majority
    (S : Set (ConditionalProtocol Unit Bool Unit Bool)) (ε η c : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hc : c ≤ 1 - Real.binEntropy η / Real.log 2)
    (hmem : ∀ N : ℕ, onePointLift (majorityProtocol ε hε0.le hε1 N) ∈ S) :
    familyLimitMinCost S c ≤
      ENNReal.ofReal (Real.log (1 / (2 * η)) / (2 * ε ^ 2) + 3) := by
  obtain ⟨N, hinfo, _hcost, hN⟩ :=
    (resolution_cost_two_sided ε hε0 hε1).2 η hη0 hη1
  have hqual : c ≤ conditionalInformationLimit
      (onePointLift (majorityProtocol ε hε0.le hε1 N)) := by
    rw [onePointLift_informationLimit]
    exact (hc.trans hinfo).trans
      (terminalMI_le_informationLimit (majorityProtocol ε hε0.le hε1 N) N)
  calc
    familyLimitMinCost S c ≤
        conditionalExtendedCost (onePointLift (majorityProtocol ε hε0.le hε1 N)) := by
      unfold familyLimitMinCost
      apply sInf_le
      exact ⟨_, hmem N, hqual, rfl⟩
    _ = extendedCost (majorityProtocol ε hε0.le hε1 N) :=
      onePointLift_extendedCost _
    _ = ENNReal.ofReal (N : ℝ) :=
      ResourceFrontier.majority_extendedCost ε hε0.le hε1 N
    _ ≤ ENNReal.ofReal (Real.log (1 / (2 * η)) / (2 * ε ^ 2) + 3) :=
      ENNReal.ofReal_le_ofReal hN

end OperatorKO7.Meta.BoundaryObserver.ProtocolFamilyCost

