import OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
import OperatorKO7.Meta.BoundaryObserver.BoundarySingularity

set_option autoImplicit false

/-!
# The perfect reading with a free random seed: least expected cost `c` for `c` bits

Manuscript: Theorem `thm:pair-resolution-sharp`(iv) and Table `tab:three-regimes`, the
deterministic end.

A reading whose output is binary carries at most one bit at every retained history, whatever the
label type and the observation kernel. With unit-cost readings, every protocol, conditional on an
initial record, therefore acquires at most its expected cost in bits. The seeded protocol draws a
seed `U` with `P(U = true) = c`, independent of a fair label; on seed `true` it reads the label once
without error and stops, on seed `false` it stops at once. It acquires exactly `c` bits at expected
cost exactly `c`. Information and cost are the `terminalMI`, `expectedCost`, `conditionalMI` and
`conditionalExpectedCost` of `ProtocolResolution`; this module adds no definition of either.
Relation: finite joint probability laws of stopped protocols. External trust: none.
-/

namespace OperatorKO7.Meta.BoundaryObserver.SeedFrontier

open scoped BigOperators
open ProtocolResolution

/-! ## One binary output carries at most one bit -/

/-- A real mass function on two points with total one has entropy at most one bit.
No sign condition on the masses is needed: the entropy is `binEntropy (m true) / log 2`. -/
theorem entropy_bool_le_one (m : Bool → ℝ) (hm : m true + m false = 1) : entropy m ≤ 1 := by
  have hb : m = binaryPrior (m true) := by
    funext b
    cases b
    · change m false = 1 - m true
      linarith
    · rfl
  rw [hb]
  unfold entropy
  rw [binaryPrior_entropy, div_le_one (Real.log_pos one_lt_two)]
  exact Real.binEntropy_le_log_two

section BinaryOutputs
variable {Z A : Type} [Fintype Z] [Fintype A]

/-- At every retained history and every action, the local gain of a reading with a binary output
is at most one bit, for every finite label type and every observation kernel, noisy or perfect.
Zero-mass histories have gain zero. -/
theorem localGain_le_one_bit (p : FiniteProtocol Z A Bool) (h : List (A × Bool)) (a : A) :
    localGain p h a ≤ 1 := by
  rcases (historyMass_nonnegative p h).eq_or_lt with hw | hw
  · rw [localGain_zero_of_historyMass_zero p h hw.symm a]
    exact zero_le_one
  · have hk : localGain p h a =
        entropy (fun y => ∑ z, posterior p h z * (p.observation h a z).mass y) -
          ∑ z, posterior p h z * entropy (p.observation h a z).mass :=
      jointMI_kernel (posterior p h) (fun z y => (p.observation h a z).mass y)
        (fun z => (p.observation h a z).total)
    have hcond : 0 ≤ ∑ z, posterior p h z * entropy (p.observation h a z).mass :=
      Finset.sum_nonneg (fun z _ =>
        mul_nonneg (posterior_nonnegative p h z) (p.observation h a z).entropy_nonnegative)
    have hout : entropy (fun y => ∑ z, posterior p h z * (p.observation h a z).mass y) ≤ 1 := by
      apply entropy_bool_le_one
      show (∑ z, posterior p h z * (p.observation h a z).mass true) +
        (∑ z, posterior p h z * (p.observation h a z).mass false) = 1
      rw [← Finset.sum_add_distrib]
      calc
        (∑ z, (posterior p h z * (p.observation h a z).mass true +
            posterior p h z * (p.observation h a z).mass false)) = ∑ z, posterior p h z := by
          apply Finset.sum_congr rfl
          intro z _
          have ht := (p.observation h a z).total
          rw [Fintype.sum_bool] at ht
          rw [← mul_add, ht, mul_one]
        _ = 1 := posterior_total p h hw
    linarith

/-- A protocol whose readings have binary outputs and cost at least one obeys the local capacity
bound of one bit per unit of cost. The cost premise is necessary: a perfect reading of cost zero at
a fair label carries one bit against a charge of zero. -/
theorem binary_output_capacity (p : FiniteProtocol Z A Bool) (hcost : ∀ h a, 1 ≤ p.cost h a) :
    LocalCapacityBound p 1 := by
  intro h a _ _ _
  calc
    localGain p h a ≤ 1 := localGain_le_one_bit p h a
    _ ≤ 1 * p.cost h a := by
      rw [one_mul]
      exact hcost h a

/-- Every protocol of readings with binary outputs, each costing at least one, acquires at most its
expected cost in bits, at every horizon and for every complete history bank. The readings may be
perfect or noisy, and the label type is any finite type. -/
theorem perfect_reading_information_le_cost (p : FiniteProtocol Z A Bool)
    (hcost : ∀ h a, 1 ≤ p.cost h a) (n : ℕ) (bank : List (List (A × Bool)))
    (hb : HistoryBank n bank) : terminalMI p n bank ≤ expectedCost p n bank := by
  simpa only [one_mul] using
    terminalMI_le_expectedCost p 1 n bank hb (binary_output_capacity p hcost)

/-- The conditional form: for every initial record law, a protocol whose branches at the records of
positive mass read binary outputs at cost at least one acquires, conditionally on the record, at
most its conditional expected cost in bits. Records of zero mass carry no premise. -/
theorem conditional_perfect_reading_information_le_cost {H0 : Type} [Fintype H0]
    (p : ConditionalProtocol H0 Z A Bool)
    (hcost : ∀ u, 0 < p.initialRecord.mass u → ∀ h a, 1 ≤ (p.given u).cost h a)
    (n : ℕ) (bank : List (List (A × Bool))) (hb : HistoryBank n bank) :
    conditionalMI p n bank ≤ conditionalExpectedCost p n bank := by
  simpa only [one_mul] using conditionalMI_le_expectedCost p n bank hb 1
    (fun u hu => binary_output_capacity (p.given u) (hcost u hu))

end BinaryOutputs

/-! ## The seeded protocol -/

/-- The perfect reading of a binary label: the outcome equals the label with probability one.
Its mass is the binary kernel at bias one half. -/
noncomputable def perfectReading (z : Bool) : FiniteLaw Bool where
  mass := binaryKernel (1 / 2) z
  nonnegative := binaryKernel_nonnegative (1 / 2) (by norm_num [abs_of_pos]) z
  total := binaryKernel_total (1 / 2) z

theorem perfectReading_mass (z y : Bool) :
    (perfectReading z).mass y = if y = z then 1 else 0 := by
  change binaryKernel (1 / 2) z y = _
  unfold binaryKernel
  split_ifs <;> norm_num

/-- The fair label law. -/
noncomputable def fairLabel : FiniteLaw Bool := binaryPriorLaw (1 / 2) (by norm_num) (by norm_num)

/-- The branch of the seeded protocol at seed `u`: the fair label, one action, the perfect reading
at unit cost; at seed `true` it stops after one reading, at seed `false` it stops at the empty
history, so no reading is taken. -/
noncomputable def seedBranch (u : Bool) : FiniteProtocol Bool Unit Bool where
  prior := fairLabel
  policy _ := unitLaw
  observation _ _ z := perfectReading z
  stop h := if u then decide (1 ≤ h.length) else true
  cost _ _ := 1
  cost_nonnegative _ _ := zero_le_one

/-- The seed record `U`, with `P(U = true) = c`, and the fair label, joined as a product law. -/
noncomputable def seedJoint (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : FiniteLaw (Bool × Bool) where
  mass uz := binaryPrior c uz.1 * binaryPrior (1 / 2) uz.2
  nonnegative uz := mul_nonneg (binaryPrior_nonnegative c hc0 hc1 uz.1)
    (binaryPrior_nonnegative (1 / 2) (by norm_num) (by norm_num) uz.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, binaryPrior_total, mul_one]

/-- The seeded protocol: initial record the seed `U` with mass `c` at `true` and `1 - c` at
`false`, the label fair and independent of the seed, and the branch `seedBranch U`. -/
noncomputable def seedProtocol (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ConditionalProtocol Bool Bool Unit Bool where
  initialRecord := binaryPriorLaw c hc0 hc1
  initialJoint := seedJoint c hc0 hc1
  given := seedBranch
  initial_joint _ _ := rfl

/-- The seed is independent of the label: the initial joint law is the product of the seed law and
the fair label law. -/
theorem seedProtocol_independent (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (u z : Bool) :
    (seedProtocol c hc0 hc1).initialJoint.mass (u, z) =
      (seedProtocol c hc0 hc1).initialRecord.mass u * binaryPrior (1 / 2) z := rfl

/-- The seed-`true` branch acquires one bit at horizon one. -/
theorem seedBranch_true_information :
    terminalMI (seedBranch true) 1 (historyBank Unit Bool 1) = 1 := by
  have hb := historyBank_complete Unit Bool 1
  have hw : historyMass (seedBranch true) [] = 1 := binaryPrior_total (1 / 2)
  have hpost : posterior (seedBranch true) [] = binaryPrior (1 / 2) := by
    funext z
    unfold posterior
    rw [hw, div_one]
    rfl
  have hgain : localGain (seedBranch true) [] () = 1 := by
    unfold localGain
    rw [hpost]
    change jointMI (binaryJoint (1 / 2) (1 / 2)) = 1
    rw [binaryJoint_information_fair]
    norm_num
  rw [terminalMI_eq_gain_sum (seedBranch true) 1 _ hb, hb.sum_eq, historySet_sum_succ]
  have hnil : ([] : List (Unit × Bool)).length < 1 ∧ (seedBranch true).stop [] = false :=
    ⟨Nat.zero_lt_one, rfl⟩
  have hzero : ∀ (h : List (Unit × Bool)) (e : Unit × Bool),
      (if (h ++ [e]).length < 1 ∧ (seedBranch true).stop (h ++ [e]) = false then
        historyMass (seedBranch true) (h ++ [e]) *
          ∑ a, ((seedBranch true).policy (h ++ [e])).mass a *
            localGain (seedBranch true) (h ++ [e]) a
      else 0) = 0 := fun h e => if_neg (by simp)
  rw [if_pos hnil, hw, one_mul]
  simp only [hzero, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_unique]
  change (1 : ℝ) * localGain (seedBranch true) [] () = 1
  rw [hgain, one_mul]

/-- The seed-`true` branch pays expected cost one at horizon one. -/
theorem seedBranch_true_cost :
    expectedCost (seedBranch true) 1 (historyBank Unit Bool 1) = 1 := by
  have hb := historyBank_complete Unit Bool 1
  have hw : historyMass (seedBranch true) [] = 1 := binaryPrior_total (1 / 2)
  unfold expectedCost
  rw [hb.sum_eq, historySet_sum_succ]
  have hnil : ([] : List (Unit × Bool)).length < 1 ∧ (seedBranch true).stop [] = false :=
    ⟨Nat.zero_lt_one, rfl⟩
  have hzero : ∀ (h : List (Unit × Bool)) (e : Unit × Bool),
      (if (h ++ [e]).length < 1 ∧ (seedBranch true).stop (h ++ [e]) = false then
        historyMass (seedBranch true) (h ++ [e]) *
          ∑ a, ((seedBranch true).policy (h ++ [e])).mass a *
            (seedBranch true).cost (h ++ [e]) a
      else 0) = 0 := fun h e => if_neg (by simp)
  rw [if_pos hnil, hw, one_mul]
  simp only [hzero, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_unique]
  change (1 : ℝ) * 1 = 1
  rw [one_mul]

/-- The seed-`false` branch stops at once: zero information at every horizon and bank. -/
theorem seedBranch_false_information (n : ℕ) (bank : List (List (Unit × Bool)))
    (hb : HistoryBank n bank) : terminalMI (seedBranch false) n bank = 0 := by
  rw [terminalMI_eq_gain_sum (seedBranch false) n bank hb]
  simp [seedBranch]

/-- The seed-`false` branch takes no action: zero expected cost at every horizon and bank. -/
theorem seedBranch_false_cost (n : ℕ) (bank : List (List (Unit × Bool))) :
    expectedCost (seedBranch false) n bank = 0 := by
  simp [expectedCost, seedBranch]

/-- The seeded protocol acquires exactly `c` bits about the fair label at horizon one. -/
theorem seedProtocol_information (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    conditionalMI (seedProtocol c hc0 hc1) 1 (historyBank Unit Bool 1) = c := by
  unfold conditionalMI
  rw [Fintype.sum_bool]
  change binaryPrior c true * terminalMI (seedBranch true) 1 (historyBank Unit Bool 1) +
      binaryPrior c false * terminalMI (seedBranch false) 1 (historyBank Unit Bool 1) = c
  rw [seedBranch_true_information,
    seedBranch_false_information 1 _ (historyBank_complete Unit Bool 1)]
  simp [binaryPrior]

/-- The seeded protocol pays expected cost exactly `c` at horizon one. -/
theorem seedProtocol_cost (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    conditionalExpectedCost (seedProtocol c hc0 hc1) 1 (historyBank Unit Bool 1) = c := by
  unfold conditionalExpectedCost
  rw [Fintype.sum_bool]
  change binaryPrior c true * expectedCost (seedBranch true) 1 (historyBank Unit Bool 1) +
      binaryPrior c false * expectedCost (seedBranch false) 1 (historyBank Unit Bool 1) = c
  rw [seedBranch_true_cost, seedBranch_false_cost]
  simp [binaryPrior]

/-! ## The frontier -/

/-- The cost frontier of the perfect binary reading with a free random seed, for `0 ≤ c ≤ 1`.
Attainment: some conditional protocol, with a fair label independent of its initial record, perfect
readings and unit costs, acquires exactly `c` bits at expected cost exactly `c` at horizon one.
Lower bound: every conditional protocol over any finite label type whose readings have binary
outputs and cost at least one, at the records of positive mass, acquires at most its conditional
expected cost in bits, at every horizon and every complete history bank. The least expected cost
of `c` bits is therefore `c`. -/
theorem seed_frontier (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (∃ p : ConditionalProtocol Bool Bool Unit Bool,
      (∀ u z, p.initialJoint.mass (u, z) = p.initialRecord.mass u * binaryPrior (1 / 2) z) ∧
      (∀ u h a z y, ((p.given u).observation h a z).mass y = if y = z then 1 else 0) ∧
      (∀ u h a, (p.given u).cost h a = 1) ∧
      conditionalMI p 1 (historyBank Unit Bool 1) = c ∧
      conditionalExpectedCost p 1 (historyBank Unit Bool 1) = c) ∧
    (∀ (H0 Z A : Type) [Fintype H0] [Fintype Z] [Fintype A]
      (p : ConditionalProtocol H0 Z A Bool),
      (∀ u, 0 < p.initialRecord.mass u → ∀ h a, 1 ≤ (p.given u).cost h a) →
      ∀ (n : ℕ) (bank : List (List (A × Bool))), HistoryBank n bank →
        conditionalMI p n bank ≤ conditionalExpectedCost p n bank) := by
  refine ⟨⟨seedProtocol c hc0 hc1, seedProtocol_independent c hc0 hc1,
    fun _ _ _ z y => perfectReading_mass z y, fun _ _ _ => rfl,
    seedProtocol_information c hc0 hc1, seedProtocol_cost c hc0 hc1⟩, ?_⟩
  intro H0 Z A _ _ _ p hcost n bank hb
  exact conditional_perfect_reading_information_le_cost p hcost n bank hb

end OperatorKO7.Meta.BoundaryObserver.SeedFrontier
