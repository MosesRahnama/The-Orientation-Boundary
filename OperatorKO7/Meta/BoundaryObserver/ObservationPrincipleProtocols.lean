import OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
import OperatorKO7.Meta.BoundaryObserver.PairResolution
import OperatorKO7.Meta.BoundaryObserver.ResolutionAttainment
import OperatorKO7.Meta.BoundaryObserver.StochasticGraph
import OperatorKO7.Meta.BoundaryObserver.BitDivision
import OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
import OperatorKO7.Meta.BoundaryObserver.ErasurePriorCompletion
import OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions
import OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation
import OperatorKO7.Meta.BoundaryObserver.DemandTransport
import OperatorKO7.Meta.BoundaryObserver.BurdenTail
import OperatorKO7.Meta.UUET.Statistics.FisherDPI
import OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
import OperatorKO7.Meta.BoundaryObserver.PersistentBinaryEvidence

set_option autoImplicit false

/-!
# Protocol, resolution and record sentences of the Boundary-Observation Principle

The statements of the sections on readings, protocols and records that no earlier declaration
states in the words of the paper: the attainment of the binary capacity by the fair prior; the
capacity form of the fixed-horizon cost; the capacity form of the adaptive binary-menu cost and the
discrimination forms of the two-sided bounds; the chain of the repetition error bounds; the infimum
`M_c` of the expected cost over adaptive protocols with an independent initial record and its
two-sided bound of order `Δ⁻¹`; the reciprocal lower bound for zero-error protocols with an
independent initial record; the increase of conditional information and cost; the conditional
variance form of the Fisher loss, and the Fisher loss for every channel with the output restricted
to its attained support; the two states of a kernel witness of a linear observer; the universal
stable record of a record that is not surjective;
the stabilizer of a side record as the stabilizer of the joint observer; the transport of licensed
plans under budgets; and the depth ratio of the natural-depth law.

Relation: none beyond the protocols, laws and records of the imported modules.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleProtocols

open ProtocolResolution

/-! ## Proposition `prop:all-prior-binary` and Theorem `thm:resolution-cost` -/

/-- The fair prior and a reading of bias `ε` attain the binary capacity `κ_ε`. -/
theorem fair_binary_attains_capacity (ε : ℝ) :
    jointMI (binaryJoint (1 / 2) ε) = binaryCapacity ε := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [binaryJoint_information, binaryCapacity]
  have h : (1 : ℝ) / 2 - ε + 2 * ε * (1 / 2) = 1 / 2 := by ring
  rw [h, one_div, Real.binEntropy_two_inv, sub_div, div_self hlog]

/-- `N` independent readings of a fair label, each of reliability `1/2 + ε`, acquire at most
`N κ_ε` bits. -/
theorem readingsInformation_le_capacity (N : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) :
    StochasticGraph.readingsInformation N ε ≤ N * binaryCapacity ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h := BitDivision.readings_mutualInfo_le N ε h0 h1
  unfold StochasticGraph.readingsInformation binaryCapacity
  rw [div_le_iff₀ hlog]
  calc _ ≤ min (Real.log 2) (N * (Real.log 2 - Real.binEntropy (1 / 2 + ε))) := h
    _ ≤ N * (Real.log 2 - Real.binEntropy (1 / 2 + ε)) := min_le_right _ _
    _ = N * (1 - Real.binEntropy (1 / 2 + ε) / Real.log 2) * Real.log 2 := by
      field_simp

/-- For `ε > 0`, acquiring `c` bits with `N` readings requires `N ≥ c / κ_ε`, and for `c ≥ 0` this
bound is at least `c / (4 ε²)`. -/
theorem readings_cost_capacity (N : ℕ) (ε c : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2)
    (hc : c ≤ StochasticGraph.readingsInformation N ε) :
    c / binaryCapacity ε ≤ N ∧ (0 ≤ c → c / (4 * ε ^ 2) ≤ c / binaryCapacity ε) := by
  have hk := binaryCapacity_pos h0
  refine ⟨?_, fun hc0 => div_le_div_of_nonneg_left hc0 hk (binaryCapacity_le_quadratic ε h0.le h1)⟩
  rw [div_le_iff₀ hk]
  exact hc.trans (readingsInformation_le_capacity N ε h0.le h1)

/-! ## Theorem `thm:resolution-sharp`(iv): the capacity and discrimination forms -/

section BinaryMenuExact

variable {A : Type} [Fintype A]

/-- Every active reading of a binary menu of bias at most `ε ≤ 1/2` obeys the exact capacity bound
`κ_ε` at its own posterior. -/
theorem binaryMenu_capacity_exact (p : FiniteProtocol Bool A Bool) (ε : ℝ)
    (menu : BinaryMenu p ε) (hε : ε ≤ 1 / 2) : LocalCapacityBound p (binaryCapacity ε) := by
  intro h a hw _ _
  rw [binaryMenu_localGain p ε menu h a hw]
  calc
    jointMI (binaryJoint (posterior p h true) (menu.bias h a)) ≤ binaryCapacity ε :=
      binaryJoint_information_le_exact_envelope _ _ ε (menu.bound h a) hε
    _ ≤ binaryCapacity ε * p.cost h a := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (menu.reading_cost h a) (binaryCapacity_nonneg ε)

/-- The adaptive binary-menu information is at most `κ_ε` times the expected cost. -/
theorem binaryMenu_information_bound_exact (p : FiniteProtocol Bool A Bool) (ε : ℝ)
    (menu : BinaryMenu p ε) (hε : ε ≤ 1 / 2) (n : ℕ) (bank : List (List (A × Bool)))
    (hb : HistoryBank n bank) :
    terminalMI p n bank ≤ binaryCapacity ε * expectedCost p n bank :=
  terminalMI_le_expectedCost p _ n bank hb (binaryMenu_capacity_exact p ε menu hε)

/-- Every protocol of the binary menu of bias `ε > 0` that acquires `c` bits pays at least
`c / κ_ε` in expectation, and for `c ≥ 0` this is at least `c / (4 ε²)`. -/
theorem binaryMenu_cost_lower_bound_exact (p : FiniteProtocol Bool A Bool) (ε c : ℝ)
    (menu : BinaryMenu p ε) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (n : ℕ)
    (bank : List (List (A × Bool))) (hb : HistoryBank n bank) (hc : c ≤ terminalMI p n bank) :
    c / binaryCapacity ε ≤ expectedCost p n bank ∧
      (0 ≤ c → c / (4 * ε ^ 2) ≤ c / binaryCapacity ε) := by
  have hk := binaryCapacity_pos hε0
  refine ⟨?_, fun hc0 => div_le_div_of_nonneg_left hc0 hk (binaryCapacity_le_quadratic ε hε0.le hε)⟩
  rw [div_le_iff₀ hk, mul_comm]
  exact hc.trans (binaryMenu_information_bound_exact p ε menu hε n bank hb)

end BinaryMenuExact

/-- In the discrimination `δ = 8 ε²` of the binary readings, the two bounds of the binary menu read
`2c / δ` and `4 log(1/(2η)) / δ + 3`. -/
theorem resolution_two_sided_discrimination (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    (∀ {A : Type} [Fintype A] (p : FiniteProtocol Bool A Bool) (c : ℝ), BinaryMenu p ε →
      ∀ (n : ℕ) (bank : List (List (A × Bool))), HistoryBank n bank →
        c ≤ terminalMI p n bank → 2 * c / (8 * ε ^ 2) ≤ expectedCost p n bank) ∧
    (∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ N : ℕ,
      1 - Real.binEntropy η / Real.log 2 ≤
          terminalMI (ResolutionAttainment.majorityProtocol ε hε0.le hε1 N) N
            (historyBank Unit Bool N) ∧
        expectedCost (ResolutionAttainment.majorityProtocol ε hε0.le hε1 N) N
            (historyBank Unit Bool N) = N ∧
        (N : ℝ) ≤ 4 * Real.log (1 / (2 * η)) / (8 * ε ^ 2) + 3) := by
  obtain ⟨hlow, hup⟩ := ResolutionAttainment.resolution_cost_two_sided ε hε0 hε1
  have hε2 : (8 : ℝ) * ε ^ 2 ≠ 0 := by positivity
  refine ⟨fun p c menu n bank hb hc => ?_, fun η hη0 hη1 => ?_⟩
  · have h := hlow p c menu n bank hb hc
    have he : 2 * c / (8 * ε ^ 2) = c / (4 * ε ^ 2) := by field_simp; ring
    rw [he]
    exact h
  · obtain ⟨N, h1, h2, h3⟩ := hup η hη0 hη1
    refine ⟨N, h1, h2, ?_⟩
    have he : 4 * Real.log (1 / (2 * η)) / (8 * ε ^ 2) = Real.log (1 / (2 * η)) / (2 * ε ^ 2) := by
      field_simp; ring
    rw [he]
    exact h3

/-! ## Theorem `thm:pair-resolution-sharp`(i) and (iii) -/

open PairResolution BoundarySingularity

/-- The repetition error chain: the likelihood-ratio decoder of the repeated reading errs with
probability at most `BC^N / 2 ≤ (1 - Δ/4)^N / 2 ≤ e^{-N Δ / 4} / 2`, at expected cost `N`. -/
theorem repeat_error_chain {Y : Type} [Fintype Y] (P Q : FiniteLaw Y) (N : ℕ) :
    ∑ h ∈ historySet (Unit × Y) N,
        stoppedMass (repeatProtocol P Q N) N (!mapDecoder P Q h) h ≤
      1 / 2 * (bhattacharyya P.mass Q.mass) ^ N ∧
    1 / 2 * (bhattacharyya P.mass Q.mass) ^ N ≤
      1 / 2 * (1 - discrimination P.mass Q.mass / 4) ^ N ∧
    1 / 2 * (1 - discrimination P.mass Q.mass / 4) ^ N ≤
      1 / 2 * Real.exp (-(N * discrimination P.mass Q.mass / 4)) ∧
    expectedCost (repeatProtocol P Q N) N (historyBank Unit Y N) = N := by
  refine ⟨repeat_error_le P Q N, ?_, repeat_error_le_exp P Q N, repeat_cost P Q N⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact pow_le_pow_left₀ (bhattacharyya_nonneg _ _)
    (bhattacharyya_le_one_sub_quarter_discrimination _ _ P.nonnegative Q.nonnegative P.total
      Q.total) N

/-- The expected costs of the adaptive protocols for a fair label with an initial record
independent of the label, every conditional reading of discrimination at most `Δ` and cost at
least one, that acquire at least `c` bits at a finite horizon. -/
def mainCostSet (Δ c : ℝ) : Set ℝ :=
  {x | ∃ (H0 A Y : Type) (_ : Fintype H0) (_ : Fintype A) (_ : Fintype Y)
      (p : ConditionalProtocol H0 Bool A Y) (_ : ConditionalPairMenu p Δ) (n : ℕ),
      (∀ u, (p.given u).prior.mass true = 1 / 2) ∧
        c ≤ conditionalJointInfo p n (historyBank A Y n) ∧
        x = conditionalExpectedCost p n (historyBank A Y n)}

/-- The infimum `M_c` of the expected cost, in `[0, ∞]`, with the value `∞` on the empty set. -/
noncomputable def mainCost (Δ c : ℝ) : ENNReal :=
  ⨅ x ∈ mainCostSet Δ c, ENNReal.ofReal x

/-- For a reading of discrimination `Δ > 0`, `0 < η ≤ 1/2` and `0 < c ≤ 1 - h(η)`, the infimum
`M_c` lies between `c log 2 / Δ` and `4 log(1/(2η)) / Δ + 1`. -/
theorem mainCost_bounds {Y : Type} [Fintype Y] (P Q : FiniteLaw Y)
    (hΔ : 0 < discrimination P.mass Q.mass) (η c : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hc : c ≤ 1 - Real.binEntropy η / Real.log 2) :
    ENNReal.ofReal (c * Real.log 2 / discrimination P.mass Q.mass) ≤
        mainCost (discrimination P.mass Q.mass) c ∧
      mainCost (discrimination P.mass Q.mass) c ≤
        ENNReal.ofReal (4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass + 1) := by
  constructor
  · apply le_iInf₂
    rintro x ⟨H0, A, Y', _, _, _, p, menu, n, -, hcx, rfl⟩
    exact ENNReal.ofReal_le_ofReal
      (conditionalPairMenu_cost_lower_bound p _ c menu hΔ n _ (historyBank_complete A Y' n) hcx)
  · obtain ⟨N, hinfo, hcost, hN⟩ := (pair_resolution_two_sided P Q hΔ).2 η hη0 hη1
    have hmem : (N : ℝ) ∈ mainCostSet (discrimination P.mass Q.mass) c := by
      refine ⟨Unit, Unit, Y, inferInstance, inferInstance, inferInstance,
        TerminalGapCostExtensions.unitRecordProtocol (repeatProtocol P Q N),
        ⟨fun _ _ => repeatProtocol_pairMenu P Q N⟩, N, fun _ => rfl, ?_, ?_⟩
      · rw [TerminalGapCostExtensions.unitRecordProtocol_information]
        exact hc.trans hinfo
      · rw [TerminalGapCostExtensions.unitRecordProtocol_cost, hcost]
    exact (iInf₂_le _ hmem).trans (ENNReal.ofReal_le_ofReal hN)

/-- For every target `c < 1` some `0 < η < 1/2` has `c ≤ 1 - h(η)`. -/
theorem exists_eta_of_lt_one (c : ℝ) (hc : c < 1) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ c ≤ 1 - Real.binEntropy η / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hε : 0 < (1 - c) * Real.log 2 := mul_pos (by linarith) hlog
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1
    (Real.binEntropy_continuous.continuousAt (x := 0)) _ hε
  refine ⟨min (δ / 2) (1 / 4), lt_min (by linarith) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  have hdist : dist (min (δ / 2) (1 / 4)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (by linarith) (by norm_num))]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h := hball hdist
  rw [Real.binEntropy_zero, Real.dist_eq, sub_zero] at h
  have hlt : Real.binEntropy (min (δ / 2) (1 / 4)) < (1 - c) * Real.log 2 :=
    lt_of_le_of_lt (le_abs_self _) h
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hlog]
  linarith

/-- For a fixed target `0 < c < 1` the infimum `M_c` has order `Δ⁻¹`: one constant `C`, depending
only on `c`, gives `c log 2 / Δ ≤ M_c ≤ C / Δ + 1` for every reading of discrimination `Δ > 0`. -/
theorem mainCost_order (c : ℝ) (hc1 : c < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Y : Type} [Fintype Y] (P Q : FiniteLaw Y),
      0 < discrimination P.mass Q.mass →
        ENNReal.ofReal (c * Real.log 2 / discrimination P.mass Q.mass) ≤
            mainCost (discrimination P.mass Q.mass) c ∧
          mainCost (discrimination P.mass Q.mass) c ≤
            ENNReal.ofReal (C / discrimination P.mass Q.mass + 1) := by
  obtain ⟨η, hη0, hη1, hc⟩ := exists_eta_of_lt_one c hc1
  refine ⟨4 * Real.log (1 / (2 * η)), ?_, fun P Q hΔ => mainCost_bounds P Q hΔ η c hη0 hη1.le hc⟩
  have h1 : 1 < 1 / (2 * η) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have := Real.log_pos h1
  linarith

/-! ## Corollary `cor:exclusive-seed`: the minimum with an independent initial record -/

open ErasureReading ErasurePriorCompletion

/-- A zero-error protocol with an independent initial record, each branch of fixed rows `P, Q`,
prior `w ∈ (0, 1)` and costs at least one, pays at least `w / a + (1 - w) / b`. -/
theorem conditional_zeroError_cost_ge {H0 A Y : Type} [Fintype H0] [Fintype A] [Fintype Y]
    (p : ConditionalProtocol H0 Bool A Y) (P Q : FiniteLaw Y) (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (hr : ∀ u h a z, (p.given u).observation h a z = PairResolution.row P Q z)
    (hprior : ∀ u, (p.given u).prior.mass true = w) (d : H0 → List (A × Y) → Bool)
    (hd : ∀ u, ZeroError (p.given u) (d u)) (hc : ∀ u h a, 1 ≤ (p.given u).cost h a)
    (ha : 0 < exclusiveMass P Q) (hb : 0 < exclusiveMass Q P) :
    ENNReal.ofReal (w / exclusiveMass P Q + (1 - w) / exclusiveMass Q P) ≤
      conditionalExtendedCost p := by
  have hbranch : ∀ u, ENNReal.ofReal (w / exclusiveMass P Q + (1 - w) / exclusiveMass Q P) ≤
      extendedCost (p.given u) := by
    intro u
    have hpos : ∀ z, 0 < (p.given u).prior.mass z := by
      intro z
      have htot := (p.given u).prior.total
      rw [Fintype.sum_bool, hprior u] at htot
      cases z
      · linarith
      · rw [hprior u]; exact hw0
    have := zeroError_cost_ge_weighted_reciprocal (p.given u) P Q (hr u) hpos (d u) (hd u)
      (hc u) ha hb
    rwa [hprior u] at this
  unfold conditionalExtendedCost
  calc ENNReal.ofReal (w / exclusiveMass P Q + (1 - w) / exclusiveMass Q P)
      = (∑ u, ENNReal.ofReal (p.initialRecord.mass u)) *
          ENNReal.ofReal (w / exclusiveMass P Q + (1 - w) / exclusiveMass Q P) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => p.initialRecord.nonnegative u),
          p.initialRecord.total, ENNReal.ofReal_one, one_mul]
    _ = ∑ u, ENNReal.ofReal (p.initialRecord.mass u) *
          ENNReal.ofReal (w / exclusiveMass P Q + (1 - w) / exclusiveMass Q P) := by
        rw [Finset.sum_mul]
    _ ≤ ∑ u, ENNReal.ofReal (p.initialRecord.mass u) * extendedCost (p.given u) :=
        Finset.sum_le_sum fun u _ => mul_le_mul_left' (hbranch u) _

/-! ## Theorem `thm:boundary-singularity`(iii): the increase with an initial record -/

/-- With an initial record, the acquired conditional information increases with the horizon. -/
theorem conditionalJointInfo_mono {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A]
    [Fintype Y] (p : ConditionalProtocol H0 Z A Y) :
    Monotone (fun n => conditionalJointInfo p n (historyBank A Y n)) := by
  intro n m hnm
  simp only
  rw [conditionalJointInfo_eq_conditionalMI p n _ (historyBank_complete A Y n),
    conditionalJointInfo_eq_conditionalMI p m _ (historyBank_complete A Y m)]
  unfold conditionalMI
  exact Finset.sum_le_sum fun u _ =>
    mul_le_mul_of_nonneg_left (terminalMI_mono (p.given u) hnm) (p.initialRecord.nonnegative u)

/-- With an initial record, the expected cost increases with the horizon. -/
theorem conditionalExpectedCost_mono {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A]
    [Fintype Y] (p : ConditionalProtocol H0 Z A Y) :
    Monotone (fun n => conditionalExpectedCost p n (historyBank A Y n)) := by
  intro n m hnm
  simp only
  unfold conditionalExpectedCost
  exact Finset.sum_le_sum fun u _ =>
    mul_le_mul_of_nonneg_left (expectedCost_mono (p.given u) hnm) (p.initialRecord.nonnegative u)

/-! ## Theorem `thm:boundary-singularity`(iv): the pole for arbitrary reading costs -/

/-- Rows of zero discrimination give zero local capacity at every history and action. No
condition on the reading costs enters: the local gain is at most the discrimination over
`log 2`, which is zero. -/
theorem zeroRows_capacity {A Y : Type} [Fintype A] [Fintype Y] (p : FiniteProtocol Bool A Y)
    (hrows : ∀ h a, discrimination (p.observation h a true).mass
      (p.observation h a false).mass = 0) :
    LocalCapacityBound p 0 := by
  intro h a hw _ _
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hgain : localGain p h a ≤ 0 := by
    unfold localGain
    rw [posterior_eq_binaryPrior_of_pos p h hw]
    calc jointMI (fun zy : Bool × Y =>
          binaryPrior (posterior p h true) zy.1 * (p.observation h a zy.1).mass zy.2)
        ≤ discrimination (p.observation h a true).mass (p.observation h a false).mass /
            Real.log 2 :=
          binary_information_le_discrimination (posterior p h true)
            (posterior_nonnegative p h true) (posterior_le_one p h true)
            (fun b => (p.observation h a b).mass)
            (fun b y => (p.observation h a b).nonnegative y)
            (fun b => (p.observation h a b).total)
      _ = 0 := by rw [hrows h a, zero_div]
  simpa only [zero_mul] using hgain

/-- Theorem `thm:boundary-singularity`(iv) for arbitrary nonnegative costs: a protocol whose rows
have discrimination zero at every history and action acquires zero information at every finite
horizon and in the information limit, whatever the reading costs and the total cost. -/
theorem zeroRows_zero_information {A Y : Type} [Fintype A] [Fintype Y]
    (p : FiniteProtocol Bool A Y)
    (hrows : ∀ h a, discrimination (p.observation h a true).mass
      (p.observation h a false).mass = 0) :
    (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧ informationLimit p = 0 := by
  have hc := zeroRows_capacity p hrows
  refine ⟨fun n bank hb => ?_, informationLimit_zero_capacity p hc⟩
  have hu := terminalMI_le_expectedCost p 0 n bank hb hc
  exact le_antisymm (by simpa only [zero_mul] using hu) (terminalMI_nonnegative p n bank hb)

/-- The conditional form: with a finite retained initial record, rows of discrimination zero at
every initial record of positive mass give zero acquired conditional information at every finite
horizon and in the limit, for arbitrary nonnegative reading costs. -/
theorem conditional_zeroRows_zero_information {H0 A Y : Type} [Fintype H0] [Fintype A]
    [Fintype Y] (p : ConditionalProtocol H0 Bool A Y)
    (hrows : ∀ u, 0 < p.initialRecord.mass u → ∀ h a,
      discrimination ((p.given u).observation h a true).mass
        ((p.given u).observation h a false).mass = 0) :
    (∀ n bank, HistoryBank n bank → conditionalJointInfo p n bank = 0) ∧
      conditionalInformationLimit p = 0 := by
  have hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) 0 :=
    fun u hu => zeroRows_capacity (p.given u) (hrows u hu)
  exact ⟨fun n bank hb => conditionalJointInfo_zero_capacity p n bank hb hc,
    conditionalInformationLimit_zero_capacity p hc⟩

/-! ## Theorem `thm:fisher-loss`: the conditional variance form -/

open OperatorKO7.Meta.UUET.Statistics OperatorKO7.Meta.UUET.Probability

/-- The conditional mean of the input score given the output `γ`. -/
noncomputable def condScoreMean {Ω Γ : Type} [Fintype Ω] [Fintype Γ] (F : ParametricFamily Ω)
    (G : ParametricFamily Γ) (K : Channel Ω Γ) (γ : Γ) : ℝ :=
  (∑ ω, F.probability ω * (K.row ω).mass γ * score F ω) / G.probability γ

/-- The conditional variance of the input score given the output `γ`. -/
noncomputable def condScoreVar {Ω Γ : Type} [Fintype Ω] [Fintype Γ] (F : ParametricFamily Ω)
    (G : ParametricFamily Γ) (K : Channel Ω Γ) (γ : Γ) : ℝ :=
  ∑ ω, (F.probability ω * (K.row ω).mass γ / G.probability γ) *
    (score F ω - condScoreMean F G K γ) ^ 2

/-- The output score is the conditional mean of the input score. -/
theorem score_eq_condScoreMean {Ω Γ : Type} [Fintype Ω] [Fintype Γ] (F : ParametricFamily Ω)
    (G : ParametricFamily Γ) (K : Channel Ω Γ)
    (ht : ∀ γ, G.tangent γ = ∑ ω, F.tangent ω * (K.row ω).mass γ) (γ : Γ) :
    score G γ = condScoreMean F G K γ := by
  unfold score condScoreMean
  rw [ht γ]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [← probability_mul_score F ω]
  ring

/-- The Fisher loss is the mean over the outputs of the conditional variance of the input score:
`I_p - I_q = ∑_y q(y) Var(u(X) | Y = y)`. -/
theorem fisher_loss_conditional_variance {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (F : ParametricFamily Ω) (G : ParametricFamily Γ) (K : Channel Ω Γ)
    (hp : ∀ γ, G.probability γ = ∑ ω, F.probability ω * (K.row ω).mass γ)
    (ht : ∀ γ, G.tangent γ = ∑ ω, F.tangent ω * (K.row ω).mass γ) :
    fisherInformation F - fisherInformation G =
      ∑ γ, G.probability γ * condScoreVar F G K γ := by
  rw [fisher_score_residual_identity F G K hp ht]
  apply Finset.sum_congr rfl
  intro γ _
  have hq : G.probability γ ≠ 0 := (G.positive_support γ).ne'
  unfold condScoreVar
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← score_eq_condScoreMean F G K ht γ]
  field_simp

/-! ## Theorem `thm:fisher-loss` for every channel: the output on its attained support -/

section AttainedSupport

open Classical

variable {Ω Γ : Type} [Fintype Ω] [Fintype Γ]

/-- The outputs that the channel `K` reaches with positive probability from the family `F`. -/
abbrev AttainedOutput (F : ParametricFamily Ω) (K : Channel Ω Γ) : Type :=
  {γ : Γ // 0 < ∑ ω, F.probability ω * (K.row ω).mass γ}

/-- A positive channel weight lands on an attained output. -/
theorem attained_of_pos (F : ParametricFamily Ω) (K : Channel Ω Γ) {ω : Ω} {γ : Γ}
    (h : 0 < (K.row ω).mass γ) : 0 < ∑ ω', F.probability ω' * (K.row ω').mass γ :=
  lt_of_lt_of_le (mul_pos (F.positive_support ω) h)
    (Finset.single_le_sum (f := fun ω' => F.probability ω' * (K.row ω').mass γ)
      (fun ω' _ => mul_nonneg (F.probability_nonnegative ω') ((K.row ω').nonnegative γ))
      (Finset.mem_univ ω))

/-- An output that is not attained has weight zero in every row. -/
theorem mass_eq_zero_of_not_attained (F : ParametricFamily Ω) (K : Channel Ω Γ) (ω : Ω) {γ : Γ}
    (hγ : ¬ 0 < ∑ ω', F.probability ω' * (K.row ω').mass γ) : (K.row ω).mass γ = 0 :=
  le_antisymm (not_lt.1 fun h => hγ (attained_of_pos F K h)) ((K.row ω).nonnegative γ)

/-- The channel `K` with its outputs restricted to the attained ones. -/
noncomputable def restrictAttained (F : ParametricFamily Ω) (K : Channel Ω Γ) :
    Channel Ω (AttainedOutput F K) where
  row ω :=
    { mass := fun γ => (K.row ω).mass γ.1
      nonnegative := fun γ => (K.row ω).nonnegative γ.1
      total := by
        have h0 : ∑ γ ∈ Finset.univ.filter
            (fun γ : Γ => ¬ 0 < ∑ ω', F.probability ω' * (K.row ω').mass γ),
            (K.row ω).mass γ = 0 :=
          Finset.sum_eq_zero fun γ hγ =>
            mass_eq_zero_of_not_attained F K ω (Finset.mem_filter.1 hγ).2
        calc ∑ γ : AttainedOutput F K, (K.row ω).mass γ.1
            = ∑ γ ∈ Finset.univ.filter
                (fun γ : Γ => 0 < ∑ ω', F.probability ω' * (K.row ω').mass γ),
                (K.row ω).mass γ :=
              (Finset.sum_subtype _ (fun γ => by simp) _).symm
          _ = ∑ γ ∈ Finset.univ.filter
                (fun γ : Γ => 0 < ∑ ω', F.probability ω' * (K.row ω').mass γ),
                (K.row ω).mass γ +
              ∑ γ ∈ Finset.univ.filter
                (fun γ : Γ => ¬ 0 < ∑ ω', F.probability ω' * (K.row ω').mass γ),
                (K.row ω).mass γ := by rw [h0, add_zero]
          _ = ∑ γ, (K.row ω).mass γ := Finset.sum_filter_add_sum_filter_not _ _ _
          _ = 1 := (K.row ω).total }

/-- The output family of `F` through `K`, on the attained outputs. -/
noncomputable def attainedFamily (F : ParametricFamily Ω) (K : Channel Ω Γ) :
    ParametricFamily (AttainedOutput F K) :=
  F.pushforward (restrictAttained F K) fun γ => γ.2

/-- Theorem `thm:fisher-loss` for every channel `K`, with the output restricted to its attained
support: the Fisher loss is the joint mean of the squared score residual and the output mean of
the conditional variance of the input score; the output information is at most the input
information; and equality holds iff the input score agrees on any two inputs that share an output
of positive weight. -/
theorem fisher_loss_attained (F : ParametricFamily Ω) (K : Channel Ω Γ) :
    fisherInformation F - fisherInformation (attainedFamily F K) =
        ∑ γ, ∑ ω, F.probability ω * ((restrictAttained F K).row ω).mass γ *
          (score F ω - score (attainedFamily F K) γ) ^ 2 ∧
      fisherInformation F - fisherInformation (attainedFamily F K) =
        ∑ γ, (attainedFamily F K).probability γ *
          condScoreVar F (attainedFamily F K) (restrictAttained F K) γ ∧
      fisherInformation (attainedFamily F K) ≤ fisherInformation F ∧
      (fisherInformation (attainedFamily F K) = fisherInformation F ↔
        ∀ ω ω' (γ : Γ), 0 < (K.row ω).mass γ → 0 < (K.row ω').mass γ →
          score F ω = score F ω') := by
  have hp : ∀ γ, (attainedFamily F K).probability γ =
      ∑ ω, F.probability ω * ((restrictAttained F K).row ω).mass γ := fun _ => rfl
  have ht : ∀ γ, (attainedFamily F K).tangent γ =
      ∑ ω, F.tangent ω * ((restrictAttained F K).row ω).mass γ := fun _ => rfl
  refine ⟨fisher_score_residual_identity F _ _ hp ht, fisher_loss_conditional_variance F _ _ hp ht,
    fisher_data_processing_of_pushforward F _ _ hp ht, ?_⟩
  rw [fisher_equality_iff_common_output_scores F _ _ hp ht]
  constructor
  · intro h ω ω' γ h1 h2
    exact h ω ω' ⟨γ, attained_of_pos F K h1⟩ h1 h2
  · intro h ω ω' γ h1 h2
    exact h ω ω' γ.1 h1 h2

/-- Theorem `thm:fisher-loss` for a deterministic observer `f`, on its attained outputs: Fisher
information is preserved iff the input score is constant on every fiber of `f`, and it is lost
strictly iff some fiber holds two different scores. -/
theorem fisher_loss_attained_deterministic [DecidableEq Γ] (F : ParametricFamily Ω)
    (f : Ω → Γ) :
    (fisherInformation (attainedFamily F (Channel.deterministic f)) = fisherInformation F ↔
        ∀ ω ω', f ω = f ω' → score F ω = score F ω') ∧
      (fisherInformation (attainedFamily F (Channel.deterministic f)) < fisherInformation F ↔
        ∃ ω ω', f ω = f ω' ∧ score F ω ≠ score F ω') := by
  obtain ⟨-, -, hle, hiff⟩ := fisher_loss_attained F (Channel.deterministic f)
  have heq : fisherInformation (attainedFamily F (Channel.deterministic f)) =
      fisherInformation F ↔ ∀ ω ω', f ω = f ω' → score F ω = score F ω' := by
    rw [hiff]
    constructor
    · intro h ω ω' hf
      exact h ω ω' (f ω) (by simp) (by rw [hf]; simp)
    · intro h ω ω' γ h1 h2
      have e1 : γ = f ω := by
        by_contra hne
        simp [Channel.deterministic, FiniteDistribution.pointMass_away hne] at h1
      have e2 : γ = f ω' := by
        by_contra hne
        simp [Channel.deterministic, FiniteDistribution.pointMass_away hne] at h2
      exact h ω ω' (e1.symm.trans e2)
  refine ⟨heq, ⟨fun hlt => ?_, fun ⟨ω, ω', hf, hs⟩ => lt_of_le_of_ne hle fun he =>
    hs (heq.1 he ω ω' hf)⟩⟩
  by_contra hno
  push_neg at hno
  exact hlt.ne (heq.2 hno)

end AttainedSupport

/-! ## Theorem `thm:affine-self-certificates`(iii): the two states of a kernel witness -/

section KernelPair

open OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation

variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype I]

/-- Theorem `thm:affine-self-certificates`(iii) on its two states: a solution `p` and a kernel
vector `k` with `L k ≠ 0` give two solutions with one row vector and two target values, so no
function of the row vector returns the target on both states. -/
theorem kernel_pair_no_readout (rows : I → V →ₗ[K] K) (b : I → K) (L : V →ₗ[K] K) (p k : V)
    (hp : Satisfies rows b p) (hk : ∀ i, rows i k = 0) (hl : L k ≠ 0) :
    Satisfies rows b (p + k) ∧ (fun i => rows i (p + k)) = (fun i => rows i p) ∧
      L p ≠ L (p + k) ∧
      ¬ ∃ g : (I → K) → K, g (fun i => rows i p) = L p ∧
        g (fun i => rows i (p + k)) = L (p + k) := by
  obtain ⟨hs, hne⟩ := ambiguity_certificate_sound rows b L p k hp hk hl
  have hrow : (fun i => rows i (p + k)) = fun i => rows i p :=
    funext fun i => by rw [map_add, hk i, add_zero]
  refine ⟨hs, hrow, hne, ?_⟩
  rintro ⟨g, h1, h2⟩
  rw [hrow, h1] at h2
  exact hne h2

end KernelPair

/-! ## Proposition `prop:universal-stable-record`: a record that is not surjective -/

open OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation

/-- A record that determines the observer and is updateable under every permitted action, not
necessarily surjective, has one and only one map from its attained image to the universal stable
record that commutes with the two record maps. -/
theorem minimal_observer_universal_range {X A Q M : Type*} (q : X → Q) (step : A → X → X)
    (m : X → M) (hread : ∀ x y, m x = m y → q x = q y)
    (hstep : ∀ a x y, m x = m y → m (step a x) = m (step a y)) :
    ∃! f : Set.range m → MinimalState q step, ∀ x, f ⟨m x, x, rfl⟩ = minimalRecord q step x := by
  have hsurj : Function.Surjective (fun x : X => (⟨m x, x, rfl⟩ : Set.range m)) := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  exact minimal_observer_universal q step (fun x => (⟨m x, x, rfl⟩ : Set.range m)) hsurj
    (fun x y h => hread x y (congrArg Subtype.val h))
    (fun a x y h => Subtype.ext (hstep a x y (congrArg Subtype.val h)))

/-! ## Corollary `cor:residual-side-stabilizer`: the joint observer -/

open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

/-- The permutations preserving the observer `q` and the side record `s` are the permutations
preserving the joint observer `x ↦ (q x, s x)`. -/
theorem side_stabilizer_eq_joint {X Y S : Type*} (q : X → Y) (s : X → S)
    (σ : Equiv.Perm X) :
    (σ ∈ licenseStabilizer q ∧ ∀ x, s (σ x) = s x) ↔
      σ ∈ licenseStabilizer (fun x => (q x, s x)) := by
  constructor
  · rintro ⟨hq, hs⟩ x
    exact Prod.ext (hq x) (hs x)
  · intro h
    exact ⟨fun x => congrArg Prod.fst (h x), fun x => congrArg Prod.snd (h x)⟩

/-! ## Proposition `prop:demand-budget-transport`: licensed plans under budgets -/

open UniversalObservation.Demand UniversalObservation.Transport

/-- A licensed plan with `k` selector values on `D`: a permitted selector with its combination
permission on `D`, and a selected family that succeeds on `D`. -/
def IsLicensedPlan {I W : Type*} (P : Problem I W) (menu : RepairMenu I W P) (D : Set I) (k : ℕ)
    (s : I → Fin k) (xs : Fin k → W) : Prop :=
  s ∈ menu.allowed k ∧ menu.combines D k s ∧ ∀ i ∈ D, P.sat (xs (s i)) i

/-- A licensed plan meets the budget `b` in every coordinate of a cost of the whole plan. -/
def PlanBudgetFeasible {I W : Type*} (P : Problem I W) (menu : RepairMenu I W P) (D : Set I)
    (k : ℕ) (cost : (I → Fin k) → (Fin k → W) → ℕ → ℝ) (b : ℕ → ℝ) : Prop :=
  ∃ s xs, IsLicensedPlan P menu D k s xs ∧ ∀ j, cost s xs j ≤ b j

/-- Bijections of demands and candidates that carry the satisfaction relation, the permitted
selectors and the combination permission keep budget feasibility of licensed plans, under plan
costs that agree along the correspondence of plans. -/
theorem plan_budget_transport_iff {I J W V : Type*} {P : Problem I W} {Q : Problem J V}
    (e : DemandIso P Q) (p : RepairMenu I W P) (q : RepairMenu J V Q)
    (hm : DemandIso.MenuCorrespondence e p q) (D : Set I) (k : ℕ)
    (c : (I → Fin k) → (Fin k → W) → ℕ → ℝ) (d : (J → Fin k) → (Fin k → V) → ℕ → ℝ)
    (hc : ∀ s xs j, d (e.selector s) (e.witnesses ∘ xs) j = c s xs j) (b : ℕ → ℝ) :
    PlanBudgetFeasible Q q (e.demands '' D) k d b ↔ PlanBudgetFeasible P p D k c b := by
  constructor
  · rintro ⟨t, ys, ⟨ht, htc, hsat⟩, hb⟩
    let s : I → Fin k := fun i => t (e.demands i)
    have he : e.selector s = t := by
      funext j
      simp [DemandIso.selector, s]
    have hys : e.witnesses ∘ (e.witnesses.symm ∘ ys) = ys := by
      funext j
      simp
    refine ⟨s, e.witnesses.symm ∘ ys, ⟨(hm.allowed k s).mp (by rw [he]; exact ht),
      (hm.combines D k s).mp (by rw [he]; exact htc), fun i hi => ?_⟩, fun j => ?_⟩
    · have h := hsat (e.demands i) ⟨i, hi, rfl⟩
      apply (e.satisfaction _ i).mp
      simpa [s] using h
    · rw [← hc, he, hys]
      exact hb j
  · rintro ⟨s, xs, ⟨hs, hsc, hsat⟩, hb⟩
    refine ⟨e.selector s, e.witnesses ∘ xs, ⟨(hm.allowed k s).mpr hs, (hm.combines D k s).mpr hsc,
      ?_⟩, fun j => (hc s xs j).trans_le (hb j)⟩
    rintro j ⟨i, hi, rfl⟩
    simpa [DemandIso.selector] using (e.satisfaction _ i).mpr (hsat i hi)

/-! ## Proposition `prop:burden-cutoff-bound`: the depth ratio -/

/-- For `β > 0` and `L > 0`, the depth ratio `r_m = exp(-β L (m + 2))` lies strictly between zero
and one. -/
theorem depth_ratio_bounds (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (m : ℕ) :
    0 < Real.exp (-β * ((m : ℝ) + 2) * L) ∧ Real.exp (-β * ((m : ℝ) + 2) * L) < 1 := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have h : 0 < β * ((m : ℝ) + 2) * L := by positivity
  exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by nlinarith)⟩

/-! ## Theorem `thm:frontier-transport`(iii) at zero bias: zero information at every horizon -/

/-- Theorem `thm:frontier-transport`(iii) at `ε = 0`: every admissible strategy of a binary task of
bias zero acquires zero information at every finite horizon, and its information limit is zero. -/
theorem binaryTask_zero_information {H0 A V R ι : Type} [Fintype H0] [Fintype A]
    {T : ProtocolTask H0 Bool A Bool V R ι} {j : ι} (m : BinaryTask T 0 j)
    (σ : ProtocolStrategy H0 A Bool R) (hσ : T.Admissible σ) :
    (∀ n, T.information σ n = 0) ∧ T.informationLimitOf σ = 0 := by
  refine ⟨fun n => le_antisymm ?_ (T.information_nonnegative σ n), m.limit_zero_capacity σ hσ⟩
  have h0 := m.information_le_cost (by norm_num) σ hσ n
  norm_num at h0
  exact h0

/-! ## Section `sec:persistent-positive-cost`: the discrimination and the information at state `n` -/

/-- Section `sec:persistent-positive-cost`: at state `n` the two rows of the binary symmetric
reading of bias `ε_n` have discrimination `(1/2)^(2n+1)`, and the fair reading carries
`1 - h_b(1/2 + ε_n)` bits. -/
theorem persistent_state_values (n : ℕ) :
    PersistentBinaryEvidence.discrimination n = (1 / 2) ^ (2 * n + 1) ∧
      jointMI (PersistentBinaryEvidence.fairJointLaw n).mass =
        1 - Real.binEntropy (1 / 2 + PersistentBinaryEvidence.epsilon n) / Real.log 2 := by
  refine ⟨?_, ?_⟩
  · rw [PersistentBinaryEvidence.discrimination_eq_eight_mul_sq, PersistentBinaryEvidence.epsilon]
    ring
  · change jointMI (binaryJoint (1 / 2) (PersistentBinaryEvidence.epsilon n)) = _
    exact binaryJoint_information_fair _

end OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleProtocols
