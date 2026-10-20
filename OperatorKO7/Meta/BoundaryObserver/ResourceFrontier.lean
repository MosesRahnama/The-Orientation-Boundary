import OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
import OperatorKO7.Meta.BoundaryObserver.ResolutionAttainment
import OperatorKO7.Meta.BoundaryObserver.DemandTransport

set_option autoImplicit false

/-!
# The resource frontier of weak-signal resolution

Graph: notes/universal-roadmap/UNIVERSAL-OBSERVATION-PROOF-GRAPH.md, M3_4 and M3_5.
Contract: UniversalObservationSpec.lean, namespaces Protocol and Transport; no specification import.
The minimum cost is ProtocolTask.minimumCost of one concrete task family: a fair hidden bit read
through binary symmetric readings of bias ε at unit price per reading. It is not a supplied real.
The lower bound is the all-strategy inverse-square price of ProtocolResolution; the upper bound is
the majority protocol of ResolutionAttainment, carried into the task by a protocol isomorphism.
The same two bounds hold for the least extended cost of the unbounded experiment.
Budget transport is the witness-preserving demand isomorphism of DemandTransport.
Relation: finite stopped laws of one task family; demand incidence. External trust: none.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ResourceFrontier

open scoped BigOperators ENNReal

section SharpScaling
open ProtocolResolution ResolutionAttainment

/-! ## The task family of one hidden bit and its readings -/

/-- The reading bias clipped into `[0, 1/2]`, so that every real argument names a probability
kernel; on that interval it is the argument itself. -/
noncomputable def readingBias (ε : ℝ) : ℝ := max 0 (min ε (1 / 2))

theorem readingBias_abs_le (ε : ℝ) : |readingBias ε| ≤ 1 / 2 := by
  unfold readingBias
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le (by norm_num) (min_le_right _ _)

theorem readingBias_of_mem {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : readingBias ε = ε := by
  unfold readingBias
  rw [min_eq_left h1, max_eq_right h0]

/-- The fair hidden bit, binary symmetric readings of bias `readingBias ε`, one unit of cost per
reading, readouts from the whole retained history, and every readout licensed. -/
noncomputable def resolutionTask (ε : ℝ) :
    ProtocolTask Unit Bool Unit Bool Bool (List (Unit × Bool) → Option Bool) Unit :=
  binaryTask (1 / 2) (readingBias ε) 1 True (by norm_num) (by norm_num) (readingBias_abs_le ε)
    zero_le_one

/-- Each task of the family is a binary task of its own bias at one unit per reading. -/
noncomputable def resolutionTask_binary (ε : ℝ) :
    BinaryTask (resolutionTask ε) |readingBias ε| () :=
  binaryTask_binary (1 / 2) (readingBias ε) 1 True (by norm_num) (by norm_num)
    (readingBias_abs_le ε) zero_le_one le_rfl

/-- At least `c` bits about the hidden bit; error and refusal masses at most one, which every
stopped law meets; the budget coordinate is not read by the minimum cost. -/
def informationRequirement (c : ℝ) : ProtocolRequirement Unit where
  information := c
  error := 1
  refusal := 1
  budget _ := 0

/-- The least expected number of readings, over every horizon and every admissible strategy of
the task, that acquires at least `c` bits at bias `ε`. -/
noncomputable def resolutionMinimumCost (c ε : ℝ) : ℝ :=
  (⨅ n : ℕ, (resolutionTask ε).minimumCost n (informationRequirement c) ()).toReal

/-- The least extended expected number of readings of an admissible unbounded experiment that
acquires at least `c` bits at bias `ε`. -/
noncomputable def resolutionLimitMinimumCost (c ε : ℝ) : ℝ :=
  ((resolutionTask ε).limitMinimumCost c ()).toReal

/-! ## The majority strategy inside the task -/

/-- Read until `N` readings are retained, then report `answer` of the history. -/
def readingStrategy (N : ℕ) (answer : List (Unit × Bool) → Option Bool) :
    ProtocolStrategy Unit Unit Bool (List (Unit × Bool) → Option Bool) where
  policy _ _ := unitLaw
  stop _ h := decide (N ≤ h.length)
  repair := answer

theorem readingStrategy_admissible (ε : ℝ) (N : ℕ) (answer : List (Unit × Bool) → Option Bool) :
    (resolutionTask ε).Admissible (readingStrategy N answer) :=
  ⟨trivial, fun _ _ _ _ _ => trivial⟩

/-- The charged protocol of the reading strategy is the majority protocol of ResolutionAttainment,
up to identity renamings: the prior masses, the kernels, the stopping rule and the unit cost agree
at every history. -/
def readingIso (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (N : ℕ)
    (answer : List (Unit × Bool) → Option Bool) :
    FiniteProtocolIso (((resolutionTask ε).costConditional (readingStrategy N answer) ()).given ())
      (majorityProtocol ε hε0 hε1 N) where
  input := Equiv.refl Bool
  action := Equiv.refl Unit
  outcome := Equiv.refl Bool
  prior z := by
    show (1 : ℝ) / 2 = binaryPrior (1 / 2) z
    cases z <;> norm_num [binaryPrior]
  policy _ _ := rfl
  observation _ _ z y := by
    show binaryKernel ε z y = binaryKernel (readingBias ε) z y
    rw [readingBias_of_mem hε0 hε1]
  stopping h := by
    show decide (N ≤ (historyEquiv (Equiv.refl Unit) (Equiv.refl Bool) h).length) =
      decide (N ≤ h.length)
    rw [historyEquiv_length]
  cost _ _ := rfl

/-- The information of the reading strategy at its own horizon is that of the majority protocol. -/
theorem readingStrategy_information (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (N : ℕ)
    (answer : List (Unit × Bool) → Option Bool) :
    (resolutionTask ε).information (readingStrategy N answer) N =
      terminalMI (majorityProtocol ε hε0 hε1 N) N (historyBank Unit Bool N) := by
  rw [ProtocolTask.information_eq_cost _ _ N (),
    conditionalJointInfo_eq_conditionalMI _ N _ (historyBank_complete Unit Bool N)]
  unfold conditionalMI
  rw [Fintype.sum_unique]
  change 1 * terminalMI _ N _ = _
  rw [one_mul]
  exact ((readingIso ε hε0 hε1 N answer).terminalMI_transport N _ _
    (historyBank_complete Unit Bool N) (historyBank_complete Unit Bool N)).symm

/-- The reading strategy pays one unit per reading: `N` at horizon `N`. -/
theorem readingStrategy_cost (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (N : ℕ)
    (answer : List (Unit × Bool) → Option Bool) :
    (resolutionTask ε).expectedCostAt (readingStrategy N answer) N () = N := by
  unfold ProtocolTask.expectedCostAt conditionalExpectedCost
  rw [Fintype.sum_unique]
  change 1 * expectedCost _ N _ = _
  rw [one_mul]
  refine ((readingIso ε hε0 hε1 N answer).expectedCost_transport N _).symm.trans ?_
  exact (expectedCost_bank _ (historyBank_map _ _ (historyBank_complete Unit Bool N))
    (historyBank_complete Unit Bool N)).trans (majority_cost ε hε0 hε1 N)

/-- Beyond its horizon the majority protocol pays nothing more: its cost is `N` at every later
horizon. -/
theorem majority_expectedCost_of_le (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) {N m : ℕ}
    (hNm : N ≤ m) :
    expectedCost (majorityProtocol ε hε0 hε1 N) m (historyBank Unit Bool m) = N := by
  rw [expectedCost_eq_historyCost, ← majority_cost ε hε0 hε1 N, expectedCost_eq_historyCost]
  symm
  apply Finset.sum_subset
  · intro h hh
    rw [mem_chargedHistorySet] at hh ⊢
    omega
  · intro h _ hh
    rw [mem_chargedHistorySet, not_lt] at hh
    have hs : (majorityProtocol ε hε0 hε1 N).stop h = true := by
      rw [majorityProtocol_stop]
      exact decide_eq_true hh
    simp [historyCost, hs]

/-- The extended cost of the majority protocol is exactly `N`. -/
theorem majority_extendedCost (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (N : ℕ) :
    extendedCost (majorityProtocol ε hε0 hε1 N) = ENNReal.ofReal N := by
  apply le_antisymm
  · rw [extendedCost_le_iff _ _ (Nat.cast_nonneg N)]
    intro m
    calc expectedCost (majorityProtocol ε hε0 hε1 N) m (historyBank Unit Bool m)
        ≤ expectedCost (majorityProtocol ε hε0 hε1 N) (max m N) (historyBank Unit Bool (max m N)) :=
          expectedCost_mono _ (le_max_left m N)
      _ = N := majority_expectedCost_of_le ε hε0 hε1 (le_max_right m N)
  · rw [← majority_cost ε hε0 hε1 N]
    exact finiteCost_le_extendedCost _ N

/-- The information limit of the reading strategy is that of the majority protocol. -/
theorem readingStrategy_informationLimit (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (N : ℕ)
    (answer : List (Unit × Bool) → Option Bool) :
    (resolutionTask ε).informationLimitOf (readingStrategy N answer) =
      informationLimit (majorityProtocol ε hε0 hε1 N) := by
  rw [ProtocolTask.informationLimitOf_eq_cost _ _ ()]
  unfold conditionalInformationLimit
  rw [Fintype.sum_unique]
  change 1 * informationLimit _ = _
  rw [one_mul]
  exact ((readingIso ε hε0 hε1 N answer).informationLimit_transport).symm

/-- The extended cost of the reading strategy is `N`. -/
theorem readingStrategy_extendedCost (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (N : ℕ)
    (answer : List (Unit × Bool) → Option Bool) :
    (resolutionTask ε).extendedCostOf (readingStrategy N answer) () = ENNReal.ofReal N := by
  unfold ProtocolTask.extendedCostOf conditionalExtendedCost
  rw [Fintype.sum_unique]
  change ENNReal.ofReal 1 * extendedCost _ = _
  rw [ENNReal.ofReal_one, one_mul, ← majority_extendedCost ε hε0 hε1 N]
  exact (readingIso ε hε0 hε1 N answer).extendedCost_transport.symm

/-! ## The two-sided bounds -/

/-- An error level whose binary entropy leaves at least `c` bits, for every `c < 1`. -/
theorem exists_error_level (c : ℝ) (hc : c < 1) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ c ≤ 1 - Real.binEntropy η / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have ht : 0 < (1 - c) * Real.log 2 := mul_pos (by linarith) hlog
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp Real.binEntropy_continuous 0 _ ht
  have hpos : 0 < min (δ / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  refine ⟨min (δ / 2) (1 / 2), hpos, min_le_right _ _, ?_⟩
  have hd : dist (min (δ / 2) (1 / 2)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hb := hball _ hd
  rw [Real.dist_eq, Real.binEntropy_zero, sub_zero] at hb
  have hq : Real.binEntropy (min (δ / 2) (1 / 2)) / Real.log 2 ≤ 1 - c := by
    rw [div_le_iff₀ hlog]
    linarith [le_abs_self (Real.binEntropy (min (δ / 2) (1 / 2)))]
  linarith

/-- Both sides with explicit constants: for every error level `η` in `(0, 1/2]` whose binary
entropy leaves at least `c` bits, the least cost of `c` bits at bias `ε` in `(0, 1/2]` lies between
`c/(4ε²)` and `log(1/(2η))/(2ε²) + 3`. -/
theorem resolutionMinimumCost_bounds (c ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) (hc : c ≤ 1 - Real.binEntropy η / Real.log 2) :
    c / (4 * ε ^ 2) ≤ resolutionMinimumCost c ε ∧
      resolutionMinimumCost c ε ≤ Real.log (1 / (2 * η)) / (2 * ε ^ 2) + 3 := by
  obtain ⟨hinfo, -, hN⟩ := majority_target ε hε0.le hε1 hε0 η hη0 hη1
  set N := 2 * ⌈Real.log (1 / (2 * η)) / (4 * ε ^ 2)⌉₊ + 1
  have hq : (resolutionTask ε).Qualifies (readingStrategy N (fun _ => none)) N
      (informationRequirement c) := by
    refine ⟨readingStrategy_admissible ε N _, ?_, ?_, ?_⟩
    · show c ≤ _
      rw [readingStrategy_information ε hε0.le hε1 N]
      exact hc.trans hinfo
    · rw [ProtocolTask.errorMass_eq_zero_of_refuses (resolutionTask ε)
        (readingStrategy N (fun _ => none)) N (fun _ _ => rfl)]
      exact zero_le_one
    · rw [ProtocolTask.refusalMass_eq_one_of_refuses (resolutionTask ε)
        (readingStrategy N (fun _ => none)) N (fun _ _ => rfl)]
      exact le_rfl
  have hup : (⨅ n : ℕ, (resolutionTask ε).minimumCost n (informationRequirement c) ()) ≤
      ENNReal.ofReal N := by
    calc (⨅ n : ℕ, (resolutionTask ε).minimumCost n (informationRequirement c) ())
        ≤ (resolutionTask ε).minimumCost N (informationRequirement c) () := iInf_le _ N
      _ ≤ ENNReal.ofReal ((resolutionTask ε).expectedCostAt
            (readingStrategy N (fun _ => none)) N ()) :=
          iInf₂_le (readingStrategy N (fun _ => none)) hq
      _ = ENNReal.ofReal N := by rw [readingStrategy_cost ε hε0.le hε1 N]
  have hbias : |readingBias ε| = ε := by rw [readingBias_of_mem hε0.le hε1, abs_of_pos hε0]
  have hlow : ENNReal.ofReal (c / (4 * ε ^ 2)) ≤
      ⨅ n : ℕ, (resolutionTask ε).minimumCost n (informationRequirement c) () := by
    refine le_iInf fun n => ?_
    have k := (resolutionTask_binary ε).minimumCost_lower (by rw [hbias]; exact hε0)
      (by rw [hbias]; exact hε1) n (informationRequirement c)
    rw [hbias] at k
    exact k
  have hfin : (⨅ n : ℕ, (resolutionTask ε).minimumCost n (informationRequirement c) ()) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  exact ⟨(ENNReal.ofReal_le_iff_le_toReal hfin).mp hlow,
    (ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg N) hup).trans hN⟩

/-- The same explicit bounds for the least extended cost of the unbounded experiment, where a
strategy may also run without stopping. -/
theorem resolutionLimitMinimumCost_bounds (c ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) (hc : c ≤ 1 - Real.binEntropy η / Real.log 2) :
    c / (4 * ε ^ 2) ≤ resolutionLimitMinimumCost c ε ∧
      resolutionLimitMinimumCost c ε ≤ Real.log (1 / (2 * η)) / (2 * ε ^ 2) + 3 := by
  obtain ⟨hinfo, -, hN⟩ := majority_target ε hε0.le hε1 hε0 η hη0 hη1
  set N := 2 * ⌈Real.log (1 / (2 * η)) / (4 * ε ^ 2)⌉₊ + 1
  have hq : (resolutionTask ε).Admissible (readingStrategy N (fun _ => none)) ∧
      c ≤ (resolutionTask ε).informationLimitOf (readingStrategy N (fun _ => none)) := by
    refine ⟨readingStrategy_admissible ε N _, ?_⟩
    rw [readingStrategy_informationLimit ε hε0.le hε1 N]
    exact (hc.trans hinfo).trans (terminalMI_le_informationLimit _ N)
  have hup : (resolutionTask ε).limitMinimumCost c () ≤ ENNReal.ofReal N := by
    calc (resolutionTask ε).limitMinimumCost c ()
        ≤ (resolutionTask ε).extendedCostOf (readingStrategy N (fun _ => none)) () :=
          iInf₂_le (readingStrategy N (fun _ => none)) hq
      _ = ENNReal.ofReal N := readingStrategy_extendedCost ε hε0.le hε1 N _
  have hbias : |readingBias ε| = ε := by rw [readingBias_of_mem hε0.le hε1, abs_of_pos hε0]
  have hlow : ENNReal.ofReal (c / (4 * ε ^ 2)) ≤ (resolutionTask ε).limitMinimumCost c () := by
    have k := (resolutionTask_binary ε).limitMinimumCost_lower (by rw [hbias]; exact hε0)
      (by rw [hbias]; exact hε1) c
    rw [hbias] at k
    exact k
  have hfin : (resolutionTask ε).limitMinimumCost c () ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  exact ⟨(ENNReal.ofReal_le_iff_le_toReal hfin).mp hlow,
    (ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg N) hup).trans hN⟩

theorem log_inv_two_mul_nonneg {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) :
    0 ≤ Real.log (1 / (2 * η)) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- A function bounded below by `c/(4ε²)` and above by `L/(2ε²) + 3` on `(0, 1/2]` is of order
`ε⁻²` from both sides, with `A = c/4`, `B = L/2 + 3/4` and `ε0 = 1/2`. -/
theorem inverseSquare_of_bounds (g : ℝ → ℝ) (c L : ℝ) (hc : 0 < c) (hL : 0 ≤ L)
    (hg : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → c / (4 * ε ^ 2) ≤ g ε ∧ g ε ≤ L / (2 * ε ^ 2) + 3) :
    ∃ A B ε0 : ℝ, 0 < A ∧ 0 < B ∧ 0 < ε0 ∧
      ∀ ε, 0 < ε → ε < ε0 → A / ε ^ 2 ≤ g ε ∧ g ε ≤ B / ε ^ 2 := by
  refine ⟨c / 4, L / 2 + 3 / 4, 1 / 2, by linarith, by linarith, by norm_num, ?_⟩
  intro ε hε0 hε1
  obtain ⟨hlo, hhi⟩ := hg ε hε0 hε1.le
  have he2 : 0 < ε ^ 2 := pow_pos hε0 2
  have hsq : ε ^ 2 ≤ 1 / 4 := by nlinarith
  refine ⟨by rw [div_div]; exact hlo, ?_⟩
  rw [le_div_iff₀ he2]
  calc g ε * ε ^ 2 ≤ (L / (2 * ε ^ 2) + 3) * ε ^ 2 := mul_le_mul_of_nonneg_right hhi he2.le
    _ = L / 2 + 3 * ε ^ 2 := by rw [add_mul, div_mul_eq_mul_div, mul_div_mul_right L 2 he2.ne']
    _ ≤ L / 2 + 3 / 4 := by linarith

/-- Both upper and lower bounds use a single represented experiment family. -/
def SharpScalingGoal (minimumCost : ℝ → ℝ → ℝ) : Prop :=
  ∀ c, 0 < c → c < 1 → ∃ A B ε0 : ℝ, 0 < A ∧ 0 < B ∧ 0 < ε0 ∧
    ∀ ε, 0 < ε → ε < ε0 → A / ε^2 ≤ minimumCost c ε ∧ minimumCost c ε ≤ B / ε^2

/-- Explicit two-sided bounds of the stated shape give the inverse-square scaling, with
`A = c/4`, `B = log(1/(2η))/2 + 3/4` and `ε0 = 1/2`. -/
theorem sharpScaling_of_bounds (f : ℝ → ℝ → ℝ)
    (hf : ∀ c ε η : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < η → η ≤ 1 / 2 →
      c ≤ 1 - Real.binEntropy η / Real.log 2 →
        c / (4 * ε ^ 2) ≤ f c ε ∧ f c ε ≤ Real.log (1 / (2 * η)) / (2 * ε ^ 2) + 3) :
    SharpScalingGoal f := by
  intro c hc0 hc1
  obtain ⟨η, hη0, hη1, hcη⟩ := exists_error_level c hc1
  exact inverseSquare_of_bounds (f c) c (Real.log (1 / (2 * η))) hc0
    (log_inv_two_mul_nonneg hη0 hη1) (fun ε h0 h1 => hf c ε η h0 h1 hη0 hη1 hcη)

/-- M3.4: the least cost of every fixed information target below one bit is of order `ε⁻²` from
both sides, on the task family whose minimum cost is ProtocolTask.minimumCost. -/
theorem sharpScalingGoal : SharpScalingGoal resolutionMinimumCost :=
  sharpScaling_of_bounds _ resolutionMinimumCost_bounds

/-- The same scaling for the least extended cost of the unbounded experiment. -/
theorem sharpScalingGoal_limit : SharpScalingGoal resolutionLimitMinimumCost :=
  sharpScaling_of_bounds _ resolutionLimitMinimumCost_bounds

/-! ## The cost-confidence tradeoff

The majority answer is the repair witness. The requirement adds an error mass of at most `η` and
no refusal to the information target, so a strategy that refuses cannot meet it. -/

/-- At least `c` bits, error mass at most `η` and no refusal. -/
def confidenceRequirement (c η : ℝ) : ProtocolRequirement Unit where
  information := c
  error := η
  refusal := 0
  budget _ := 0

/-- The least expected number of readings, over every horizon and every admissible strategy, that
acquires at least `c` bits and answers with error mass at most `η` and no refusal. -/
noncomputable def confidenceMinimumCost (c η ε : ℝ) : ℝ :=
  (⨅ n : ℕ, (resolutionTask ε).minimumCost n (confidenceRequirement c η) ()).toReal

/-- The majority value of the retained readings, reported as an answer. -/
def majorityAnswer (n : ℕ) (h : List (Unit × Bool)) : Option Bool := some (majority n h)

theorem resolutionTask_record (ε : ℝ) (u : Unit) : (resolutionTask ε).initialRecord.mass u = 1 :=
  rfl

/-- The stopped law of the reading strategy is the stopped law of the majority protocol. -/
theorem readingStrategy_stoppedMass (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (N : ℕ)
    (answer : List (Unit × Bool) → Option Bool) (u : Unit) (z : Bool) (h : List (Unit × Bool)) :
    stoppedMass (((resolutionTask ε).lawConditional (readingStrategy N answer)).given u) N z h =
      stoppedMass (majorityProtocol ε hε0 hε1 N) N z h := by
  cases u
  have k := (readingIso ε hε0 hε1 N answer).stoppedMass_transport N z h
  rw [show historyEquiv (readingIso ε hε0 hε1 N answer).action
      (readingIso ε hε0 hε1 N answer).outcome h = h from historyEquiv_refl h] at k
  exact k.symm

/-- The error mass of the majority answer is the stopped mass of the rejected label. -/
theorem readingStrategy_errorMass (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (n : ℕ) :
    (resolutionTask ε).errorMass (readingStrategy (2 * n + 1) (majorityAnswer n)) (2 * n + 1) =
      ∑ h ∈ historySet (Unit × Bool) (2 * n + 1),
        stoppedMass (majorityProtocol ε hε0 hε1 (2 * n + 1)) (2 * n + 1) (!majority n h) h := by
  have hb := historyBank_complete Unit Bool (2 * n + 1)
  calc (resolutionTask ε).errorMass (readingStrategy (2 * n + 1) (majorityAnswer n)) (2 * n + 1)
      = ∑ z : Bool, ∑ h ∈ historySet (Unit × Bool) (2 * n + 1),
          stoppedMass (majorityProtocol ε hε0 hε1 (2 * n + 1)) (2 * n + 1) z h *
            errorLoss z (some (majority n h)) := by
        unfold ProtocolTask.errorMass FiniteProtocolIso.stoppedExpectation
        simp only [Fintype.sum_unique, resolutionTask_record, one_mul]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [hb.sum_eq]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [readingStrategy_stoppedMass ε hε0 hε1]
        rfl
    _ = ∑ h ∈ historySet (Unit × Bool) (2 * n + 1), ∑ z : Bool,
          stoppedMass (majorityProtocol ε hε0 hε1 (2 * n + 1)) (2 * n + 1) z h *
            errorLoss z (some (majority n h)) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Fintype.sum_bool]
        rcases Bool.eq_false_or_eq_true (majority n h) with hm | hm <;> rw [hm] <;>
          simp [errorLoss]

/-- The majority answer never refuses. -/
theorem readingStrategy_refusalMass (ε : ℝ) (N n : ℕ) :
    (resolutionTask ε).refusalMass (readingStrategy N (majorityAnswer n)) N = 0 := by
  unfold ProtocolTask.refusalMass
  exact Finset.sum_eq_zero fun _ _ =>
    mul_eq_zero_of_right _ (stoppedExpectation_const_zero _ N _)

/-- Both sides of the cost-confidence tradeoff with explicit constants: `c` bits with error mass at
most `η` and no refusal cost at least `c/(4ε²)` and at most `log(1/(2η))/(2ε²) + 3` readings,
whenever the binary entropy of `η` leaves at least `c` bits. -/
theorem confidenceMinimumCost_bounds (c η ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) (hc : c ≤ 1 - Real.binEntropy η / Real.log 2) :
    c / (4 * ε ^ 2) ≤ confidenceMinimumCost c η ε ∧
      confidenceMinimumCost c η ε ≤ Real.log (1 / (2 * η)) / (2 * ε ^ 2) + 3 := by
  obtain ⟨hinfo, -, hN⟩ := majority_target ε hε0.le hε1 hε0 η hη0 hη1
  set n := ⌈Real.log (1 / (2 * η)) / (4 * ε ^ 2)⌉₊
  have hε2 : 0 < 4 * ε ^ 2 := by positivity
  have hnle : Real.log (1 / (2 * η)) / (4 * ε ^ 2) ≤ n := Nat.le_ceil _
  have herr : 1 / 2 * (1 - 4 * ε ^ 2) ^ n ≤ η := by
    have h1 := majority_error_le_exp ε hε0.le hε1 n
    have hle : Real.log (1 / (2 * η)) ≤ 4 * n * ε ^ 2 := by
      rw [div_le_iff₀ hε2] at hnle
      linarith
    have h2 : Real.exp (-(4 * n * ε ^ 2)) ≤ 2 * η := by
      calc Real.exp (-(4 * n * ε ^ 2)) ≤ Real.exp (-Real.log (1 / (2 * η))) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = 2 * η := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
    linarith
  have hq : (resolutionTask ε).Qualifies (readingStrategy (2 * n + 1) (majorityAnswer n))
      (2 * n + 1) (confidenceRequirement c η) := by
    refine ⟨readingStrategy_admissible ε (2 * n + 1) _, ?_, ?_, ?_⟩
    · show c ≤ _
      rw [readingStrategy_information ε hε0.le hε1 (2 * n + 1)]
      exact hc.trans hinfo
    · show _ ≤ η
      rw [readingStrategy_errorMass ε hε0.le hε1 n]
      exact (majority_error_le ε hε0.le hε1 n).trans herr
    · show _ ≤ 0
      rw [readingStrategy_refusalMass ε (2 * n + 1) n]
  have hup : (⨅ m : ℕ, (resolutionTask ε).minimumCost m (confidenceRequirement c η) ()) ≤
      ENNReal.ofReal ((2 * n + 1 : ℕ) : ℝ) := by
    calc (⨅ m : ℕ, (resolutionTask ε).minimumCost m (confidenceRequirement c η) ())
        ≤ (resolutionTask ε).minimumCost (2 * n + 1) (confidenceRequirement c η) () :=
          iInf_le _ (2 * n + 1)
      _ ≤ ENNReal.ofReal ((resolutionTask ε).expectedCostAt
            (readingStrategy (2 * n + 1) (majorityAnswer n)) (2 * n + 1) ()) :=
          iInf₂_le (readingStrategy (2 * n + 1) (majorityAnswer n)) hq
      _ = ENNReal.ofReal ((2 * n + 1 : ℕ) : ℝ) := by
          rw [readingStrategy_cost ε hε0.le hε1 (2 * n + 1)]
  have hbias : |readingBias ε| = ε := by rw [readingBias_of_mem hε0.le hε1, abs_of_pos hε0]
  have hlow : ENNReal.ofReal (c / (4 * ε ^ 2)) ≤
      ⨅ m : ℕ, (resolutionTask ε).minimumCost m (confidenceRequirement c η) () := by
    refine le_iInf fun m => ?_
    have k := (resolutionTask_binary ε).minimumCost_lower (by rw [hbias]; exact hε0)
      (by rw [hbias]; exact hε1) m (confidenceRequirement c η)
    rw [hbias] at k
    exact k
  have hfin : (⨅ m : ℕ, (resolutionTask ε).minimumCost m (confidenceRequirement c η) ()) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  exact ⟨(ENNReal.ofReal_le_iff_le_toReal hfin).mp hlow,
    (ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg _) hup).trans hN⟩

/-- For every error level `η` in `(0, 1/2]` and every positive target `c` that its binary entropy
leaves, the least cost of `c` bits with error mass at most `η` and no refusal is of order `ε⁻²`
from both sides. -/
theorem confidence_sharpScaling (c η : ℝ) (hc0 : 0 < c) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hc : c ≤ 1 - Real.binEntropy η / Real.log 2) :
    ∃ A B ε0 : ℝ, 0 < A ∧ 0 < B ∧ 0 < ε0 ∧
      ∀ ε, 0 < ε → ε < ε0 →
        A / ε ^ 2 ≤ confidenceMinimumCost c η ε ∧ confidenceMinimumCost c η ε ≤ B / ε ^ 2 :=
  inverseSquare_of_bounds (fun ε => confidenceMinimumCost c η ε) c (Real.log (1 / (2 * η))) hc0
    (log_inv_two_mul_nonneg hη0 hη1)
    (fun ε h0 h1 => confidenceMinimumCost_bounds c η ε h0 h1 hη0 hη1 hc)


/-! ## Exported finiteness of the extended minimum costs -/

/-- The source extended infimum underlying the real-valued information minimum. -/
noncomputable def resolutionMinimumCostExtended (c ε : ℝ) : ℝ≥0∞ :=
  ⨅ n : ℕ, (resolutionTask ε).minimumCost n (informationRequirement c) ()

/-- The source extended infimum for unbounded-time information acquisition. -/
noncomputable def resolutionLimitMinimumCostExtended (c ε : ℝ) : ℝ≥0∞ :=
  (resolutionTask ε).limitMinimumCost c ()

/-- The source extended infimum for information, bounded error and no refusal. -/
noncomputable def confidenceMinimumCostExtended (c η ε : ℝ) : ℝ≥0∞ :=
  ⨅ n : ℕ, (resolutionTask ε).minimumCost n (confidenceRequirement c η) ()

/-- Exact source identification: the real information minimum is the finite-value
projection of its extended infimum, not an independently supplied cost. -/
theorem resolutionMinimumCost_eq_extended (c ε : ℝ) :
    resolutionMinimumCost c ε = (resolutionMinimumCostExtended c ε).toReal := rfl

/-- Exact source identification for the unbounded-horizon extended infimum. -/
theorem resolutionLimitMinimumCost_eq_extended (c ε : ℝ) :
    resolutionLimitMinimumCost c ε = (resolutionLimitMinimumCostExtended c ε).toReal := rfl

/-- Exact source identification for the no-refusal confidence minimum. -/
theorem confidenceMinimumCost_eq_extended (c η ε : ℝ) :
    confidenceMinimumCost c η ε = (confidenceMinimumCostExtended c η ε).toReal := rfl

/-- One majority strategy qualifies for the confidence, information and limit tasks.
Its information and cost are computed from the same stopped law and the information limit. -/
theorem majorityStrategy_finite_witness (c η ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hc : c ≤ 1 - Real.binEntropy η / Real.log 2) :
    ∃ n : ℕ,
      (resolutionTask ε).Qualifies
        (readingStrategy (2 * n + 1) (majorityAnswer n)) (2 * n + 1)
        (confidenceRequirement c η) ∧
      c ≤ (resolutionTask ε).informationLimitOf
        (readingStrategy (2 * n + 1) (majorityAnswer n)) ∧
      (resolutionTask ε).expectedCostAt
        (readingStrategy (2 * n + 1) (majorityAnswer n)) (2 * n + 1) () =
          ((2 * n + 1 : ℕ) : ℝ) ∧
      (resolutionTask ε).extendedCostOf
        (readingStrategy (2 * n + 1) (majorityAnswer n)) () =
          ENNReal.ofReal (((2 * n + 1 : ℕ) : ℝ)) := by
  obtain ⟨hinfo, _, _hN⟩ := majority_target ε hε0.le hε1 hε0 η hη0 hη1
  set n := ⌈Real.log (1 / (2 * η)) / (4 * ε ^ 2)⌉₊
  have hε2 : 0 < 4 * ε ^ 2 := by positivity
  have hnle : Real.log (1 / (2 * η)) / (4 * ε ^ 2) ≤ n := Nat.le_ceil _
  have herr : 1 / 2 * (1 - 4 * ε ^ 2) ^ n ≤ η := by
    have hle : Real.log (1 / (2 * η)) ≤ 4 * n * ε ^ 2 := by
      rw [div_le_iff₀ hε2] at hnle
      linarith
    have hexp : Real.exp (-(4 * n * ε ^ 2)) ≤ 2 * η := by
      calc
        Real.exp (-(4 * n * ε ^ 2)) ≤ Real.exp (-Real.log (1 / (2 * η))) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = 2 * η := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
    have hbound := majority_error_le_exp ε hε0.le hε1 n
    linarith
  have hconfidence : (resolutionTask ε).Qualifies
      (readingStrategy (2 * n + 1) (majorityAnswer n)) (2 * n + 1)
      (confidenceRequirement c η) := by
    refine ⟨readingStrategy_admissible ε (2 * n + 1) _, ?_, ?_, ?_⟩
    · show c ≤ _
      rw [readingStrategy_information ε hε0.le hε1 (2 * n + 1)]
      exact hc.trans hinfo
    · show _ ≤ η
      rw [readingStrategy_errorMass ε hε0.le hε1 n]
      exact (majority_error_le ε hε0.le hε1 n).trans herr
    · show _ ≤ 0
      rw [readingStrategy_refusalMass ε (2 * n + 1) n]
  refine ⟨n, hconfidence, ?_, ?_, ?_⟩
  · rw [readingStrategy_informationLimit ε hε0.le hε1 (2 * n + 1)]
    exact (hc.trans hinfo).trans
      (terminalMI_le_informationLimit (majorityProtocol ε hε0.le hε1 (2 * n + 1))
        (2 * n + 1))
  · exact readingStrategy_cost ε hε0.le hε1 (2 * n + 1) (majorityAnswer n)
  · exact readingStrategy_extendedCost ε hε0.le hε1 (2 * n + 1) (majorityAnswer n)

/-- All three original extended infima are finite, using one constructed majority
strategy that meets the information, confidence and unbounded limit requirements. -/
theorem resolutionExtendedInfima_finite (c η ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hc : c ≤ 1 - Real.binEntropy η / Real.log 2) :
    resolutionMinimumCostExtended c ε ≠ ⊤ ∧
    resolutionLimitMinimumCostExtended c ε ≠ ⊤ ∧
    confidenceMinimumCostExtended c η ε ≠ ⊤ := by
  obtain ⟨n, hconfidence, hlimit, hrealcost, hextcost⟩ :=
    majorityStrategy_finite_witness c η ε hε0 hε1 hη0 hη1 hc
  let N : ℕ := 2 * n + 1
  let σ := readingStrategy N (majorityAnswer n)
  have hinformation : (resolutionTask ε).Qualifies σ N (informationRequirement c) := by
    exact ⟨hconfidence.1, hconfidence.2.1,
      hconfidence.2.2.1.trans (by show η ≤ 1; linarith [hη1]),
      hconfidence.2.2.2.trans (by show (0 : ℝ) ≤ 1; norm_num)⟩
  have hfiniteInformation : resolutionMinimumCostExtended c ε ≤ ENNReal.ofReal (N : ℝ) := by
    unfold resolutionMinimumCostExtended
    calc
      (⨅ m : ℕ, (resolutionTask ε).minimumCost m (informationRequirement c) ()) ≤
          (resolutionTask ε).minimumCost N (informationRequirement c) () := iInf_le _ N
      _ ≤ ENNReal.ofReal ((resolutionTask ε).expectedCostAt σ N ()) :=
        iInf₂_le σ hinformation
      _ = ENNReal.ofReal (N : ℝ) := by rw [hrealcost]
  have hfiniteLimit : resolutionLimitMinimumCostExtended c ε ≤ ENNReal.ofReal (N : ℝ) := by
    unfold resolutionLimitMinimumCostExtended
    exact (iInf₂_le σ ⟨hconfidence.1, hlimit⟩).trans_eq hextcost
  have hfiniteConfidence : confidenceMinimumCostExtended c η ε ≤ ENNReal.ofReal (N : ℝ) := by
    unfold confidenceMinimumCostExtended
    calc
      (⨅ m : ℕ, (resolutionTask ε).minimumCost m (confidenceRequirement c η) ()) ≤
          (resolutionTask ε).minimumCost N (confidenceRequirement c η) () := iInf_le _ N
      _ ≤ ENNReal.ofReal ((resolutionTask ε).expectedCostAt σ N ()) :=
        iInf₂_le σ hconfidence
      _ = ENNReal.ofReal (N : ℝ) := by rw [hrealcost]
  exact ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfiniteInformation,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfiniteLimit,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfiniteConfidence⟩

end SharpScaling

/-! ## M3.5: budget feasibility under a demand isomorphism -/

section BudgetTransport
open UniversalObservation.Demand UniversalObservation.Transport

def BudgetTransportGoal : Prop :=
  ∀ (I J W V : Type) (P : Problem I W) (Q : Problem J V)
    (e : DemandIso P Q) (c : W → ℕ → ℝ) (d : V → ℕ → ℝ),
    (∀ w j, d (e.witnesses w) j = c w j) →
    ∀ D b, BudgetFeasible P D c b ↔ BudgetFeasible Q (e.demands '' D) d b

/-- A cost-preserving demand isomorphism keeps the whole feasible budget set, in both directions. -/
theorem budgetTransportGoal : BudgetTransportGoal := by
  intro I J W V P Q e c d hc D b
  exact (budget_transport_iff e c d hc D b).symm

end BudgetTransport

end OperatorKO7.Meta.BoundaryObserver.ResourceFrontier
