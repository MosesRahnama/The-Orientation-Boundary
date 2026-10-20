import OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem
import OperatorKO7.Meta.BoundaryObserver.BoundarySingularityQuantum
import OperatorKO7.Meta.BoundaryObserver.ThermalReset
import OperatorKO7.Meta.BoundaryObserver.PairBell
import OperatorKO7.Meta.BoundaryObserver.PairField
import OperatorKO7.Meta.BoundaryObserver.PairQubit
import OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleBoundaryClauses

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem

universe u

open scoped BigOperators Kronecker ComplexOrder
open OperatorKO7.Meta.BoundaryObserver
open ProtocolResolution MergedPair

noncomputable section

def MergeFloorGoal : Prop :=
  (∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
      [Nontrivial ι] (u : Matrix.unitaryGroup (ι × κ) ℂ) (rho : Matrix ι ι ℂ),
      rho.PosDef → rho.trace = 1 → ∀ (h : Matrix κ κ ℂ) (hh : h.IsHermitian) (β : ℝ),
        0 < BoundaryReconstruction.Thermal.entropy (BoundaryReconstruction.Thermal.marginalLeft
          (BoundaryReconstruction.Thermal.thermalJoint u rho hh β))) ∧
  ∀ (rho : Matrix Bool Bool ℂ), rho.trace = 1 → ∀ β : ℝ, 0 < β → ∀ η : ℝ, 0 < η →
    ∃ E : ℝ, BoundaryReconstruction.Thermal.entropy (BoundaryReconstruction.Thermal.marginalLeft
      (BoundaryReconstruction.Thermal.thermalJoint ThermalReset.swapUnitary rho
        (ThermalReset.twoLevel_hermitian E) β)) < η

theorem mergeFloor : MergeFloorGoal := by
  constructor
  · intro ι κ _ _ _ _ _ _ u rho hrho htr h hh β
    exact BoundarySingularity.Thermal.no_exact_thermal_erasure u hrho htr hh β
  · intro rho htr β hβ η hη
    exact ThermalReset.approximate_reset htr β hβ η hη


/-- M6.7(ii): the register of any finite dimension is reset below any positive entropy by one swap
with a bath of its own dimension. -/
def DemonResetGoal : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (rho : Matrix ι ι ℂ), rho.trace = 1 →
    ∀ β : ℝ, 0 < β → ∀ η : ℝ, 0 < η → ∃ (h : Matrix ι ι ℂ) (hh : h.IsHermitian),
      BoundaryReconstruction.Thermal.entropy (BoundaryReconstruction.Thermal.marginalLeft
        (BoundaryReconstruction.Thermal.thermalJoint ThermalReset.swapUnitary rho hh β)) < η

open Filter Topology BoundaryReconstruction.Thermal in
/-- G21. One ground level at energy zero and every other level at gap E: as E grows the Gibbs
state of the bath tends to the ground point mass, and one swap hands that state to the register. -/
theorem demonResetGoal : DemonResetGoal := by
  intro ι _ _ _ rho htr β hβ η hη
  classical
  let i0 : ι := Classical.arbitrary ι
  let e : ℝ → ι → ℝ := fun E i => if i = i0 then 0 else E
  have hexp : Tendsto (fun E : ℝ => Real.exp (-β * E)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hβ))
  have hterm : ∀ j : ι,
      Tendsto (fun E => Real.exp (-β * e E j)) atTop (𝓝 (if j = i0 then 1 else 0)) := by
    intro j
    by_cases hj : j = i0
    · simp only [e, hj, if_true, mul_zero, Real.exp_zero]
      exact tendsto_const_nhds
    · simp only [e, hj, if_false]
      exact hexp
  have hZ : Tendsto (fun E => partition β (e E)) atTop (𝓝 1) := by
    have h := tendsto_finset_sum Finset.univ (fun j _ => hterm j)
    simpa [partition, Finset.sum_ite_eq'] using h
  have hw : ∀ i : ι,
      Tendsto (fun E => gibbsWeight β (e E) i) atTop (𝓝 (if i = i0 then 1 else 0)) := by
    intro i
    have h := (hterm i).div hZ one_ne_zero
    simpa [gibbsWeight] using h
  have hn : ∀ i : ι,
      Tendsto (fun E => Real.negMulLog (gibbsWeight β (e E) i)) atTop (𝓝 0) := by
    intro i
    have h := (Real.continuous_negMulLog.tendsto _).comp (hw i)
    by_cases hi : i = i0
    · simpa [hi, Function.comp_def] using h
    · simpa [hi, Function.comp_def] using h
  have hT : Tendsto (fun E => ∑ i, Real.negMulLog (gibbsWeight β (e E) i)) atTop (𝓝 0) := by
    have h := tendsto_finset_sum Finset.univ (fun i _ => hn i)
    simpa using h
  obtain ⟨E, hE⟩ := ((tendsto_order.1 hT).2 η hη).exists
  refine ⟨spectralLift 1 (e E), spectralLift_hermitian 1 (e E), ?_⟩
  rw [ThermalReset.swap_output rho htr, gibbsState_spectralLift, entropy_spectralLift]
  exact hE

/-- The transcript register of a protocol at horizon n: the diagonal matrix of its transcript law. -/
def transcriptRegister {A Y : Type} [Fintype A] [Fintype Y] [DecidableEq A] [DecidableEq Y]
    (p : FiniteProtocol Bool A Y) (n : ℕ) :
    Matrix (↥(historySet (A × Y) n)) (↥(historySet (A × Y) n)) ℂ :=
  BoundaryReconstruction.Thermal.realDiagonal (fun h => ∑ z, stoppedMass p n z h.val)

open BoundarySingularity in
/-- M6.7(i): the bit a protocol moves across the boundary is paid in both currencies. Its readings
cost at least `I log 2 / δ`, and every finite thermal reset of its transcript register pays heat
and residual entropy that add, in nats, to at least `I log 2`. -/
def CycleGoal : Prop :=
  ∀ (A Y : Type) [Fintype A] [Fintype Y] [DecidableEq A] [DecidableEq Y]
    (p : FiniteProtocol Bool A Y) (δ : ℝ), PairMenu p δ → 0 < δ → ∀ n : ℕ,
    terminalMI p n (historyBank A Y n) * Real.log 2 ≤ δ * expectedCost p n (historyBank A Y n) ∧
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [Nonempty κ]
      (u : Matrix.unitaryGroup ((↥(historySet (A × Y) n)) × κ) ℂ) (h : Matrix κ κ ℂ)
      (hh : h.IsHermitian) (β : ℝ), 0 < β →
        terminalMI p n (historyBank A Y n) * Real.log 2 ≤
          β * BoundaryReconstruction.Thermal.reservoirHeat u (transcriptRegister p n) hh β +
            BoundaryReconstruction.Thermal.entropy (BoundaryReconstruction.Thermal.marginalLeft
              (BoundaryReconstruction.Thermal.thermalJoint u (transcriptRegister p n) hh β))

/-- `-x log x` of a finite nonnegative sum is at most the sum of the terms. -/
private theorem negMulLog_sum_le {H : Type} (s : Finset H) (m : H → ℝ) (hm : ∀ h, 0 ≤ m h) :
    Real.negMulLog (∑ h ∈ s, m h) ≤ ∑ h ∈ s, Real.negMulLog (m h) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (BitDivision.negMulLog_add_le (hm a) (Finset.sum_nonneg fun h _ => hm h)).trans
      (by linarith)

open BoundarySingularity BoundaryReconstruction.Thermal in
/-- G20. The bit moved across the boundary is paid in readings, and the reset of the same
transcript register pays heat and residual entropy that add, in nats, to at least I log 2. -/
theorem cycleGoal : CycleGoal := by
  intro A Y _ _ _ _ p δ menu hδ n
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hb := historyBank_complete A Y n
  refine ⟨?_, ?_⟩
  · have h := (pairMenu_information_bound p δ menu hδ.le n (historyBank A Y n) hb).2
    have h2 : terminalMI p n (historyBank A Y n) * Real.log 2 ≤
        δ / Real.log 2 * expectedCost p n (historyBank A Y n) * Real.log 2 :=
      mul_le_mul_of_nonneg_right h hlog.le
    calc terminalMI p n (historyBank A Y n) * Real.log 2 ≤
        δ / Real.log 2 * expectedCost p n (historyBank A Y n) * Real.log 2 := h2
      _ = δ * expectedCost p n (historyBank A Y n) := by
        field_simp
  · intro κ _ _ _ u h hh β hβ
    -- the transcript law of the register
    let w : ↥(historySet (A × Y) n) → ℝ := fun hs => ∑ z, stoppedMass p n z hs.val
    have hw0 : ∀ hs, 0 ≤ w hs := fun hs =>
      Finset.sum_nonneg (fun z _ => stoppedMass_nonnegative p n z hs.val)
    have hw1 : ∑ hs, w hs = 1 := by
      change (∑ hs : ↥(historySet (A × Y) n), ∑ z, stoppedMass p n z hs.val) = 1
      rw [finset_subtype_sum (historySet (A × Y) n) (fun h => ∑ z, stoppedMass p n z h),
        Finset.sum_comm]
      simp only [historySet_stoppedMass_target_marginal]
      exact p.prior.total
    have hreg : transcriptRegister p n = spectralLift 1 w := by
      simp [transcriptRegister, spectralLift, rotate, w]
    have hpsd : (transcriptRegister p n).PosSemidef := by
      unfold transcriptRegister realDiagonal
      exact Matrix.PosSemidef.diagonal (fun hs => Complex.zero_le_real.mpr (hw0 hs))
    have htr : (transcriptRegister p n).trace = 1 := by
      unfold transcriptRegister realDiagonal
      rw [Matrix.trace_diagonal, ← Complex.ofReal_sum]
      change ((∑ hs, w hs : ℝ) : ℂ) = 1
      rw [hw1, Complex.ofReal_one]
    have hent : entropy (transcriptRegister p n) =
        ∑ h ∈ historySet (A × Y) n, Real.negMulLog (∑ z, stoppedMass p n z h) := by
      rw [hreg, entropy_spectralLift]
      exact finset_subtype_sum (historySet (A × Y) n)
        (fun h => Real.negMulLog (∑ z, stoppedMass p n z h))
    -- information is at most the transcript entropy
    have hI : terminalMI p n (historyBank A Y n) * Real.log 2 ≤
        ∑ h ∈ historySet (A × Y) n, Real.negMulLog (∑ z, stoppedMass p n z h) := by
      have hprior : entropy p.prior.mass ≤
          ∑ z, (historySet (A × Y) n).sum (fun h => entropyTerm (stoppedMass p n z h)) := by
        rw [ProtocolResolution.entropy_eq_sum]
        apply Finset.sum_le_sum
        intro z _
        rw [← historySet_stoppedMass_target_marginal p n z]
        unfold entropyTerm
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right
          (negMulLog_sum_le _ _ (fun h => stoppedMass_nonnegative p n z h)) hlog.le
      have hmi : terminalMI p n (historyBank A Y n) ≤
          ∑ h ∈ historySet (A × Y) n, entropyTerm (∑ z, stoppedMass p n z h) := by
        unfold terminalMI
        simp only [hb.sum_eq]
        linarith
      have hconv : (∑ h ∈ historySet (A × Y) n, entropyTerm (∑ z, stoppedMass p n z h)) *
          Real.log 2 =
          ∑ h ∈ historySet (A × Y) n, Real.negMulLog (∑ z, stoppedMass p n z h) := by
        unfold entropyTerm
        rw [← Finset.sum_div, div_mul_cancel₀ _ (ne_of_gt hlog)]
      rw [← hconv]
      exact mul_le_mul_of_nonneg_right hmi hlog.le
    -- Landauer for the same register, unitary and bath
    have hland := landauer_from_unitary u hpsd htr hh β hβ
    rw [div_le_iff₀ hβ] at hland
    rw [hent] at hland
    linarith

open BoundarySingularity PairQubit in
/-- M6.16(i): the smallest instance binds every clause to one pair: the two copies of one object,
the constant observer on `Bool`. -/
def ApexPairGoal : Prop :=
  IsMergedPair (fun _ : Bool => ()) true false ∧
    (∀ ε : ℝ, discrimination (binaryKernel ε true) (binaryKernel ε false) = 8 * ε ^ 2) ∧
    BoundaryReconstruction.Thermal.entropy BoundarySingularity.Thermal.fairPair = Real.log 2 ∧
    pairX = (fun i j : Bool => if Equiv.swap true false j = i then (1 : ℂ) else 0) ∧
    BoundaryReconstruction.Thermal.marginalLeft bellState = BoundarySingularity.Thermal.fairPair

open BoundarySingularity PairQubit in
/-- G51. The constant observer on the two labels: a merged pair, the binary discrimination
8 ε², the fair-pair entropy log 2, the transposition as the swap matrix and the Bell marginal. -/
theorem apexPairGoal : ApexPairGoal := by
  refine ⟨⟨by decide, rfl⟩, discrimination_binaryKernel,
    BoundarySingularity.Thermal.fairPair_entropy, ?_, PairQubit.quantum_purification.1⟩
  ext i j
  cases i <;> cases j <;> simp [pairX]

open PairBell PairQubit in
/-- Clause (16) of Theorem `thm:boundary-quantum`, the Bell table: in the state `Φ` at angle
`π / 4` the four correlations are those of the extreme table, `-1 / √2` at the pair of second
tests and `1 / √2` at the other three settings, and the score is `2 √2`. -/
def BellTableClauseGoal : Prop :=
  BellTableGoal ∧
    (∀ x y : Bool, stateCorrelation bellState (Real.pi / 4) x y =
      if x && y then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2) ∧
    chshScore bellState (Real.pi / 4) = 2 * Real.sqrt 2

/-- The Bell table clause holds by `bellTable`, `bell_table_correlations` and
`bell_table_score`. -/
theorem bellTableClause : BellTableClauseGoal :=
  ⟨PairBell.bellTable, ObservationPrincipleBoundaryClauses.bell_table_correlations,
    ObservationPrincipleBoundaryClauses.bell_table_score⟩

open BoundaryPole FiberResolution PairQubit PairField PairBell BoundaryPrivacy
  BoundarySecrecy in
/-- M6.16(ii): the Boundary Theorem, every clause on one statement. -/
def BoundaryTheoremGoal : Prop :=
  RecordPoleGoal ∧ BoundaryZeroSetGoal ∧ RecordProtocolPoleGoal ∧ KinematicClauseGoal ∧
    PlaceOrbitClauseGoal ∧ PoleOrderOneGoal ∧ PoleResidueGoal ∧ GodelPoleGoal ∧
    GodelSideSymbolGoal ∧ DiagonalWalkGoal ∧ DiagonalUnionGoal ∧ CountedRecursionClauseGoal.{u} ∧
    FiberOneReadingGoal ∧ FiberCapacityClauseGoal ∧ FiberAttainmentGoal ∧ FiberFanoGoal ∧
    SparseControlGoal ∧ MergeFloorGoal ∧ CycleGoal ∧ DemonResetGoal ∧ PauliRelationsGoal ∧
    PairSpanGoal ∧ PairFiberAlgebraGoal ∧ BitConservationGoal ∧ ComplementaryBitsGoal ∧
    ComplementaryLawGoal ∧ GeneratorNoetherGoal ∧ UnitaryNoetherGoal ∧
    InvisiblePermutationGoal ∧ FrameOrbitGoal ∧ FieldSelectionGoal ∧ BellTableClauseGoal ∧
    PureExcessGoal ∧ MeasuredRowsGoal ∧ QuantumRecordPoleGoal ∧ TwoPointGoal ∧
    PrivacyDiscriminationGoal ∧ PrivacyCostGoal ∧ PerfectSecrecyPoleGoal ∧ OneTimePadGoal ∧
    ShannonKeyGoal ∧ ApexPairGoal

/-- G52. The Boundary Theorem: every clause, each with its accepted proof, on one statement. -/
theorem boundaryTheoremGoal : BoundaryTheoremGoal.{u} :=
  ⟨BoundaryPole.recordPoleGoal, BoundaryPole.boundaryZeroSetGoal,
    BoundaryPole.recordProtocolPoleGoal, kinematicClause, placeOrbitClause,
    BoundaryPole.poleOrderOneGoal, BoundaryPole.poleResidueGoal, BoundaryPole.godelPoleGoal,
    BoundaryPole.godelSideSymbolGoal, BoundaryPole.diagonalWalkGoal,
    BoundaryPole.diagonalUnionGoal, countedRecursionClause.{u},
    FiberResolution.fiberOneReading, fiberCapacityClause,
    FiberResolution.fiberAttainment, FiberResolution.fiberFano, FiberResolution.sparseControl,
    mergeFloor, cycleGoal, demonResetGoal, PairQubit.pauli_relations, PairQubit.pair_span,
    PairQubit.pair_fiber_algebra, PairQubit.bitConservationGoal,
    PairQubit.complementaryBitsGoal, PairQubit.complementaryLawGoal,
    PairQubit.generatorNoetherGoal, PairQubit.unitaryNoetherGoal,
    PairQubit.invisiblePermutationGoal, PairQubit.frameOrbitGoal, PairField.fieldSelectionGoal,
    bellTableClause, PairBell.pureExcess, PairQubit.measuredRowsGoal,
    PairQubit.quantumRecordPoleGoal, BoundaryPole.twoPointGoal,
    BoundaryPrivacy.privacyDiscriminationGoal, BoundaryPrivacy.privacyCostGoal,
    BoundarySecrecy.perfectSecrecyPoleGoal, BoundarySecrecy.oneTimePadGoal,
    BoundarySecrecy.shannonKeyGoal, apexPairGoal⟩


end

end OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem
