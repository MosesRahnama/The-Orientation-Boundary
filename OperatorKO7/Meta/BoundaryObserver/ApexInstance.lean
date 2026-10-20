import OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem
import OperatorKO7.Meta.BoundaryObserver.BoundaryTheoremQuantum
import Mathlib.LinearAlgebra.Matrix.Reindex

set_option autoImplicit false

/-!
# Every pair clause on the constant Bool observer

Graph: BOUNDARY-THEOREM-PROOF-GRAPH.md, expansion E4.
The observer is the constant map on Bool, with true and false as its two states.
The finite matrix coordinates are identified explicitly with those same states.
Each clause of `BoundaryTheorem.BoundaryTheoremCoreGoal` that speaks about a pair, its
binary reading, its fiber, its rows or its messages is stated here at that one instance,
and `boolPairCoreInstanceGoal` is one conjunction with `BoundaryTheorem.ApexCoreGoal`.
The register, qubit, composite and field clauses of `BoundaryTheorem.BoundaryTheoremGoal`
join the same instance in `boolPairInstanceGoal`, one conjunction with
`BoundaryTheorem.ApexPairGoal`.

The five clauses about the Gödel pair, the diagonal tower and the recursor passes
(`GodelPoleGoal`, `GodelSideSymbolGoal`, `DiagonalWalkGoal`, `DiagonalUnionGoal`,
`RecursionClauseGoal`) concern other merged pairs and stay with their own instances;
`SparseControlGoal` concerns fibers of unbounded size and is not a pair clause.

PREMISE_ORIGIN_AUDIT
The merged-pair premise of every specialized clause is DERIVED_FROM_CERTIFIED_STRUCTURE
through `BoundaryTheorem.apexCoreGoal`. The positivity of the binary discrimination is
INDEPENDENTLY_PROVED from `discrimination_binaryKernel`. The fiber premises at size two
(`2 ≤ n`, uniform prior, error bound) are discharged at the instance. Every remaining
premise of a specialized clause is ORIGINAL_FINAL_ASSUMPTION of that clause.
-/

namespace OperatorKO7.Meta.BoundaryObserver
namespace ApexInstance

open scoped BigOperators Kronecker ComplexOrder
open ProtocolResolution BoundarySingularity PairResolution MergedPair
open BoundaryPole PairQubit FiberResolution PairField PairBell BoundaryPrivacy BoundarySecrecy

noncomputable section

/-!
## Unit 1: the record, kinematic and place-orbit clauses
-/

/-- Both states have the same unit-valued record. -/
def record : Bool → Unit := fun _ => ()

/-- The two labels name the actual Bool states without a further encoding. -/
theorem pairState_eq (b : Bool) : BoundaryPole.pairState true false b = b := by
  cases b <;> rfl

/-- The accepted classical apex theorem supplies the merged-pair witness for this observer. -/
theorem mergedPair : IsMergedPair record true false :=
  BoundaryTheorem.apexCoreGoal.1

/-- The two finite matrix indices label the same Bool states. -/
def pairIndex : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := decide (i = 1)
  left_inv := by decide
  right_inv := by decide

/-- The matrix-coordinate observer is the original observer transported along pairIndex. -/
def indexedRecord : Fin 2 → Unit := record ∘ pairIndex.symm

/-- The finite matrix coordinates retain exactly the original record. -/
theorem indexedRecord_eq (b : Bool) : indexedRecord (pairIndex b) = record b := rfl

/-- Relabeling both matrix indices gives the full algebra equivalence of the two presentations. -/
def pairMatrixEquiv : Matrix Bool Bool ℂ ≃ₐ[ℂ] BoundaryReconstruction.Mat 2 :=
  Matrix.reindexAlgEquiv ℂ ℂ pairIndex

/-- The record, protocol, kinematic and place-orbit clauses refer to this single observer. -/
def RecordKinematicPairGoal : Prop :=
  IsMergedPair record true false ∧
    (∀ (Y : Type) [Fintype Y] (K : Reading Bool Y),
      RecordDetermined record K → readingDiscrimination K true false = 0) ∧
    (IsMergedPair record true false ↔
      (true ≠ false ∧ ∀ (Y : Type) [Fintype Y] (K : Reading Bool Y),
        RecordDetermined record K → readingDiscrimination K true false = 0)) ∧
    (∀ (A Y : Type) [Fintype A] [Fintype Y]
      (p : FiniteProtocol Bool A Y) (K : List (A × Y) → A → Reading Bool Y),
      (∀ h a, RecordDetermined record (K h a)) →
      (∀ h a b, p.observation h a b = K h a (BoundaryPole.pairState true false b)) →
        (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧ informationLimit p = 0) ∧
    ((∀ f : Bool → Bool, Determines record f → f true = f false) ∧
      (∀ f : Bool → Bool, f true ≠ f false →
        (f true = decide (true = true) ∧ f false = decide (false = true)) ∨
          (f true = decide (true = false) ∧ f false = decide (false = false))) ∧
      (∀ (S : Type) (s : Bool → S),
        Set.InjOn (fun x => (record x, s x)) ({true, false} : Set Bool) ↔
          s true ≠ s false) ∧
      ¬ ∃ d : Unit → Unit → Bool,
        ∀ a ∈ ({true, false} : Set Bool), ∀ b ∈ ({true, false} : Set Bool),
          d (record a) (record b) = decide (a = b)) ∧
    (∀ (n : ℕ) (p p' : Bool → Fin n),
      p ∈ PlaceCoordinates.PlaceCoord record n → p' ∈ PlaceCoordinates.PlaceCoord record n →
        (∃ σ ∈ OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer.licenseStabilizer
            record, p' = p ∘ σ.symm) ∧
        ∀ τ ∈ OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer.licenseStabilizer
            record, p ∘ τ.symm = p → τ = 1)

/-- The accepted clauses instantiate to the same Bool observer and the same ordered pair. -/
theorem recordKinematicPairGoal : RecordKinematicPairGoal := by
  refine ⟨mergedPair, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y _ K hK
    exact BoundaryPole.recordPoleGoal Bool Unit Y record K true false hK mergedPair
  · exact BoundaryPole.boundaryZeroSetGoal Bool Unit record true false
  · intro A Y _ _ p K hK hsource
    exact BoundaryPole.recordProtocolPoleGoal Bool Unit A Y record true false p K
      mergedPair hK hsource
  · obtain ⟨h1, h2, -, h4, h5⟩ :=
      BoundaryTheorem.kinematicClause Bool Unit record true false mergedPair
    exact ⟨h1, h2, h4, h5⟩
  · intro n p p' hp hp'
    exact BoundaryTheorem.placeOrbitClause Bool Unit record n p p' hp hp'

/-!
## Unit 2: the pole of order one at the binary reading of the pair

The binary symmetric reading assigns to the state b the law of signed bias ε.
Its discrimination at the pair is 8 ε², positive for every positive bias, so the
order-one and residue clauses hold on this reading with the number 8 ε² in place
of the discrimination.
-/

/-- The binary symmetric reading of the two states at bias ε. -/
def binaryRow (ε : ℝ) (hε : |ε| ≤ 1 / 2) : Reading Bool Bool :=
  fun b => binaryKernelLaw ε hε b

theorem binaryRow_discrimination (ε : ℝ) (hε : |ε| ≤ 1 / 2) :
    readingDiscrimination (binaryRow ε hε) true false = 8 * ε ^ 2 :=
  discrimination_binaryKernel ε

/-- The order-one and residue clauses at the binary reading of the pair. -/
def BinaryPoleGoal : Prop :=
  ∀ (ε : ℝ) (hε : |ε| ≤ 1 / 2), 0 < ε →
    readingDiscrimination (binaryRow ε hε) true false = 8 * ε ^ 2 ∧
    (∀ (A : Type) [Fintype A] (p : FiniteProtocol Bool A Bool) (c : ℝ),
      PairMenu p (8 * ε ^ 2) → ∀ n bank, HistoryBank n bank →
        c ≤ terminalMI p n bank → c * Real.log 2 ≤ 8 * ε ^ 2 * expectedCost p n bank) ∧
    (∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ N : ℕ,
      1 - Real.binEntropy η / Real.log 2 ≤
          terminalMI (repeatProtocol (binaryRow ε hε true) (binaryRow ε hε false) N) N
            (historyBank Unit Bool N) ∧
        8 * ε ^ 2 * N ≤ 4 * Real.log (1 / (2 * η)) + 8 * ε ^ 2) ∧
    (∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
      (1 - Real.binEntropy η / Real.log 2) * Real.log 2 ≤
          8 * ε ^ 2 * leastRepeatCost (binaryRow ε hε true) (binaryRow ε hε false)
            (1 - Real.binEntropy η / Real.log 2) ∧
        8 * ε ^ 2 * leastRepeatCost (binaryRow ε hε true) (binaryRow ε hε false)
            (1 - Real.binEntropy η / Real.log 2) ≤
          4 * Real.log (1 / (2 * η)) + 8 * ε ^ 2)

theorem binaryPoleGoal : BinaryPoleGoal := by
  intro ε hε hpos
  have hdisc : discrimination (binaryRow ε hε true).mass (binaryRow ε hε false).mass =
      8 * ε ^ 2 := discrimination_binaryKernel ε
  have hdpos : 0 < discrimination (binaryRow ε hε true).mass (binaryRow ε hε false).mass := by
    rw [hdisc]
    positivity
  obtain ⟨hcost, hattain⟩ :=
    BoundaryPole.poleOrderOneGoal Bool (binaryRow ε hε true) (binaryRow ε hε false) hdpos
  refine ⟨hdisc, ?_, ?_, ?_⟩
  · intro A _ p c hm n bank hb hc
    have hm' : PairMenu p
        (discrimination (binaryRow ε hε true).mass (binaryRow ε hε false).mass) := by
      rw [hdisc]
      exact hm
    have h := hcost A p c hm' n bank hb hc
    rwa [hdisc] at h
  · intro η hη hη'
    obtain ⟨N, hN1, hN2⟩ := hattain η hη hη'
    refine ⟨N, hN1, ?_⟩
    rwa [hdisc] at hN2
  · intro η hη hη'
    have h := BoundaryPole.poleResidueGoal Bool (binaryRow ε hε true) (binaryRow ε hε false)
      η hdpos hη hη'
    rwa [hdisc] at h

/-!
## Unit 3: the fiber clauses at fiber size two

The two states form one fiber of size two of the constant observer. The one-reading,
capacity, attainment and Fano clauses are stated at n = 2, where the factor n - 1 is 1
and the Fano correction term vanishes.
-/

/-- The four fiber clauses at the fiber of the pair. -/
def FiberPairGoal : Prop :=
  (∀ (Y : Type) [Fintype Y] (p : FiniteLaw (Fin 2)) (K : Fin 2 → FiniteLaw Y),
    jointMI (fun by_ : Fin 2 × Y => p.mass by_.1 * (K by_.1).mass by_.2) ≤
      (∑ b, ∑ b', if b ≠ b' then
        (p.mass b + p.mass b') * discrimination (K b).mass (K b').mass else 0) /
          (2 * Real.log 2)) ∧
  (∀ (A Y : Type) [Fintype A] [Fintype Y] (p : FiniteProtocol (Fin 2) A Y) (δ : ℝ),
    FiberMenu p δ → 0 ≤ δ → LocalCapacityBound p (δ / Real.log 2)) ∧
  (∀ (Y : Type) [Fintype Y] (p0 : FiniteLaw (Fin 2)) (K : Fin 2 → FiniteLaw Y) (β : ℝ)
    (g : List (Unit × Y) → Fin 2) (N : ℕ),
    (∀ b, p0.mass b = 1 / 2) →
    (∀ b b', b ≠ b' → bhattacharyya (K b).mass (K b').mass ≤ β) →
    (∀ h b, fiberLikelihood K b h ≤ fiberLikelihood K (g h) h) →
      fiberError p0 K N g ≤ β ^ N) ∧
  (∀ (Y : Type) [Fintype Y] (p0 : FiniteLaw (Fin 2)) (K : Fin 2 → FiniteLaw Y)
    (g : List (Unit × Y) → Fin 2) (N : ℕ),
    (∀ b, p0.mass b = 1 / 2) → fiberError p0 K N g ≤ 1 / 2 →
      1 - Real.binEntropy (fiberError p0 K N g) / Real.log 2 ≤
        terminalMI (repeatFiber p0 K N) N (historyBank Unit Y N))

theorem fiberPairGoal : FiberPairGoal := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y _ p K
    exact FiberResolution.fiberOneReading 2 Y p K
  · intro A Y _ _ p δ hm hδ
    have h := FiberResolution.fiberCapacity 2 A Y p δ hm hδ
    convert h using 1
    norm_num
  · intro Y _ p0 K β g N hp hb hg
    have hp' : ∀ b, p0.mass b = 1 / ((2 : ℕ) : ℝ) := by
      intro b
      rw [hp b]
      norm_num
    have h := FiberResolution.fiberAttainment 2 Y p0 K β g N hp' hb hg
    convert h using 1
    norm_num
  · intro Y _ p0 K g N hp he
    have hp' : ∀ b, p0.mass b = 1 / ((2 : ℕ) : ℝ) := by
      intro b
      rw [hp b]
      norm_num
    have he' : fiberError p0 K N g ≤ 1 - 1 / ((2 : ℕ) : ℝ) := by
      have h12 : (1 : ℝ) - 1 / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
      rw [h12]
      exact he
    have h := FiberResolution.fiberFano 2 Y p0 K g N hp' le_rfl he'
    have hlogb : Real.logb 2 ((2 : ℕ) : ℝ) = 1 := by
      rw [Nat.cast_ofNat]
      exact Real.logb_self_eq_one one_lt_two
    have hlog1 : Real.log (((2 : ℕ) : ℝ) - 1) = 0 := by
      norm_num
    rw [hlogb, hlog1, mul_zero, add_zero] at h
    exact h

/-!
## Unit 4: the thermal clauses on the register of the pair

The register of the pair is the Bool-indexed density matrix. The merge floor, the
reset by one swap and the cycle hold on that register.
-/

/-- The merge floor, the demon reset and the cycle on the register of the pair. -/
def ThermalPairGoal : Prop :=
  (∀ (κ : Type) [Fintype κ] [DecidableEq κ] [Nonempty κ]
      (u : Matrix.unitaryGroup (Bool × κ) ℂ) (rho : Matrix Bool Bool ℂ),
      rho.PosDef → rho.trace = 1 → ∀ (h : Matrix κ κ ℂ) (hh : h.IsHermitian) (β : ℝ),
        0 < BoundaryReconstruction.Thermal.entropy (BoundaryReconstruction.Thermal.marginalLeft
          (BoundaryReconstruction.Thermal.thermalJoint u rho hh β))) ∧
  (∀ (rho : Matrix Bool Bool ℂ), rho.trace = 1 → ∀ β : ℝ, 0 < β → ∀ η : ℝ, 0 < η →
    ∃ E : ℝ, BoundaryReconstruction.Thermal.entropy (BoundaryReconstruction.Thermal.marginalLeft
      (BoundaryReconstruction.Thermal.thermalJoint ThermalReset.swapUnitary rho
        (ThermalReset.twoLevel_hermitian E) β)) < η) ∧
  (∀ (rho : Matrix Bool Bool ℂ), rho.trace = 1 →
    ∀ β : ℝ, 0 < β → ∀ η : ℝ, 0 < η → ∃ (h : Matrix Bool Bool ℂ) (hh : h.IsHermitian),
      BoundaryReconstruction.Thermal.entropy (BoundaryReconstruction.Thermal.marginalLeft
        (BoundaryReconstruction.Thermal.thermalJoint ThermalReset.swapUnitary rho hh β)) < η) ∧
  BoundaryTheorem.CycleGoal

theorem thermalPairGoal : ThermalPairGoal := by
  refine ⟨?_, BoundaryTheorem.mergeFloor.2, ?_, BoundaryTheorem.cycleGoal⟩
  · intro κ _ _ _ u rho hpd htr h hh β
    exact BoundaryTheorem.mergeFloor.1 Bool κ u rho hpd htr h hh β
  · intro rho htr β hβ η hη
    exact BoundaryTheorem.demonResetGoal Bool rho htr β hβ η hη

/-!
## Unit 5: the qubit, Noether and quantum-record clauses of the pair

The fiber algebra, the Noether clauses and the quantum record pole are stated for the
matrix-coordinate observer `indexedRecord`, which is the original constant observer
transported along `pairIndex`.
-/

/-- The qubit clauses of the pair. -/
def QubitPairGoal : Prop :=
  PauliRelationsGoal ∧ PairSpanGoal ∧
    (∀ a : BoundaryReconstruction.Mat 2, a ∈ BoundaryReconstruction.fiberAlgebra indexedRecord) ∧
    BitConservationGoal ∧ ComplementaryBitsGoal ∧ ComplementaryLawGoal

theorem qubitPairGoal : QubitPairGoal :=
  ⟨PairQubit.pauli_relations, PairQubit.pair_span, PairQubit.pair_fiber_algebra,
    PairQubit.bitConservationGoal, PairQubit.complementaryBitsGoal,
    PairQubit.complementaryLawGoal⟩

/-- The Noether, frame and quantum-record clauses on the observer of the pair. -/
def NoetherPairGoal : Prop :=
  (∀ H : BoundaryReconstruction.Mat 2,
    BoundaryReconstruction.FiberClosed indexedRecord H ↔
      ∀ y, H * recordProjector indexedRecord y = recordProjector indexedRecord y * H) ∧
  (∀ u : Matrix.unitaryGroup (Fin 2) ℂ,
    (∀ ρ : BoundaryReconstruction.Mat 2, ρ.PosSemidef → ρ.trace = 1 → ∀ y,
      ((u : BoundaryReconstruction.Mat 2) * ρ * star (u : BoundaryReconstruction.Mat 2) *
          recordProjector indexedRecord y).trace = (ρ * recordProjector indexedRecord y).trace) ↔
      BoundaryReconstruction.FiberClosed indexedRecord (u : BoundaryReconstruction.Mat 2)) ∧
  (∀ s : Equiv.Perm (Fin 2),
    BoundaryReconstruction.FiberClosed indexedRecord (BoundaryReconstruction.permutationMat s) ↔
      ∀ i, indexedRecord (s i) = indexedRecord i) ∧
  (∀ u v : Matrix.unitaryGroup (Fin 2) ℂ,
    BoundaryReconstruction.FiberClosed indexedRecord (u : BoundaryReconstruction.Mat 2) →
    BoundaryReconstruction.FiberClosed indexedRecord (v : BoundaryReconstruction.Mat 2) →
      ∃ w : Matrix.unitaryGroup (Fin 2) ℂ,
        BoundaryReconstruction.FiberClosed indexedRecord (w : BoundaryReconstruction.Mat 2) ∧
          v = w * u ∧ ∀ w' : Matrix.unitaryGroup (Fin 2) ℂ, v = w' * u → w' = w) ∧
  (∀ (Y : Type) (E : Y → BoundaryReconstruction.Mat 2) (c : Y → Unit → ℂ)
    (ρ₀ ρ₁ : BoundaryReconstruction.Mat 2),
    (∀ y, E y = ∑ r ∈ Finset.univ.image indexedRecord, c y r • recordProjector indexedRecord r) →
    (∀ r, (ρ₀ * recordProjector indexedRecord r).trace =
      (ρ₁ * recordProjector indexedRecord r).trace) →
      ∀ y, (ρ₀ * E y).trace = (ρ₁ * E y).trace)

theorem noetherPairGoal : NoetherPairGoal := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact PairQubit.generatorNoetherGoal 2 Unit indexedRecord
  · exact PairQubit.unitaryNoetherGoal 2 Unit indexedRecord
  · exact PairQubit.invisiblePermutationGoal 2 Unit indexedRecord
  · exact PairQubit.frameOrbitGoal 2 Unit indexedRecord
  · intro Y
    exact PairQubit.quantumRecordPoleGoal 2 Unit Y indexedRecord

/-!
## Unit 6: the secrecy clauses with the two states as messages
-/

/-- Perfect secrecy, the one-time pad and the key bound with the two states as messages. -/
def SecrecyPairGoal : Prop :=
  (∀ (K C : Type) [Fintype K] [Fintype C] [DecidableEq C] (key : FiniteLaw K)
    (enc : K → Bool → C),
    (∀ c, cipherLaw key enc true c = cipherLaw key enc false c) →
      discrimination (cipherLaw key enc true) (cipherLaw key enc false) = 0) ∧
  OneTimePadGoal ∧
  (∀ (K C : Type) [Fintype K] [Fintype C] [DecidableEq C] (key : FiniteLaw K)
    (enc : K → Bool → C) (dec : K → C → Bool),
    (∀ k m, dec k (enc k m) = m) → (∀ m m' c, cipherLaw key enc m c = cipherLaw key enc m' c) →
      2 ≤ (Finset.univ.filter (fun k => 0 < key.mass k)).card)

theorem secrecyPairGoal : SecrecyPairGoal := by
  refine ⟨?_, BoundarySecrecy.oneTimePadGoal, ?_⟩
  · intro K C _ _ _ key enc h
    exact BoundarySecrecy.perfectSecrecyPoleGoal K Bool C key enc true false h
  · intro K C _ _ _ key enc dec hdec hsec
    have h := BoundarySecrecy.shannonKeyGoal K Bool C key enc dec hdec hsec
    rwa [Fintype.card_bool] at h

/-!
## Unit 7: one conjunction on the pair
-/

/-- E4, core form: every pair clause of the core Boundary Theorem on the constant Bool
observer and its two states, as one conjunction with the classical apex pair statement. -/
def BoolPairCoreInstanceGoal : Prop :=
  RecordKinematicPairGoal ∧ BinaryPoleGoal ∧ FiberPairGoal ∧ TwoPointGoal ∧
    PrivacyDiscriminationGoal ∧ PrivacyCostGoal ∧ SecrecyPairGoal ∧
    BoundaryTheorem.ApexCoreGoal

theorem boolPairCoreInstanceGoal : BoolPairCoreInstanceGoal :=
  ⟨recordKinematicPairGoal, binaryPoleGoal, fiberPairGoal, BoundaryPole.twoPointGoal,
    BoundaryPrivacy.privacyDiscriminationGoal, BoundaryPrivacy.privacyCostGoal,
    secrecyPairGoal, BoundaryTheorem.apexCoreGoal⟩

/-- E4: every pair clause of the Boundary Theorem on the constant Bool observer and its two
states, as one conjunction with the five-object apex pair statement. -/
def BoolPairInstanceGoal : Prop :=
  RecordKinematicPairGoal ∧ BinaryPoleGoal ∧ FiberPairGoal ∧ ThermalPairGoal ∧
    QubitPairGoal ∧ NoetherPairGoal ∧ FieldSelectionGoal ∧ BellTableGoal ∧ PureExcessGoal ∧
    MeasuredRowsGoal ∧ TwoPointGoal ∧ PrivacyDiscriminationGoal ∧ PrivacyCostGoal ∧
    SecrecyPairGoal ∧ BoundaryTheorem.ApexPairGoal

theorem boolPairInstanceGoal : BoolPairInstanceGoal :=
  ⟨recordKinematicPairGoal, binaryPoleGoal, fiberPairGoal, thermalPairGoal, qubitPairGoal,
    noetherPairGoal, PairField.fieldSelectionGoal, PairBell.bellTable, PairBell.pureExcess,
    PairQubit.measuredRowsGoal, BoundaryPole.twoPointGoal,
    BoundaryPrivacy.privacyDiscriminationGoal, BoundaryPrivacy.privacyCostGoal,
    secrecyPairGoal, BoundaryTheorem.apexPairGoal⟩

end

end ApexInstance
end OperatorKO7.Meta.BoundaryObserver
