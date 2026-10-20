import OperatorKO7.Meta.BoundaryObserver.PairBell
import OperatorKO7.Meta.BoundaryObserver.FiberResolution
import OperatorKO7.Meta.BoundaryObserver.PairQubit
import OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy
import OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem
import OperatorKO7.Meta.BoundaryObserver.BoundaryTheoremQuantum
import OperatorKO7.Meta.BoundaryObserver.BoundaryPole
import OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy
import OperatorKO7.Meta.BoundaryObserver.PairField

set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

/-!
# Boundary Theorem reach
M6.0, M6.15 and the first three independent M6.10 proofs.
Sources: BoundaryPole.lean, BoundarySecrecy.lean and PairField.lean.
Targets: the unchanged Goal propositions from BoundaryTheoremSpec.lean.
-/

#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.Reading
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.Reading
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.RecordDetermined
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.RecordDetermined
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.readingDiscrimination
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.readingDiscrimination
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.pairState
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.pairState
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.RecordPoleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.RecordPoleGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.BoundaryZeroSetGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.BoundaryZeroSetGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.RecordProtocolPoleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.RecordProtocolPoleGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.recordPoleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.recordPoleGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.boundaryZeroSetGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.boundaryZeroSetGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.recordProtocolPoleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.recordProtocolPoleGoal

#print OperatorKO7.Meta.BoundaryObserver.BoundaryPole.RecordPoleGoal
#print OperatorKO7.Meta.BoundaryObserver.BoundaryPole.BoundaryZeroSetGoal
#print OperatorKO7.Meta.BoundaryObserver.BoundaryPole.RecordProtocolPoleGoal

open OperatorKO7.Meta.BoundaryObserver
open BoundaryPole ProtocolResolution MergedPair

example :
    ∀ (X Q Y : Type) [Fintype Y] (q : X → Q) (K : Reading X Y) (x₀ x₁ : X),
      RecordDetermined q K → IsMergedPair q x₀ x₁ → readingDiscrimination K x₀ x₁ = 0 :=
  recordPoleGoal

example :
    ∀ (X Q : Type) (q : X → Q) (x₀ x₁ : X),
      IsMergedPair q x₀ x₁ ↔
        (x₀ ≠ x₁ ∧ ∀ (Y : Type) [Fintype Y] (K : Reading X Y),
          RecordDetermined q K → readingDiscrimination K x₀ x₁ = 0) :=
  boundaryZeroSetGoal

/-- Control at a record type with no `Fintype` instance: the identity observer on `ℕ` splits the
states `0` and `1`, so some record-determined finite reading has nonzero discrimination there. -/
example : ¬ ∀ (Y : Type) [Fintype Y] (K : Reading ℕ Y),
    RecordDetermined (id : ℕ → ℕ) K → readingDiscrimination K 0 1 = 0 := by
  intro h
  exact Nat.zero_ne_one ((boundaryZeroSetGoal ℕ ℕ id 0 1).mpr ⟨by decide, h⟩).2

example :
    ∀ (X Q A Y : Type) [Fintype A] [Fintype Y] (q : X → Q) (x₀ x₁ : X)
      (p : FiniteProtocol Bool A Y) (K : List (A × Y) → A → Reading X Y),
      IsMergedPair q x₀ x₁ → (∀ h a, RecordDetermined q (K h a)) →
      (∀ h a b, p.observation h a b = K h a (pairState x₀ x₁ b)) →
        (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧ informationLimit p = 0 :=
  recordProtocolPoleGoal

/-! ## M6.15: exact secrecy declarations and a nonempty cipher witness -/

#check @OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.cipherLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.cipherLaw
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.PerfectSecrecyPoleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.PerfectSecrecyPoleGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.OneTimePadGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.OneTimePadGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.ShannonKeyGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.ShannonKeyGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.perfectSecrecyPoleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.perfectSecrecyPoleGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.oneTimePadGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.oneTimePadGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.shannonKeyGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.shannonKeyGoal

#print OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.PerfectSecrecyPoleGoal
#print OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.OneTimePadGoal
#print OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy.ShannonKeyGoal

open BoundarySecrecy

example :
    ∀ (K M C : Type) [Fintype K] [Fintype C] [DecidableEq C] (key : FiniteLaw K)
      (enc : K → M → C) (m₀ m₁ : M),
      (∀ c, cipherLaw key enc m₀ c = cipherLaw key enc m₁ c) →
        BoundarySingularity.discrimination (cipherLaw key enc m₀) (cipherLaw key enc m₁) = 0 :=
  perfectSecrecyPoleGoal

example :
    ∀ key : FiniteLaw Bool, (∀ k, key.mass k = 1 / 2) → ∀ m c : Bool,
      cipherLaw key (fun k m => xor k m) m c = 1 / 2 :=
  oneTimePadGoal

example :
    ∀ (K M C : Type) [Fintype K] [Fintype M] [Fintype C] [DecidableEq C] (key : FiniteLaw K)
      (enc : K → M → C) (dec : K → C → M),
      (∀ k m, dec k (enc k m) = m) → (∀ m m' c, cipherLaw key enc m c = cipherLaw key enc m' c) →
        Fintype.card M ≤ (Finset.univ.filter (fun k => 0 < key.mass k)).card :=
  shannonKeyGoal

example : ∃ key : FiniteLaw Bool,
    (∀ k, key.mass k = 1 / 2) ∧
    (∀ k m : Bool, xor k (xor k m) = m) ∧
    (∀ m m' c : Bool,
      cipherLaw key (fun k m => xor k m) m c = cipherLaw key (fun k m => xor k m) m' c) := by
  let key : FiniteLaw Bool :=
    { mass := fun _ => 1 / 2
      nonnegative := by intro k; norm_num
      total := by norm_num }
  have hfair : ∀ k, key.mass k = 1 / 2 := fun _ => rfl
  refine ⟨key, hfair, ?_, ?_⟩
  · intro k m
    cases k <;> cases m <;> rfl
  · intro m m' c
    exact (oneTimePadGoal key hfair m c).trans (oneTimePadGoal key hfair m' c).symm

/-! ## M6.10: real interference, complex phase, classical purification -/

#check @OperatorKO7.Meta.BoundaryObserver.PairField.RealInterferenceGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairField.RealInterferenceGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairField.ComplexNeedsSecondReportGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairField.ComplexNeedsSecondReportGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairField.ClassicalPurificationFailsGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairField.ClassicalPurificationFailsGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairField.realInterferenceGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairField.realInterferenceGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairField.complexNeedsSecondReportGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairField.complexNeedsSecondReportGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairField.classicalPurificationFailsGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairField.classicalPurificationFailsGoal

#print OperatorKO7.Meta.BoundaryObserver.PairField.RealInterferenceGoal
#print OperatorKO7.Meta.BoundaryObserver.PairField.ComplexNeedsSecondReportGoal
#print OperatorKO7.Meta.BoundaryObserver.PairField.ClassicalPurificationFailsGoal

open scoped BigOperators

example :
    ∀ A B : Matrix (Fin 2) (Fin 2) ℂ,
      QuantumReconstruction.Hermitian A → QuantumReconstruction.Hermitian B →
      (∀ i j, (A i j).im = 0) → (∀ i j, (B i j).im = 0) →
      (∀ i, QuantumReconstruction.population A i = QuantumReconstruction.population B i) →
      QuantumReconstruction.plusReport A 0 1 = QuantumReconstruction.plusReport B 0 1 → A = B :=
  PairField.realInterferenceGoal

example :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ,
      QuantumReconstruction.Hermitian A ∧ QuantumReconstruction.Hermitian B ∧
      (∀ i, QuantumReconstruction.population A i = QuantumReconstruction.population B i) ∧
      QuantumReconstruction.plusReport A 0 1 = QuantumReconstruction.plusReport B 0 1 ∧
      QuantumReconstruction.phaseReport A 0 1 ≠ QuantumReconstruction.phaseReport B 0 1 :=
  PairField.complexNeedsSecondReportGoal

example :
    ¬ ∃ (Y : Type) (_ : Fintype Y) (m : Bool × Y → ℝ),
      (∀ z, 0 ≤ m z) ∧ (∃ z₀, m z₀ = 1 ∧ ∀ z, z ≠ z₀ → m z = 0) ∧
        ∀ b, ∑ y, m (b, y) = 1 / 2 :=
  PairField.classicalPurificationFailsGoal

/-! ## BoundaryPole validated source interface -/

#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.leastRepeatCost
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.leastRepeatCost
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.PoleOrderOneGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.PoleOrderOneGoal
#print OperatorKO7.Meta.BoundaryObserver.BoundaryPole.PoleOrderOneGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.poleOrderOneGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.poleOrderOneGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.PoleResidueGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.PoleResidueGoal
#print OperatorKO7.Meta.BoundaryObserver.BoundaryPole.PoleResidueGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.poleResidueGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.poleResidueGoal

/-! ## PairQubit validated source interface -/

#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.pairZ
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.pairZ
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.pairX
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.pairX
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.pairY
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.pairY
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.PauliRelationsGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.PauliRelationsGoal
#print OperatorKO7.Meta.BoundaryObserver.PairQubit.PauliRelationsGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.PairSpanGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.PairSpanGoal
#print OperatorKO7.Meta.BoundaryObserver.PairQubit.PairSpanGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.PairFiberAlgebraGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.PairFiberAlgebraGoal
#print OperatorKO7.Meta.BoundaryObserver.PairQubit.PairFiberAlgebraGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.bellState
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.bellState
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.QuantumPurificationGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.QuantumPurificationGoal
#print OperatorKO7.Meta.BoundaryObserver.PairQubit.QuantumPurificationGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.fieldStateDimension
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.fieldStateDimension
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.FieldDimensionGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.FieldDimensionGoal
#print OperatorKO7.Meta.BoundaryObserver.PairQubit.FieldDimensionGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.pauli_relations
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.pauli_relations
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.pair_span
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.pair_span
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.pair_fiber_algebra
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.pair_fiber_algebra
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.quantum_purification
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.quantum_purification
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.bell_state_posSemidef
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.bell_state_posSemidef
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.field_dimension
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.field_dimension

/-! ## BoundaryPrivacy validated source interface -/

#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy.IndistinguishableRows
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy.IndistinguishableRows
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy.PrivacyDiscriminationGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy.PrivacyDiscriminationGoal
#print OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy.PrivacyDiscriminationGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy.PrivacyCostGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy.PrivacyCostGoal
#print OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy.PrivacyCostGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy.privacyDiscriminationGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy.privacyDiscriminationGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy.privacyCostGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy.privacyCostGoal

/-! ## BoundaryTheorem validated source interface -/

#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.KinematicClauseGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.KinematicClauseGoal
#print OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.KinematicClauseGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.kinematicClause
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.kinematicClause
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.PlaceOrbitClauseGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.PlaceOrbitClauseGoal
#print OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.PlaceOrbitClauseGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.placeOrbitClause
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.placeOrbitClause
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.MergeFloorGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.MergeFloorGoal
#print OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.MergeFloorGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.mergeFloor
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.mergeFloor

/-! ## M6.10: recovered complex local tomography, exact G36 -/

#check @OperatorKO7.Meta.BoundaryObserver.PairField.ComplexLocalTomographyGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairField.ComplexLocalTomographyGoal
#print OperatorKO7.Meta.BoundaryObserver.PairField.ComplexLocalTomographyGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairField.complexLocalTomographyGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairField.complexLocalTomographyGoal

open scoped Kronecker

example :
    ∀ ρ σ : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      (∀ A B : Matrix Bool Bool ℂ, A.IsHermitian → B.IsHermitian →
        (ρ * (A ⊗ₖ B)).trace = (σ * (A ⊗ₖ B)).trace) → ρ = σ :=
  PairField.complexLocalTomographyGoal

/-! M6.5: FiberResolution, goals G14 to G18. -/

#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberOneReadingGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberOneReadingGoal
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberMenu
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberMenu
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberMenu.mk
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberMenu.mk
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberMenu.rows
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberMenu.rows
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberMenu.reading_cost
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberMenu.reading_cost
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberCapacityGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberCapacityGoal
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.repeatFiber
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.repeatFiber
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberLikelihood
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberLikelihood
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberError
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberError
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberAttainmentGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberAttainmentGoal
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberFanoGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberFanoGoal
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.sparseRow
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.sparseRow
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.SparseControlGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.SparseControlGoal
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberOneReading
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberOneReading
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberCapacity
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberCapacity
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberAttainment
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberAttainment
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberFano
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberFano
#check @OperatorKO7.Meta.BoundaryObserver.FiberResolution.sparseControl
#print axioms OperatorKO7.Meta.BoundaryObserver.FiberResolution.sparseControl

example : OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberOneReadingGoal := OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberOneReading
example : OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberCapacityGoal := OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberCapacity
example : OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberAttainmentGoal := OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberAttainment
example : OperatorKO7.Meta.BoundaryObserver.FiberResolution.FiberFanoGoal := OperatorKO7.Meta.BoundaryObserver.FiberResolution.fiberFano
example : OperatorKO7.Meta.BoundaryObserver.FiberResolution.SparseControlGoal := OperatorKO7.Meta.BoundaryObserver.FiberResolution.sparseControl

/-! M6.3, M6.4 and M6.13: BoundaryPole later goals G07 to G13 and G45. -/

#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.GodelPoleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.GodelPoleGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.godelPoleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.godelPoleGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.GodelSideSymbolGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.GodelSideSymbolGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.godelSideSymbolGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.godelSideSymbolGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.DiagonalWalkGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.DiagonalWalkGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.diagonalWalkGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.diagonalWalkGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.DiagonalUnionGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.DiagonalUnionGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.diagonalUnionGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.diagonalUnionGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.OrientationPoleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.OrientationPoleGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.orientationPoleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.orientationPoleGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.CounterSideSymbolGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.CounterSideSymbolGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.counterSideSymbolGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.counterSideSymbolGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.RecursionClauseGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.RecursionClauseGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.recursionClauseGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.recursionClauseGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.TwoPointGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.TwoPointGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.twoPointGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.twoPointGoal

example : OperatorKO7.Meta.BoundaryObserver.BoundaryPole.GodelPoleGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryPole.godelPoleGoal
example : OperatorKO7.Meta.BoundaryObserver.BoundaryPole.GodelSideSymbolGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryPole.godelSideSymbolGoal
example : OperatorKO7.Meta.BoundaryObserver.BoundaryPole.DiagonalWalkGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryPole.diagonalWalkGoal
example : OperatorKO7.Meta.BoundaryObserver.BoundaryPole.DiagonalUnionGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryPole.diagonalUnionGoal
example : OperatorKO7.Meta.BoundaryObserver.BoundaryPole.OrientationPoleGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryPole.orientationPoleGoal
example : OperatorKO7.Meta.BoundaryObserver.BoundaryPole.CounterSideSymbolGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryPole.counterSideSymbolGoal
example : OperatorKO7.Meta.BoundaryObserver.BoundaryPole.RecursionClauseGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryPole.recursionClauseGoal
example : OperatorKO7.Meta.BoundaryObserver.BoundaryPole.TwoPointGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryPole.twoPointGoal

/-! M6.11: PairBell, goals G40 and G41; G42 remains a definition. -/

#check @OperatorKO7.Meta.BoundaryObserver.PairBell.aliceTest
#print axioms OperatorKO7.Meta.BoundaryObserver.PairBell.aliceTest
#check @OperatorKO7.Meta.BoundaryObserver.PairBell.bobTest
#print axioms OperatorKO7.Meta.BoundaryObserver.PairBell.bobTest
#check @OperatorKO7.Meta.BoundaryObserver.PairBell.stateCorrelation
#print axioms OperatorKO7.Meta.BoundaryObserver.PairBell.stateCorrelation
#check @OperatorKO7.Meta.BoundaryObserver.PairBell.chshScore
#print axioms OperatorKO7.Meta.BoundaryObserver.PairBell.chshScore
#check @OperatorKO7.Meta.BoundaryObserver.PairBell.BellTableGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairBell.BellTableGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairBell.schmidtState
#print axioms OperatorKO7.Meta.BoundaryObserver.PairBell.schmidtState
#check @OperatorKO7.Meta.BoundaryObserver.PairBell.PureExcessGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairBell.PureExcessGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairBell.localBlochSq
#print axioms OperatorKO7.Meta.BoundaryObserver.PairBell.localBlochSq
#check @OperatorKO7.Meta.BoundaryObserver.PairBell.SignTest
#print axioms OperatorKO7.Meta.BoundaryObserver.PairBell.SignTest
#check @OperatorKO7.Meta.BoundaryObserver.PairBell.MixedExcessGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairBell.MixedExcessGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairBell.bellTable
#print axioms OperatorKO7.Meta.BoundaryObserver.PairBell.bellTable
#check @OperatorKO7.Meta.BoundaryObserver.PairBell.pureExcess
#print axioms OperatorKO7.Meta.BoundaryObserver.PairBell.pureExcess

example : OperatorKO7.Meta.BoundaryObserver.PairBell.BellTableGoal := OperatorKO7.Meta.BoundaryObserver.PairBell.bellTable
example : OperatorKO7.Meta.BoundaryObserver.PairBell.PureExcessGoal := OperatorKO7.Meta.BoundaryObserver.PairBell.pureExcess
#check @OperatorKO7.Meta.BoundaryObserver.PairBell.mixedExcess
#print axioms OperatorKO7.Meta.BoundaryObserver.PairBell.mixedExcess
example : OperatorKO7.Meta.BoundaryObserver.PairBell.MixedExcessGoal := OperatorKO7.Meta.BoundaryObserver.PairBell.mixedExcess

/-! PairQubit: declarations added in the M6 completion pass. -/

#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.recordProjector
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.recordProjector
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.GeneratorNoetherGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.GeneratorNoetherGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.generatorNoetherGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.generatorNoetherGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.InvisiblePermutationGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.InvisiblePermutationGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.invisiblePermutationGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.invisiblePermutationGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.FrameOrbitGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.FrameOrbitGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.frameOrbitGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.frameOrbitGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.UnitaryNoetherGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.UnitaryNoetherGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.unitaryNoetherGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.unitaryNoetherGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.MeasuredRowsGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.MeasuredRowsGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.measuredRowsGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.measuredRowsGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.QuantumRecordPoleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.QuantumRecordPoleGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.quantumRecordPoleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.quantumRecordPoleGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.BitConservationGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.BitConservationGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.ComplementaryBitsGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.ComplementaryBitsGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.ComplementaryLawGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.ComplementaryLawGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.bitConservationGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.bitConservationGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.complementaryBitsGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.complementaryBitsGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairQubit.complementaryLawGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairQubit.complementaryLawGoal

/-! PairField: declarations added in the M6 completion pass. -/

#check @OperatorKO7.Meta.BoundaryObserver.PairField.RealLocalTomographyFailsGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairField.RealLocalTomographyFailsGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairField.realLocalTomographyFailsGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairField.realLocalTomographyFailsGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairField.FieldSelectionGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairField.FieldSelectionGoal
#check @OperatorKO7.Meta.BoundaryObserver.PairField.fieldSelectionGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.PairField.fieldSelectionGoal

/-! BoundaryTheorem: declarations added in the M6 completion pass. -/

#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.DemonResetGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.DemonResetGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.demonResetGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.demonResetGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.transcriptRegister
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.transcriptRegister
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.CycleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.CycleGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.cycleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.cycleGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.ApexPairGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.ApexPairGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.apexPairGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.apexPairGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.BoundaryTheoremGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.BoundaryTheoremGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.boundaryTheoremGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.boundaryTheoremGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.ApexCoreGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.ApexCoreGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.apexCoreGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.apexCoreGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.BoundaryTheoremCoreGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.BoundaryTheoremCoreGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.boundaryTheoremCoreGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.boundaryTheoremCoreGoal

/-! M6 completion Goal examples. -/

example : OperatorKO7.Meta.BoundaryObserver.PairQubit.BitConservationGoal := OperatorKO7.Meta.BoundaryObserver.PairQubit.bitConservationGoal
example : OperatorKO7.Meta.BoundaryObserver.PairQubit.ComplementaryBitsGoal := OperatorKO7.Meta.BoundaryObserver.PairQubit.complementaryBitsGoal
example : OperatorKO7.Meta.BoundaryObserver.PairQubit.ComplementaryLawGoal := OperatorKO7.Meta.BoundaryObserver.PairQubit.complementaryLawGoal
example : OperatorKO7.Meta.BoundaryObserver.PairQubit.GeneratorNoetherGoal := OperatorKO7.Meta.BoundaryObserver.PairQubit.generatorNoetherGoal
example : OperatorKO7.Meta.BoundaryObserver.PairQubit.UnitaryNoetherGoal := OperatorKO7.Meta.BoundaryObserver.PairQubit.unitaryNoetherGoal
example : OperatorKO7.Meta.BoundaryObserver.PairQubit.InvisiblePermutationGoal := OperatorKO7.Meta.BoundaryObserver.PairQubit.invisiblePermutationGoal
example : OperatorKO7.Meta.BoundaryObserver.PairQubit.FrameOrbitGoal := OperatorKO7.Meta.BoundaryObserver.PairQubit.frameOrbitGoal
example : OperatorKO7.Meta.BoundaryObserver.PairQubit.MeasuredRowsGoal := OperatorKO7.Meta.BoundaryObserver.PairQubit.measuredRowsGoal
example : OperatorKO7.Meta.BoundaryObserver.PairQubit.QuantumRecordPoleGoal := OperatorKO7.Meta.BoundaryObserver.PairQubit.quantumRecordPoleGoal
example : OperatorKO7.Meta.BoundaryObserver.PairField.RealLocalTomographyFailsGoal := OperatorKO7.Meta.BoundaryObserver.PairField.realLocalTomographyFailsGoal
example : OperatorKO7.Meta.BoundaryObserver.PairField.FieldSelectionGoal := OperatorKO7.Meta.BoundaryObserver.PairField.fieldSelectionGoal
example : OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.CycleGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.cycleGoal
example : OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.DemonResetGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.demonResetGoal
example : OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.ApexPairGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.apexPairGoal
example : OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.BoundaryTheoremGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.boundaryTheoremGoal
example : OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.ApexCoreGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.apexCoreGoal
example : OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.BoundaryTheoremCoreGoal := OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.boundaryTheoremCoreGoal
