import OperatorKO7.Meta.Physics.LandauerHeatBound
import OperatorKO7.Meta.QuantumBoundary.CategoricalLandauer
import OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy

/-!
# Landauer floor for record events

The defined floor depends on the reliable record-bit count and is invariant under changes to the redundant representation. For positive `kB` and `T`, the floor increases strictly with that count. The per-bit cost equals `erasureCost (kB * T) 1`.

Under `LandauerApplicable` and `LandauerHeatLaw`, released heat is at least the defined floor. The recursor-shaped event below is encoded as a record-formation event; that event interpretation is a modeling assumption. For finite `α`, the module also proves that the entropy of `pushforward (diag α m) p` equals `H p` for any `p : α → ℝ` and positive `m`.
-/

set_option autoImplicit false

noncomputable section

namespace OperatorKO7.Meta.Physics.ConfessionLandauerSplit

open OperatorKO7.Meta.Physics.RecordFormation
open OperatorKO7.Meta.Physics.LandauerHeatBound
open OperatorKO7.Meta.QuantumBoundary.CategoricalLandauer
open OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite

/-! ## Floor invariance under redundant representation -/

/-- The Landauer floor of a stage-2 record-formation event is a function of the committed reliable
record alone: two events whose objective records carry the same reliable-bit count have the same floor,
regardless of how their redundant carriers differ. -/
theorem landauerLowerBound_of_reliableBits
    (E F : RecordFormationEvent) (kB T : ℝ)
    (h : reliableRecordBitCount E = reliableRecordBitCount F) :
    landauerLowerBound E kB T = landauerLowerBound F kB T := by
  simp [landauerLowerBound, h]

/-- Replacing the redundant representation leaves the defined floor unchanged. -/
theorem landauerLowerBound_indep_redundancy
    (E : RecordFormationEvent) (kB T : ℝ) (rr : RedundantRepresentation) :
    landauerLowerBound { E with redundantRepresentation := rr } kB T
      = landauerLowerBound E kB T := by
  rfl

/-! ## Heat bound under applicability conditions -/

/-- Under Landauer applicability and the stated heat law, released heat is at least the floor for the committed reliable record. -/
theorem confession_record_bears_landauer_floor
    {E : RecordFormationEvent} {kB T releasedHeat : ℝ}
    (hApp : LandauerApplicable E T)
    (law : LandauerHeatLaw E kB T releasedHeat) :
    releasedHeat ≥ landauerPerBitCost kB T * (reliableRecordBitCount E : ℝ) := by
  simpa [landauerLowerBound] using landauer_per_bit_floor hApp law

/-- `landauerPerBitCost kB T` equals `erasureCost (kB * T) 1`. -/
theorem landauerPerBitCost_eq_erasureCost_one (kB T : ℝ) :
    landauerPerBitCost kB T = erasureCost (kB * T) 1 := by
  unfold landauerPerBitCost erasureCost
  push_cast
  ring

/-! ## Combined heat bound and floor invariance -/

/-- Under the Landauer assumptions, the committed record has the stated heat lower bound, and changes to the redundant representation leave the defined floor unchanged. -/
theorem confession_thermo_split
    {E : RecordFormationEvent} {kB T releasedHeat : ℝ}
    (hApp : LandauerApplicable E T)
    (law : LandauerHeatLaw E kB T releasedHeat) :
    releasedHeat ≥ landauerPerBitCost kB T * (reliableRecordBitCount E : ℝ)
    ∧ ∀ rr : RedundantRepresentation,
        landauerLowerBound { E with redundantRepresentation := rr } kB T
          = landauerLowerBound E kB T :=
  ⟨confession_record_bears_landauer_floor hApp law,
   fun rr => landauerLowerBound_indep_redundancy E kB T rr⟩

/-! ## Entropy under diagonal duplication -/

/-- For a finite type `α`, a function `p : α → ℝ`, and positive `m`, the entropy of the diagonal pushforward equals `H p`. -/
theorem redundant_carrier_zero_marginal_information
    {α : Type} [Fintype α] [DecidableEq α] {m : ℕ} (hm : 0 < m) (p : α → ℝ) :
    H (pushforward (diag α m) p) = H p :=
  diagonal_entropy_eq hm p

/-! ## Recursor-shaped event example -/

/-- A record-formation event with one reliable record bit and a redundant-representation count `payloadCopies`. -/
def recursorConfessionEvent (payloadCopies : Nat) : RecordFormationEvent where
  recordBits := ⟨1⟩
  certificateBits := ⟨1⟩
  overwrittenBits := ⟨0⟩
  discardedBits := ⟨1⟩
  objectiveState := ⟨1, 3, 2⟩
  redundantRepresentation := ⟨1, payloadCopies⟩
  cyclicStage2 := True
  entropyBudgetClosed := True
  bathIrreversible := True
  noUnaccountedWorkReservoir := True
  systemEntropyDebtBits := 0
  memoryEntropyDebtBits := 0
  externalWork := 0

/-- The five-copy and zero-copy event records have the same defined Landauer floor. -/
theorem recursorConfession_floor_indep_of_copies (kB T : ℝ) :
    landauerLowerBound (recursorConfessionEvent 5) kB T
      = landauerLowerBound (recursorConfessionEvent 0) kB T :=
  landauerLowerBound_of_reliableBits (recursorConfessionEvent 5) (recursorConfessionEvent 0) kB T rfl

/-- The recursor-shaped confession event is Landauer-applicable at unit temperature. -/
theorem recursorConfessionEvent_applicable (payloadCopies : Nat) :
    LandauerApplicable (recursorConfessionEvent payloadCopies) 1 where
  C1_thermalBath := by norm_num [C1_ThermalBathPresent]
  C2_classicalRegister := by
    unfold C2_ClassicalRegisterCreated IsObjectiveRecordState
    refine ⟨?_, ?_⟩
    · show (2 : ℕ) ≤ 3
      decide
    · show (0 : ℕ) < 1
      decide
  C3_cyclicOrEntropyAccounted := by
    unfold C3_CyclicApparatusOrEntropyAccounted
    exact ⟨Or.inl True.intro, rfl, rfl⟩
  C4_bathIrreversible := True.intro
  C5_noUnaccountedWorkReservoir := by
    unfold C5_NoUnaccountedWorkReservoir
    exact ⟨True.intro, rfl⟩
  C6_honestBitBookkeeping := by
    unfold C6_HonestBitBookkeeping
    exact ⟨rfl, rfl, rfl⟩

/-- The recursor-shaped confession event satisfies the explicit Landauer heat law at unit `kB`, `T`,
saturating at the committed-record floor. -/
theorem recursorConfessionEvent_heatLaw (payloadCopies : Nat) :
    LandauerHeatLaw (recursorConfessionEvent payloadCopies) 1 1 (landauerPerBitCost 1 1) where
  kB_pos := by norm_num
  lowerBound := by
    have h : landauerPerBitCost 1 1
          * ((recursorConfessionEvent payloadCopies).discardedBits.count : ℝ)
        - 1 * 1 * (((recursorConfessionEvent payloadCopies).systemEntropyDebtBits : ℝ)
          + ((recursorConfessionEvent payloadCopies).memoryEntropyDebtBits : ℝ))
        - (recursorConfessionEvent payloadCopies).externalWork
        = landauerPerBitCost 1 1 := by
      simp [recursorConfessionEvent]
    rw [ge_iff_le, h]

/-- This theorem applies the heat-bound and floor-invariance clauses to the five-copy event at unit `kB` and `T`. -/
theorem recursorConfession_split_witness :
    (landauerPerBitCost 1 1) ≥ landauerPerBitCost 1 1 * (reliableRecordBitCount (recursorConfessionEvent 5) : ℝ)
    ∧ ∀ rr : RedundantRepresentation,
        landauerLowerBound { (recursorConfessionEvent 5) with redundantRepresentation := rr } 1 1
          = landauerLowerBound (recursorConfessionEvent 5) 1 1 :=
  confession_thermo_split
    (recursorConfessionEvent_applicable 5)
    (recursorConfessionEvent_heatLaw 5)

/-- The defined floor of the five-copy event at unit `kB` and `T` is positive because `Real.log 2` is positive. -/
theorem recursorConfession_floor_pos :
    0 < landauerLowerBound (recursorConfessionEvent 5) 1 1 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h : landauerLowerBound (recursorConfessionEvent 5) 1 1 = Real.log 2 := by
    simp [landauerLowerBound, landauerPerBitCost, reliableRecordBitCount, recursorConfessionEvent]
  rw [h]; exact hlog

/-! ## Axiom dependencies -/

#print axioms landauerLowerBound_of_reliableBits
#print axioms landauerLowerBound_indep_redundancy
#print axioms confession_record_bears_landauer_floor
#print axioms landauerPerBitCost_eq_erasureCost_one
#print axioms confession_thermo_split
#print axioms redundant_carrier_zero_marginal_information
#print axioms recursorConfession_floor_indep_of_copies
#print axioms recursorConfessionEvent_applicable
#print axioms recursorConfessionEvent_heatLaw
#print axioms recursorConfession_split_witness
#print axioms recursorConfession_floor_pos

end OperatorKO7.Meta.Physics.ConfessionLandauerSplit
