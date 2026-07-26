import OperatorKO7.Meta.Physics.LandauerHeatBound
import OperatorKO7.Meta.QuantumBoundary.CategoricalLandauer
import OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy

/-!
# The confession-Landauer split: free redundant discard, costed record commitment

This module mechanizes the precise thermodynamic signature of the dependency-pair confession (and of
every boundary-operator confession modelled as a stage-2 record-formation event). It states, as one
theorem, the split that the existing `RecordFormation` / `LandauerHeatBound` model already *encodes
implicitly* but never states explicitly:

1. **Free discard.** The duplicated payload carrier the confession throws away (the redundant
   representation, the `G`-stack of identical `Y` copies) is thermodynamically free: the Landauer floor
   is invariant under it. Two events that commit the same reliable record carry the same floor, no
   matter how their redundant carriers differ (`landauerLowerBound_of_reliableBits`,
   `landauerLowerBound_indep_redundancy`).

2. **Costed commit.** The Landauer floor `kB·T·ln2 · (reliable record bits)` is borne by the
   irreversible commitment of the objective record, not by the discard
   (`confession_record_bears_landauer_floor`), and that per-bit price is exactly the categorical
   erasure floor `erasureCost (kB·T) 1` (`landauerPerBitCost_eq_erasureCost_one`).

The headline `confession_thermo_split` is the conjunction. It is the exact correction of the brainstorm
slogan "the duplication of Y violates thermodynamics": the duplication is *free*, the irreversible
record commitment is the costed event. The information-theoretic reason the discard is free is the
diagonal-entropy lemma `diagonal_entropy_eq` (`H(Δ_m Y) = H(Y)`): the redundant carrier has zero
marginal Shannon information (`redundant_carrier_zero_marginal_information`).

## Claim typing (binding)

* PROVEN (the theorems below): the floor's invariance under the redundant carrier, the floor on the
  committed record (conditional on the explicit C1-C6 package and heat law), the per-bit/erasure-cost
  identity, and the diagonal-entropy re-export. All compose existing baseline-clean anchors.
* ANALOGY / MODELLING (docstring only, never asserted by a theorem): the identification "the
  dependency-pair confession *is* a stage-2 record-formation event" is the same modelling assumption
  the QEC bridge (`QECSyndromeAsStage2`) already uses; the Landauer inequality itself is an explicit
  physical assumption (the `LandauerHeatLaw` field), as in `LandauerHeatBound.lean`. No claim is made
  that the recursor's DP projection unconditionally dissipates `kB·T·ln2`.

## Audit slots
- Relation: NA (thermodynamic cost functional + record bookkeeping; no rewriting relation).
- Closure: `propext`, `Classical.choice`, `Quot.sound` (or a subset); verified by `#print axioms` below.
- Trust: no `sorry`/`admit`/`axiom`/`opaque`/`partial`/`unsafe`/`native_decide`/`bv_decide`/`@[csimp]`.
- Non-vacuity (R5): `recursorConfessionEvent` gives a concrete recursor-shaped event; the floor is the
  same for 5 redundant copies as for 0 (`recursorConfession_floor_indep_of_copies`), and the headline
  split fires on it with a strictly positive committed-record floor
  (`recursorConfession_split_witness`).
- Scope: the conditional record-formation Landauer surface only; the QM/physical identification is
  modelling, never a theorem type.
-/

set_option autoImplicit false

noncomputable section

namespace OperatorKO7.Meta.Physics.ConfessionLandauerSplit

open OperatorKO7.Meta.Physics.RecordFormation
open OperatorKO7.Meta.Physics.LandauerHeatBound
open OperatorKO7.Meta.QuantumBoundary.CategoricalLandauer
open OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite

/-! ## Free discard: the floor depends only on the committed reliable record -/

/-- The Landauer floor of a stage-2 record-formation event is a function of the committed reliable
record alone: two events whose objective records carry the same reliable-bit count have the same floor,
regardless of how their redundant carriers differ. -/
theorem landauerLowerBound_of_reliableBits
    (E F : RecordFormationEvent) (kB T : ℝ)
    (h : reliableRecordBitCount E = reliableRecordBitCount F) :
    landauerLowerBound E kB T = landauerLowerBound F kB T := by
  simp [landauerLowerBound, h]

/-- **Free discard (structural).** Replacing the redundant representation by ANY other leaves the
Landauer floor unchanged: the duplicated carrier the confession discards is thermodynamically free. -/
theorem landauerLowerBound_indep_redundancy
    (E : RecordFormationEvent) (kB T : ℝ) (rr : RedundantRepresentation) :
    landauerLowerBound { E with redundantRepresentation := rr } kB T
      = landauerLowerBound E kB T := by
  rfl

/-! ## Costed commit: the floor is borne by the irreversible record commitment -/

/-- **Costed commit.** Under the C1-C6 applicability package and the explicit heat law, the released
heat is at least the full Landauer floor carried by the committed reliable record:
`Q ≥ kB·T·ln2 · (reliable record bits)`. This is the irreversible record-commitment cost, the only
thermodynamically charged event of the confession. -/
theorem confession_record_bears_landauer_floor
    {E : RecordFormationEvent} {kB T releasedHeat : ℝ}
    (hApp : LandauerApplicable E T)
    (law : LandauerHeatLaw E kB T releasedHeat) :
    releasedHeat ≥ landauerPerBitCost kB T * (reliableRecordBitCount E : ℝ) := by
  simpa [landauerLowerBound] using landauer_per_bit_floor hApp law

/-- The record-formation per-bit cost IS the categorical erasure floor: `landauerPerBitCost kB T =
erasureCost (kB·T) 1`. The two Landauer modules charge the same `kB·T·ln2` per committed bit. -/
theorem landauerPerBitCost_eq_erasureCost_one (kB T : ℝ) :
    landauerPerBitCost kB T = erasureCost (kB * T) 1 := by
  unfold landauerPerBitCost erasureCost
  push_cast
  ring

/-! ## The headline split -/

/-- **The confession thermodynamic split (headline).** Model a confession as a stage-2
record-formation event under the C1-C6 applicability package and the explicit heat law. The
thermodynamic signature splits cleanly:
(1) the committed reliable record bears the full Landauer floor `kB·T·ln2 · (reliable bits)`;
(2) that floor is invariant under the redundant carrier the confession discards.
The duplication is not charged; the irreversible record commitment is. This is the precise correction
of "duplication violates thermodynamics": the redundant copy is free, the committed verdict is the
costed event. -/
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

/-! ## Why the redundant carrier is free (information-theoretic) -/

/-- **Why the redundant carrier is free.** The `m`-fold diagonal copy of the payload distribution
carries the SAME Shannon entropy as one copy (`diagonal_entropy_eq`, `H(Δ_m Y) = H(Y)`): the duplicated
carrier has zero marginal information. Zero marginal information is the reason its erasure need not be
paid for; the floor in `confession_thermo_split` charges only the committed record. -/
theorem redundant_carrier_zero_marginal_information
    {α : Type} [Fintype α] [DecidableEq α] {m : ℕ} (hm : 0 < m) (p : α → ℝ) :
    H (pushforward (diag α m) p) = H p :=
  diagonal_entropy_eq hm p

/-! ## R5 non-vacuity: a concrete recursor-shaped confession event -/

/-- A concrete confession event shaped like the recursor's dependency-pair projection: one committed
reliable record bit (the termination verdict), and `payloadCopies` duplicated payload carriers (the
`G`-stack of redundant `Y` copies). The redundant copies are real and counted, but they do not enter
the Landauer floor. -/
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

/-- **R5 (free discard, concrete).** Five duplicated payload copies give the EXACT SAME Landauer floor
as zero copies. The redundant carrier is free. -/
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

/-- **R5 (headline, concrete).** The confession split fires on the recursor-shaped event with five
redundant payload copies: the committed record bears the strictly positive floor `ln 2`, and that floor
is invariant under the redundant carrier. -/
theorem recursorConfession_split_witness :
    (landauerPerBitCost 1 1) ≥ landauerPerBitCost 1 1 * (reliableRecordBitCount (recursorConfessionEvent 5) : ℝ)
    ∧ ∀ rr : RedundantRepresentation,
        landauerLowerBound { (recursorConfessionEvent 5) with redundantRepresentation := rr } 1 1
          = landauerLowerBound (recursorConfessionEvent 5) 1 1 :=
  confession_thermo_split
    (recursorConfessionEvent_applicable 5)
    (recursorConfessionEvent_heatLaw 5)

/-- The committed-record floor of the recursor-shaped event is strictly positive (`ln 2 > 0`): the
costed-commit half is non-vacuous. -/
theorem recursorConfession_floor_pos :
    0 < landauerLowerBound (recursorConfessionEvent 5) 1 1 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h : landauerLowerBound (recursorConfessionEvent 5) 1 1 = Real.log 2 := by
    simp [landauerLowerBound, landauerPerBitCost, reliableRecordBitCount, recursorConfessionEvent]
  rw [h]; exact hlog

/-! ## Axiom inventory (must be a subset of `{propext, Classical.choice, Quot.sound}`) -/

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
