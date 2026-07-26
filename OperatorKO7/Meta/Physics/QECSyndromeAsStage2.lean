import OperatorKO7.Meta.Physics.LandauerHeatBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

namespace OperatorKO7.Meta.Physics.QECSyndromeAsStage2

open OperatorKO7.Meta.Physics.RecordFormation
open OperatorKO7.Meta.Physics.LandauerHeatBound

/-!
# QEC syndrome record adapter

`QECSyndromeRound` stores structural predicates and numerical values as input
fields. The adapter copies those fields into `RecordFormationEvent` and assigns
the syndrome count to three bit-count fields. The final theorem combines a
supplied abstain inequality with a supplied applicable `LandauerHeatLaw`; it
does not derive either physical premise from the syndrome record.
-/

/-- Abstract finite syndrome-extraction round used by the QEC bridge. -/
structure QECSyndromeRound where
  syndromeBitCount : Nat
  redundancyCount : Nat
  redundancyThreshold : Nat
  overwrittenBitCount : Nat
  cyclicStage2 : Prop
  entropyBudgetClosed : Prop
  bathIrreversible : Prop
  noUnaccountedWorkReservoir : Prop
  systemEntropyDebtBits : Nat
  memoryEntropyDebtBits : Nat
  externalWork : ℝ
  abstainErrorRateValue : ℝ
  syndromeHeatCostValue : ℝ

/-- Structural projection from a QEC syndrome round to the shared stage-2
record-formation carrier. -/
def qecSyndromeAsRecordFormation (round : QECSyndromeRound) : RecordFormationEvent where
  recordBits := ⟨round.syndromeBitCount⟩
  certificateBits := ⟨round.syndromeBitCount⟩
  overwrittenBits := ⟨round.overwrittenBitCount⟩
  discardedBits := ⟨round.syndromeBitCount⟩
  objectiveState :=
    ⟨round.syndromeBitCount, round.redundancyCount, round.redundancyThreshold⟩
  redundantRepresentation := ⟨round.syndromeBitCount, round.redundancyCount⟩
  cyclicStage2 := round.cyclicStage2
  entropyBudgetClosed := round.entropyBudgetClosed
  bathIrreversible := round.bathIrreversible
  noUnaccountedWorkReservoir := round.noUnaccountedWorkReservoir
  systemEntropyDebtBits := round.systemEntropyDebtBits
  memoryEntropyDebtBits := round.memoryEntropyDebtBits
  externalWork := round.externalWork

/-- QEC-side abstain error rate. -/
def abstainErrorRate (round : QECSyndromeRound) : ℝ :=
  round.abstainErrorRateValue

/-- QEC-side released heat for the syndrome-formation round. -/
def syndromeHeatCost (round : QECSyndromeRound) : ℝ :=
  round.syndromeHeatCostValue

/-- Historical mutual-information label for `reliableRecordBitCount`; no entropy expression is
defined by this abbreviation. -/
noncomputable def recordedMutualInformation (E : RecordFormationEvent) : ℝ :=
  reliableRecordBitCount E

/-- The three relevant bit-count fields agree because the adapter assigns each from
`round.syndromeBitCount`. -/
theorem qecSyndromeAsRecordFormation_honestBitBookkeeping
    (round : QECSyndromeRound) :
    C6_HonestBitBookkeeping (qecSyndromeAsRecordFormation round) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Pairs the supplied `hAbstain` inequality with the lower bound obtained from the supplied
`LandauerHeatLaw` and `LandauerApplicable` witnesses. The positivity hypotheses `h_kB` and `h_T`
are present in the interface but are not used to construct either supplied witness. -/
theorem qec_abstain_bound_landauer_annotated
    (round : QECSyndromeRound)
    (kB T : ℝ)
    (h_kB : 0 < kB)
    (h_T : 0 < T)
    (hApp : LandauerApplicable (qecSyndromeAsRecordFormation round) T)
    (law : LandauerHeatLaw
      (qecSyndromeAsRecordFormation round) kB T (syndromeHeatCost round))
    (τ_Y : ℝ)
    (hAbstain : abstainErrorRate round ≤ 1 - τ_Y) :
    abstainErrorRate round ≤ 1 - τ_Y ∧
      syndromeHeatCost round ≥
        kB * T * Real.log 2 * recordedMutualInformation (qecSyndromeAsRecordFormation round) := by
  have _ := h_kB
  have _ := h_T
  constructor
  · exact hAbstain
  · simpa [syndromeHeatCost, landauerLowerBound, landauerPerBitCost, recordedMutualInformation]
      using landauer_per_bit_floor hApp law

end OperatorKO7.Meta.Physics.QECSyndromeAsStage2
