import OperatorKO7.Meta.Physics.ConfessionLandauerSplit

/-!
# Landauer floor from reliable record bits

For the defined floor, `landauerLowerBound E kB T` equals `kB * T * Real.log 2` times the number of reliable record bits. With positive `kB` and `T`, the floor increases with that count, stays unchanged when only the redundant representation changes, and equals the one-bit erasure cost per committed bit.

These are statements about the defined cost. Identifying it with released heat requires `LandauerApplicable` and `LandauerHeatLaw`. Trust status: PROVEN-IN-LEAN under the Mathlib baseline.
-/

set_option autoImplicit false

noncomputable section

namespace OperatorKO7.Meta.Physics.ConfessionLandauerExact

open OperatorKO7.Meta.Physics.RecordFormation
open OperatorKO7.Meta.Physics.LandauerHeatBound
open OperatorKO7.Meta.QuantumBoundary.CategoricalLandauer
open OperatorKO7.Meta.Physics.ConfessionLandauerSplit

/-! ## Formula for the defined floor -/

/-- The defined floor equals `kB * T * Real.log 2 * reliableRecordBitCount E`. Its interpretation as released heat requires `LandauerApplicable` and `LandauerHeatLaw`. Trust: kernel-only. -/
theorem landauerLowerBound_eq_perBit_mul_bits (E : RecordFormationEvent) (kB T : ℝ) :
    landauerLowerBound E kB T = kB * T * Real.log 2 * (reliableRecordBitCount E : ℝ) := by
  unfold landauerLowerBound landauerPerBitCost
  ring

/-! ## Strict increase with reliable record bits -/

/-- For positive `kB` and `T`, an event with more reliable record bits has a higher defined floor. Its interpretation as released heat requires `LandauerApplicable` and `LandauerHeatLaw`. Trust: kernel-only. -/
theorem landauerLowerBound_strictMono_in_reliableBits
    (E F : RecordFormationEvent) (kB T : ℝ) (hkB : 0 < kB) (hT : 0 < T)
    (h : reliableRecordBitCount E < reliableRecordBitCount F) :
    landauerLowerBound E kB T < landauerLowerBound F kB T := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : 0 < kB * T * Real.log 2 := mul_pos (mul_pos hkB hT) hlog
  rw [landauerLowerBound_eq_perBit_mul_bits, landauerLowerBound_eq_perBit_mul_bits]
  have hcast : (reliableRecordBitCount E : ℝ) < (reliableRecordBitCount F : ℝ) := by
    exact_mod_cast h
  exact mul_lt_mul_of_pos_left hcast hpos

/-! ## Floor increase and redundant-representation invariance -/

/-- For positive `kB` and `T`, the defined floor increases with reliable record bits, stays unchanged when the redundant representation changes, and equals the one-bit erasure cost per committed bit. The released-heat interpretation requires `LandauerApplicable` and `LandauerHeatLaw`. Trust: kernel-only. -/
theorem distinction_costed_memory_free
    (E F : RecordFormationEvent) (kB T : ℝ) (hkB : 0 < kB) (hT : 0 < T) :
    (reliableRecordBitCount E < reliableRecordBitCount F →
        landauerLowerBound E kB T < landauerLowerBound F kB T)
    ∧ (∀ rr : RedundantRepresentation,
        landauerLowerBound { E with redundantRepresentation := rr } kB T
          = landauerLowerBound E kB T)
    ∧ landauerPerBitCost kB T = erasureCost (kB * T) 1 :=
  ⟨fun h => landauerLowerBound_strictMono_in_reliableBits E F kB T hkB hT h,
   fun rr => landauerLowerBound_indep_redundancy E kB T rr,
   landauerPerBitCost_eq_erasureCost_one kB T⟩

/-! ## Two-bit example -/

/-- A two-reliable-bit confession event: the recursor confession with the committed reliable-bit count
raised to `2`. Only the floor-relevant field (`objectiveState.reliableBits`) changes. -/
def twoBitConfessionEvent : RecordFormationEvent :=
  { recursorConfessionEvent 0 with
      objectiveState := { (recursorConfessionEvent 0).objectiveState with reliableBits := 2 } }

theorem oneBit_reliableRecordBitCount :
    reliableRecordBitCount (recursorConfessionEvent 0) = 1 := rfl

theorem twoBit_reliableRecordBitCount :
    reliableRecordBitCount twoBitConfessionEvent = 2 := rfl

/-- At unit `kB` and `T`, the two-bit recursor event has a higher floor than the one-bit event. -/
theorem floor_strict_increase_witness :
    landauerLowerBound (recursorConfessionEvent 0) 1 1
      < landauerLowerBound twoBitConfessionEvent 1 1 := by
  have h12 : reliableRecordBitCount (recursorConfessionEvent 0)
      < reliableRecordBitCount twoBitConfessionEvent := by
    rw [oneBit_reliableRecordBitCount, twoBit_reliableRecordBitCount]
    decide
  exact landauerLowerBound_strictMono_in_reliableBits _ _ 1 1 (by norm_num) (by norm_num) h12

/-! ## Axiom reports -/

#print axioms landauerLowerBound_eq_perBit_mul_bits
#print axioms landauerLowerBound_strictMono_in_reliableBits
#print axioms distinction_costed_memory_free
#print axioms floor_strict_increase_witness

end OperatorKO7.Meta.Physics.ConfessionLandauerExact
