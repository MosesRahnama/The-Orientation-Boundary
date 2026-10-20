import OperatorKO7.Meta.Physics.ConfessionLandauerSplit

/-!
# The unconditional core of the confession-Landauer floor: distinction costed, memory free (exactly)

This module extracts and sharpens the **unconditional** mathematical core of the confession-Landauer
split (`ConfessionLandauerSplit`). The split proposition the manuscript previously stated as a single
conditional package is in fact two layers, and this module separates them honestly:

* the **defined Landauer floor** `landauerLowerBound E kB T = kB·T·ln2 · (reliable record bits)` obeys an
  exact closed form, is strictly increasing in the committed reliable-bit count (more distinction is
  strictly more costed), is invariant under any redundant payload carrier (duplicated memory is free),
  and charges exactly the categorical erasure floor per bit. These are unconditional arithmetic facts
  about the defined quantity, with no physical hypothesis;
* the identification of that floor with **physically released heat** stays conditional on the Landauer
  applicability package (C1-C6) and the explicit heat law, and is not touched here: it remains
  `ConfessionLandauerSplit.confession_record_bears_landauer_floor`.

This is the precise correction the program wanted: "memory free, distinction costed" is a theorem at the
level of the cost functional, while "this floor is dissipated heat" remains an explicit physical
assumption. No claim here asserts that the recursor's confession unconditionally dissipates `kB·T·ln2`.

## Claim typing (binding)

* PROVEN (the theorems below): exact floor closed form, strict monotonicity in committed bits, invariance
  under the redundant carrier, per-bit/erasure-cost identity, and a concrete strict-increase witness. All
  compose existing baseline-clean anchors and standard `Real` order facts.
* CONDITIONAL (not in this module): the physical-heat realization, kept in `ConfessionLandauerSplit`.

## Audit slots
- Relation: NA (thermodynamic cost functional + bit bookkeeping; no rewriting relation).
- Closure: `propext`, `Classical.choice`, `Quot.sound` (or a subset); verified by `#print axioms` below.
- Trust: no `sorry`/`admit`/`axiom`/`opaque`/`partial`/`unsafe`/`native_decide`/`bv_decide`/`@[csimp]`.
- Non-vacuity (R5): `recursorConfessionEvent` and `twoBitConfessionEvent` give concrete events with
  reliable-bit counts `1` and `2`; `floor_strict_increase_witness` exhibits the strict increase
  (`ln 2 < 2·ln 2`), and `ConfessionLandauerSplit.recursorConfession_floor_pos` gives strict positivity.
- Scope: the defined floor quantity only; the physical identification is conditional and elsewhere.
-/

set_option autoImplicit false

noncomputable section

namespace OperatorKO7.Meta.Physics.ConfessionLandauerExact

open OperatorKO7.Meta.Physics.RecordFormation
open OperatorKO7.Meta.Physics.LandauerHeatBound
open OperatorKO7.Meta.QuantumBoundary.CategoricalLandauer
open OperatorKO7.Meta.Physics.ConfessionLandauerSplit

/-! ## Exact closed form of the defined floor -/

/--
Proves: the defined Landauer floor is exactly `kB·T·ln2` per committed reliable bit,
  `landauerLowerBound E kB T = kB * T * Real.log 2 * (reliableRecordBitCount E : ℝ)`.
Does not prove: that this floor is released heat (conditional; see `ConfessionLandauerSplit`).
Relation: not applicable. Closure: not applicable. Trust: kernel-only.
-/
theorem landauerLowerBound_eq_perBit_mul_bits (E : RecordFormationEvent) (kB T : ℝ) :
    landauerLowerBound E kB T = kB * T * Real.log 2 * (reliableRecordBitCount E : ℝ) := by
  unfold landauerLowerBound landauerPerBitCost
  ring

/-! ## Distinction costed: strictly increasing in the committed reliable-bit count -/

/--
Proves: for `kB > 0` and `T > 0`, an event that commits strictly more reliable bits has a strictly
  higher floor: `reliableRecordBitCount E < reliableRecordBitCount F → landauerLowerBound E kB T <
  landauerLowerBound F kB T`. The per-bit price `kB·T·ln2` is strictly positive, so the floor is strictly
  monotone in the committed-distinction count.
Does not prove: anything about released heat (conditional, elsewhere).
Relation: not applicable. Closure: not applicable. Trust: kernel-only.
Scope: `kB > 0`, `T > 0`; the inequality is on the defined floor quantity.
-/
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

/-! ## The unconditional headline: distinction costed, memory free -/

/--
Proves: the unconditional mathematical core, "distinction costed, memory free." For `kB > 0`, `T > 0`,
  the defined Landauer floor of the committed record
  (1) is strictly increasing in the committed reliable-bit count (more distinction is strictly more
      costed);
  (2) is invariant under any redundant payload carrier (duplicated memory is free);
  (3) charges exactly the categorical erasure floor `erasureCost (kB·T) 1` per committed bit.
Does not prove: that this floor is physically released heat. That identification is conditional on the
  Landauer applicability package and the heat law and is kept in
  `ConfessionLandauerSplit.confession_record_bears_landauer_floor`; nothing here asserts it.
Relation: not applicable. Closure: not applicable. Trust: kernel-only.
Scope: `kB > 0`, `T > 0`; statements about the defined floor quantity, not released heat.
-/
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

/-! ## R5 non-vacuity: a concrete strict increase -/

/-- A two-reliable-bit confession event: the recursor confession with the committed reliable-bit count
raised to `2`. Only the floor-relevant field (`objectiveState.reliableBits`) changes. -/
def twoBitConfessionEvent : RecordFormationEvent :=
  { recursorConfessionEvent 0 with
      objectiveState := { (recursorConfessionEvent 0).objectiveState with reliableBits := 2 } }

theorem oneBit_reliableRecordBitCount :
    reliableRecordBitCount (recursorConfessionEvent 0) = 1 := rfl

theorem twoBit_reliableRecordBitCount :
    reliableRecordBitCount twoBitConfessionEvent = 2 := rfl

/-- **R5 (distinction strictly costed, concrete).** A two-bit confession has a strictly higher floor than
the one-bit recursor confession (`ln 2 < 2·ln 2` at unit `kB`, `T`). The strict-monotonicity half of the
headline is non-vacuous. -/
theorem floor_strict_increase_witness :
    landauerLowerBound (recursorConfessionEvent 0) 1 1
      < landauerLowerBound twoBitConfessionEvent 1 1 := by
  have h12 : reliableRecordBitCount (recursorConfessionEvent 0)
      < reliableRecordBitCount twoBitConfessionEvent := by
    rw [oneBit_reliableRecordBitCount, twoBit_reliableRecordBitCount]
    decide
  exact landauerLowerBound_strictMono_in_reliableBits _ _ 1 1 (by norm_num) (by norm_num) h12

/-! ## Axiom inventory (must be a subset of `{propext, Classical.choice, Quot.sound}`) -/

#print axioms landauerLowerBound_eq_perBit_mul_bits
#print axioms landauerLowerBound_strictMono_in_reliableBits
#print axioms distinction_costed_memory_free
#print axioms floor_strict_increase_witness

end OperatorKO7.Meta.Physics.ConfessionLandauerExact
