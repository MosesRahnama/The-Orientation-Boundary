import OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
import OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity
import OperatorKO7.Meta.SafeStep.BranchEntropyGeneral
import OperatorKO7.Meta.SafeStep.GaugeFixingGuard
import OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord

/-!
# Gate Theorem: concrete KO7 weld

This module welds the Gate event to the live KO7 occurrence carrier, the
`R_rec_succ` dependency-pair channel, the SafeStep diagonal distinction guard,
and the real three-node `eqW void void` terminal-multiplicity accounting.

The duplicated generator is represented at the occurrence layer by the pair
`(s, frame)` and `(s, active)`: equal Trace value, distinct role. The compiled DP
channel uses the same role split on `Occ Unit` to select the extracted recursive
callee. These are deliberately not identified as the same Trace encoding:
`DPChannelInstance.step_ne_extracted` proves the frame term `s` differs from the
recursive callee `recΔ b s n`.

Scope fence: derives the license event and its accounting, NOT Arts–Giesl soundness.
In particular, this module does not prove that termination of the extracted DP
problem transfers to termination of the original rewriting system. That remains
the imported dependency-pair soundness boundary described by the workstream.

Relation: `Step` / `MetaDependencyPairs.DPPair` on the `R_rec_succ` family, plus
`KO7LocalCone.LocalRaw` and `KO7LocalCone.LocalLicensed` for the confluence-side
accounting. Closure: local cone reachability only on the quantitative side.
Trust: kernel checked, Mathlib baseline only.
-/

set_option autoImplicit false

open OperatorKO7 Trace
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone
open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity
open OperatorKO7.Meta.SafeStep.BranchEntropyGeneral
open OperatorKO7.Meta.SafeStep.GaugeFixingGuard
open OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord

namespace OperatorKO7.Meta.DistinctionBoundary.GateTheorem

/-- A concrete record-license event: the supplied surface emits at least one
non-null record on the indexed input pair. -/
def HasNonNullRecord (S : RecordSurface) (a b : S.Witness) : Prop :=
  ∃ r, S.emits a b r ∧ S.nonnull r

/-- The frame occurrence of the duplicated generator. -/
def generatorFrame (s : Trace) : Occ Trace := (s, Role.frame)

/-- The active occurrence of the same duplicated generator. -/
def generatorActive (s : Trace) : Occ Trace := (s, Role.active)

private theorem nonnullRecord_of_distinct {W : Type} {a b : W} (hab : a ≠ b) :
    HasNonNullRecord (ko7RecordSurface W) a b := by
  exact ⟨Rec.diff a b, Or.inr ⟨hab, rfl⟩, trivial⟩

private theorem hasNonNullRecord_iff_distinct {W : Type} {a b : W} :
    HasNonNullRecord (ko7RecordSurface W) a b ↔ a ≠ b := by
  constructor
  · rintro ⟨r, he, hn⟩
    exact nonnull_has_distinction (ko7_distinctionComplete W) he hn
  · exact nonnullRecord_of_distinct

/-- **G1.** The two duplicated-generator occurrences have the same live Trace
value. The second conjunct ties the active occurrence to the step-argument slot
inside the actual extracted `recΔ b s n` callee, so this is a statement about
the live `R_rec_succ` extraction and not only a generic role pair. -/
theorem ko7_generator_pair_valueDiag (b s n : Trace) :
    (generatorFrame s).1 = (generatorActive s).1 ∧
    extractRecSuccDP b s n = recΔ b (generatorActive s).1 n := by
  exact ⟨rfl, rfl⟩

/-- **G2.** The same two occurrences have distinct frame/active roles. The proof
is tied to the live occurrence carrier via `occ_frame_ne_active`. -/
theorem ko7_generator_pair_roleDistinct (b s n : Trace) :
    (generatorFrame s).2 ≠ (generatorActive s).2 := by
  intro hrole
  apply occ_frame_ne_active s
  apply Prod.ext
  · exact (ko7_generator_pair_valueDiag b s n).1
  · exact hrole

/-- **G3.** On the concrete KO7 record surfaces, the live duplicated-generator
pair refuses a non-null value record while admitting a non-null role record. -/
theorem gate_ko7 (b s n : Trace) :
    (¬ HasNonNullRecord (ko7RecordSurface Trace)
      (generatorFrame s).1 (generatorActive s).1) ∧
    HasNonNullRecord (ko7RecordSurface Role)
      (generatorFrame s).2 (generatorActive s).2 := by
  constructor
  · intro hrec
    have hne : (generatorFrame s).1 ≠ (generatorActive s).1 :=
      (hasNonNullRecord_iff_distinct.mp hrec)
    exact hne (ko7_generator_pair_valueDiag b s n).1
  · exact nonnullRecord_of_distinct (ko7_generator_pair_roleDistinct b s n)

/-- **G4.** The non-null role-record event is equivalent, on the live
`R_rec_succ` family, to the actual DP channel separating frame from active,
together with the same-input `Step`/`DPPair` extraction certificate and the
proved failure of value-only factorization. This identifies the issued role
record with the concrete DP-license event without claiming DP soundness. -/
theorem roleRecord_is_dp_license (b s n : Trace) :
    HasNonNullRecord (ko7RecordSurface Role) Role.frame Role.active ↔
      actualDPChannel b s n (((), Role.frame) : Occ Unit) ≠
          actualDPChannel b s n (((), Role.active) : Occ Unit) ∧
      Step (recΔ b s (delta n)) (app s (extractRecSuccDP b s n)) ∧
      DPPair (recΔ b s (delta n)) (extractRecSuccDP b s n) ∧
      (¬ ∃ g : Unit → Bool, ∀ o : Occ Unit,
        actualDPChannel b s n o = g o.1) := by
  constructor
  · intro hroleRecord
    have hrole : Role.frame ≠ Role.active :=
      hasNonNullRecord_iff_distinct.mp hroleRecord
    have hsep :
        actualDPChannel b s n (((), Role.frame) : Occ Unit) ≠
          actualDPChannel b s n (((), Role.active) : Occ Unit) := by
      intro hEq
      have hactive :
          decodeActive (actualDPChannel b s n (((), Role.active) : Occ Unit)) :=
        (actualDPChannel_decodes_isActive b s n
          (((), Role.active) : Occ Unit)).mpr rfl
      rw [← hEq] at hactive
      have hframeActive : isActive (((), Role.frame) : Occ Unit) :=
        (actualDPChannel_decodes_isActive b s n
          (((), Role.frame) : Occ Unit)).mp hactive
      exact hrole hframeActive
    have hcert := extractRecSuccDP_certified b s n
    exact ⟨hsep, hcert.1, hcert.2,
      actual_dp_license_not_value_factored b s n⟩
  · intro hdp
    have hrole : Role.frame ≠ Role.active := by
      intro hEq
      apply hdp.1
      apply congrArg (actualDPChannel b s n)
      apply Prod.ext
      · rfl
      · exact hEq
    exact nonnullRecord_of_distinct hrole

/-- **G5.** For the concrete KO7 record surface, refusal of every non-null value
record is exactly refusal of the SafeStep distinction license. The theorem is
general in the two Trace inputs; the diagonal instance is used by G7. -/
theorem valueRefusal_is_safestep_guard (a b : Trace) :
    (¬ HasNonNullRecord (ko7RecordSurface Trace) a b) ↔
      ¬ DistinctionLicense a b := by
  change (¬ HasNonNullRecord (ko7RecordSurface Trace) a b) ↔ ¬ (a ≠ b)
  rw [hasNonNullRecord_iff_distinct]

/-- **G6.** The real KO7 local cone loses one bit when the raw two-verdict
terminal support is licensed down to one verdict, and that bit equals the
base-two entropy of the two-valued frame/active role channel. The structural
terminal-multiplicity theorem is carried alongside the entropy equality. -/
theorem refused_bit_eq_spent_bit_ko7 :
    (branchEntropy (terminalMultiplicity LocalRaw .source) -
        branchEntropy (terminalMultiplicity LocalLicensed .source) =
      branchEntropy 2) ∧
    structuralHartleyCollapse LocalRaw LocalLicensed .source = 1 := by
  constructor
  · rw [raw_terminalMultiplicity_eq_two, licensed_terminalMultiplicity_eq_one,
      branchEntropy_two, branchEntropy_one]
    norm_num
  · exact ko7_structuralHartleyCollapse_eq_one

/-- **G7, capstone.** The KO7 recursor exposes a value-diagonal but role-distinct
duplicated-generator pair. Its role record is exactly the live DP-license event:
the actual channel separates frame/active, the same input has the certified
`Step`/`DPPair` extraction, and the channel cannot factor through its erased
value. The value record is refused by the SafeStep distinction guard. The real
KO7 local-cone refusal cost equals the two-role channel cost, one bit.

This derives license issuance and accounting only. It does not derive
Arts–Giesl dependency-pair soundness. -/
theorem gate_derives_dp_license (b s n : Trace) :
    (¬ HasNonNullRecord (ko7RecordSurface Trace) s s) ∧
    HasNonNullRecord (ko7RecordSurface Role) Role.frame Role.active ∧
    (¬ ∃ g : Trace → Bool, ∀ o : Occ Trace,
      (isActive o ↔ g o.1 = true)) ∧
    actualDPChannel b s n (((), Role.frame) : Occ Unit) ≠
      actualDPChannel b s n (((), Role.active) : Occ Unit) ∧
    Step (recΔ b s (delta n)) (app s (extractRecSuccDP b s n)) ∧
    DPPair (recΔ b s (delta n)) (extractRecSuccDP b s n) ∧
    (¬ ∃ g : Unit → Bool, ∀ o : Occ Unit,
      actualDPChannel b s n o = g o.1) ∧
    (¬ DistinctionLicense s s) ∧
    (branchEntropy (terminalMultiplicity LocalRaw .source) -
        branchEntropy (terminalMultiplicity LocalLicensed .source) =
      branchEntropy 2) ∧
    structuralHartleyCollapse LocalRaw LocalLicensed .source = 1 := by
  have hg := gate_ko7 b s n
  have hvalue : ¬ HasNonNullRecord (ko7RecordSurface Trace) s s := by
    simpa [generatorFrame, generatorActive] using hg.1
  have hrole : HasNonNullRecord (ko7RecordSurface Role) Role.frame Role.active := by
    simpa [generatorFrame, generatorActive] using hg.2
  have hdp := (roleRecord_is_dp_license b s n).mp hrole
  have hguard := (valueRefusal_is_safestep_guard s s).mp hvalue
  have hbits := refused_bit_eq_spent_bit_ko7
  exact ⟨hvalue, hrole, isActive_not_value_factored s,
    hdp.1, hdp.2.1, hdp.2.2.1, hdp.2.2.2,
    hguard, hbits.1, hbits.2⟩

/-! ## Public reach and axiom surface -/

#check @HasNonNullRecord
#check @generatorFrame
#check @generatorActive
#check @ko7_generator_pair_valueDiag
#check @ko7_generator_pair_roleDistinct
#check @gate_ko7
#check @roleRecord_is_dp_license
#check @valueRefusal_is_safestep_guard
#check @refused_bit_eq_spent_bit_ko7
#check @gate_derives_dp_license

#print axioms HasNonNullRecord
#print axioms generatorFrame
#print axioms generatorActive
#print axioms ko7_generator_pair_valueDiag
#print axioms ko7_generator_pair_roleDistinct
#print axioms gate_ko7
#print axioms roleRecord_is_dp_license
#print axioms valueRefusal_is_safestep_guard
#print axioms refused_bit_eq_spent_bit_ko7
#print axioms gate_derives_dp_license

end OperatorKO7.Meta.DistinctionBoundary.GateTheorem
