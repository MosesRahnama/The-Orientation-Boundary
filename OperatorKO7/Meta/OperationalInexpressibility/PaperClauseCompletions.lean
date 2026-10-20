import OperatorKO7.Meta.SchemaOffsetAndWrapper
import OperatorKO7.Meta.RecordEmissionNecessity
import OperatorKO7.Meta.OperationalInexpressibility.ProgressOrbitEquivalence
import OperatorKO7.Meta.Confluence_Safe

/-!
# Four clauses of the Operational Inexpressibility paper

Four statements of the Operational Inexpressibility paper carry a clause that the cited Lean left
in prose. `prop:S-retained` names the counter as the only permutation-invariant strictly descending
coordinate of the trace; `cor:y-bridge` names the generator token as the only inhabitant of the
frame slot and of the active-site slot; `thm:progress-quotient` gives the progress quotient at least
two points when the index set has two; `prop:eqW-overlap` says that the guard `a ≠ b` removes the
reflexive overlap. This file proves the four clauses.
-/

set_option autoImplicit false

universe u v w

namespace OperatorKO7.StepDuplicating
namespace StepDuplicatingSchema
namespace BaseDuplicatingSystem

/-- The three coordinates of the trace at a step: the counter, the wrapper-stack multiplicity and
the payload multiplicity. -/
inductive TraceCoordinate
  | counter
  | stack
  | copies
  deriving DecidableEq, Repr

/-- The value of a trace coordinate at step `i` of the trace with counter `k`. -/
def coordinateValue (k : Nat) : TraceCoordinate → Nat → Nat
  | .counter, i => trace_ctr k i
  | .stack, i => trace_wraps i
  | .copies, i => trace_pay i

/-- Every trace coordinate is fixed by every permutation of the payload positions. -/
theorem coordinateValue_gaugeInvariant {B : Type} (k i : Nat) (c : TraceCoordinate) :
    GaugeInvariant (fun (_ : PayloadTuple B i) => coordinateValue k c i) :=
  constCoord_gaugeInvariant _

/-- Proposition `prop:S-retained`, uniqueness clause: while the counter has not run out, the counter
is the only trace coordinate that is permutation-invariant and strictly descends at the step. -/
theorem retained_coordinate_unique {B : Type} (k i : Nat) (hik : i < k) (c : TraceCoordinate) :
    (GaugeInvariant (fun (_ : PayloadTuple B i) => coordinateValue k c i) ∧
        coordinateValue k c (i + 1) < coordinateValue k c i) ↔ c = .counter := by
  constructor
  · rintro ⟨-, h⟩
    cases c with
    | counter => rfl
    | stack => exact absurd h (show ¬ (i + 1 < i) by omega)
    | copies => exact absurd h (show ¬ (i + 1 + 1 < i + 1) by omega)
  · rintro rfl
    exact ⟨coordinateValue_gaugeInvariant k i .counter, trace_ctr_strict_descent k i hik⟩

end BaseDuplicatingSystem

namespace RecordTerm

/-- The frame slot has the generator sort, whose only inhabitant is the token `gen`. -/
theorem frame_slot_unique (g : RecordGenerator) (t : RecordTerm) :
    RecordTerm.frame g t = RecordTerm.frame .gen t := by
  cases g
  rfl

/-- The generator position of the active site has the generator sort as well. -/
theorem active_slot_unique (t : RecordTerm) (g : RecordGenerator) (n : RecordCounter) :
    RecordTerm.active t g n = RecordTerm.active t .gen n := by
  cases g
  rfl

/-- Corollary `cor:y-bridge`: the generator token alone fills the frame slot and the active-site
slot, and the right-hand side of the primitive duplicator carries it at a frame generator position
and at a distinct active generator position. -/
theorem shared_generator_bridge (n : RecordCounter) :
    (∀ g : RecordGenerator, g = .gen) ∧
      (∀ (g : RecordGenerator) (t : RecordTerm), RecordTerm.frame g t = RecordTerm.frame .gen t) ∧
      (∀ (t : RecordTerm) (g : RecordGenerator) (m : RecordCounter),
        RecordTerm.active t g m = RecordTerm.active t .gen m) ∧
      ∃ p q, p ≠ q ∧ p ∈ generatorPositions (primitiveDuplicatorRhs n) ∧
        q ∈ generatorPositions (primitiveDuplicatorRhs n) ∧
        p.isFrameGeneratorPos ∧ q.isActiveGeneratorPos :=
  ⟨fun g => by cases g; rfl, frame_slot_unique, active_slot_unique,
    architectural_necessity_of_payload_duplication
      (primitiveDuplicatorRhs_emitsNewRecordFrame n)
      (primitiveDuplicatorRhs_preservesRecursiveGenerator n)⟩

end RecordTerm

end StepDuplicatingSchema
end OperatorKO7.StepDuplicating

namespace OperatorKO7.Meta.OperationalInexpressibility.ProgressOrbitEquivalence

/-- Theorem `thm:progress-quotient`, cardinality clause: two distinct indices give two distinct
points of the progress quotient. -/
theorem progressLicensedQuotient_two_points {I : Type u} {A : Type v} {B : Type w}
    (O : IndexedOrbitSystem I A) (P : IndexedOrbitSystem I B) {i j : I} (hij : i ≠ j) :
    ∃ x y : progressLicensedQuotient O P, x ≠ y :=
  ⟨(progressQuotientEquiv O P).symm i, (progressQuotientEquiv O P).symm j,
    fun h => hij ((progressQuotientEquiv O P).symm.injective h)⟩

/-- The progress quotient has more than one point when the index set has more than one. -/
theorem progressLicensedQuotient_nontrivial {I : Type u} {A : Type v} {B : Type w}
    (O : IndexedOrbitSystem I A) (P : IndexedOrbitSystem I B) [Nontrivial I] :
    Nontrivial (progressLicensedQuotient O P) := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  exact ⟨progressLicensedQuotient_two_points O P hij⟩

end OperatorKO7.Meta.OperationalInexpressibility.ProgressOrbitEquivalence

namespace MetaSN_KO7

open OperatorKO7 Trace

/-- Proposition `prop:eqW-overlap`, guard clause: under the guarded relation the reflexive overlap
`eqW void void` has the single reduct `void`, because the guard `a ≠ b` blocks the second rule. -/
theorem safeStep_eqW_void_void_unique {t : Trace} (h : SafeStep (eqW void void) t) : t = void := by
  cases h with
  | R_eq_refl _ _ => rfl
  | R_eq_diff _ _ hne => exact absurd rfl hne

/-- The guarded relation joins locally at `eqW void void`, where the unguarded relation does not. -/
theorem localJoin_eqW_void_void_safe : LocalJoinSafe (eqW void void) :=
  localJoin_of_unique (eqW void void) void (fun h => safeStep_eqW_void_void_unique h)

end MetaSN_KO7
