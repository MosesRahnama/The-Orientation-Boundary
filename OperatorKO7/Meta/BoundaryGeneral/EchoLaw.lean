import Mathlib.Logic.Relation
import OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord

/-!
# Echo and licensed records

An `Episode` has states, object coordinates, answers, records, a target-distinction predicate, and raw and licensed emission relations. `EchoAt` means the answer is independent of the object. `InformativeAt` means some pair of objects gives different answers. `LicensedSound` requires every licensed non-null record to assert the target distinction. `ObjectWitnessed` requires each target distinction to imply an informative channel.

Under `LicensedSound` and `ObjectWitnessed`, an echo state has no licensed non-null record. Conversely, any licensed non-null record implies an informative channel. `FalseFormalLegitimacyAt` means that the raw surface emits a non-null record and the licensed surface emits none. If the null record is not non-null, this condition yields a distinct raw target alongside the null record.

`EchoDynamics` models a run that adds one record unit per step while its licensing state stays fixed. The run mass is the initial mass plus the number of steps, and no licensed non-null record appears at any run depth that starts at an echo state.

This module defines an abstract episode and does not define a term-rewriting relation. Trust: Mathlib baseline; no `sorry`, `admit`, `axiom`, or `native_decide` occurs here.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.EchoLaw

/-! ## Episode data -/

/-- A licensed emission episode. `answer` is the query channel, read at a state
against an object coordinate; `Distinction` is the target property a non-null
record would assert; `rawEmits` and `licensedEmits` are the unguarded and
guarded record surfaces on the same states. -/
structure Episode where
  /-- Licensing states. -/
  State : Type
  /-- The object coordinate the channel may or may not read. -/
  Object : Type
  /-- Channel answers. -/
  Answer : Type
  /-- Emitted records. -/
  Record : Type
  /-- The null record. -/
  null : Record
  /-- Which records are non-null. -/
  nonnull : Record → Prop
  /-- The query channel. -/
  answer : State → Object → Answer
  /-- The target distinction a non-null record asserts. -/
  Distinction : State → Prop
  /-- Unguarded emission. -/
  rawEmits : State → Record → Prop
  /-- Guarded emission. -/
  licensedEmits : State → Record → Prop

variable {E : Episode}

/-! ## Channel behavior -/

/-- At `s`, the answer is an echo when it is independent of the object coordinate. -/
def EchoAt (E : Episode) (s : E.State) : Prop :=
  ∀ o o', E.answer s o = E.answer s o'

/-- The channel at `s` is **informative**: some object change moves the answer. -/
def InformativeAt (E : Episode) (s : E.State) : Prop :=
  ∃ o o', E.answer s o ≠ E.answer s o'

/-- Echo is equivalent to the absence of any object pair with different answers. -/
theorem echoAt_iff_not_informativeAt (E : Episode) (s : E.State) :
    EchoAt E s ↔ ¬ InformativeAt E s := by
  constructor
  · rintro h ⟨o, o', hne⟩
    exact hne (h o o')
  · intro h o o'
    refine Classical.byContradiction (fun hne => ?_)
    exact h ⟨o, o', hne⟩

/-- An informative channel is not an echo. -/
theorem not_echoAt_of_informativeAt {s : E.State}
    (h : InformativeAt E s) : ¬ EchoAt E s := by
  intro he
  exact (echoAt_iff_not_informativeAt E s).mp he h

/-! ## The two declared hypotheses -/

/-- The licensed surface is **distinction-sound**: a non-null licensed record at
`s` requires the target distinction at `s`. This is the record-side soundness
condition, the abstract form of `DistinctionRecord.DistinctionComplete`. -/
def LicensedSound (E : Episode) : Prop :=
  ∀ s r, E.licensedEmits s r → E.nonnull r → E.Distinction s

/-- `ObjectWitnessed E` states that every target distinction makes the channel informative at that state. -/
def ObjectWitnessed (E : Episode) : Prop :=
  ∀ s, E.Distinction s → InformativeAt E s

/-! ## The law -/

/-- Under `LicensedSound` and `ObjectWitnessed`, an echo state emits no licensed non-null record. -/
theorem no_licensed_nonnull_at_echo
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    {s : E.State} (hecho : EchoAt E s) :
    ¬ ∃ r, E.licensedEmits s r ∧ E.nonnull r := by
  rintro ⟨r, hemit, hn⟩
  exact (echoAt_iff_not_informativeAt E s).mp hecho
    (hwit s (hsound s r hemit hn))

/-- Under the same hypotheses, every licensed non-null record implies that the channel reads the object coordinate. -/
theorem nonnull_licensed_record_forces_informative_channel
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    {s : E.State} {r : E.Record}
    (hemit : E.licensedEmits s r) (hn : E.nonnull r) :
    InformativeAt E s :=
  hwit s (hsound s r hemit hn)

/-- At an echo state, every licensed record is null under `LicensedSound` and `ObjectWitnessed`. -/
theorem licensed_records_null_on_echo_region
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    {s : E.State} (hecho : EchoAt E s)
    {r : E.Record} (hemit : E.licensedEmits s r) :
    ¬ E.nonnull r := by
  intro hn
  exact no_licensed_nonnull_at_echo hsound hwit hecho ⟨r, hemit, hn⟩

/-! ## False formal legitimacy -/

/-- `FalseFormalLegitimacyAt` means that a state raw-emits a non-null record and emits no licensed non-null record. -/
def FalseFormalLegitimacyAt (E : Episode) (s : E.State) : Prop :=
  (∃ r, E.rawEmits s r ∧ E.nonnull r) ∧ ¬ ∃ r, E.licensedEmits s r ∧ E.nonnull r

/-- Under `LicensedSound` and `ObjectWitnessed`, raw non-null emission at an echo state gives `FalseFormalLegitimacyAt`. -/
theorem ffl_of_raw_nonnull_at_echo
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    {s : E.State} (hecho : EchoAt E s)
    (hraw : ∃ r, E.rawEmits s r ∧ E.nonnull r) :
    FalseFormalLegitimacyAt E s :=
  ⟨hraw, no_licensed_nonnull_at_echo hsound hwit hecho⟩

/-- If the null record is not non-null, `FalseFormalLegitimacyAt` supplies a raw non-null record distinct from the null record. -/
theorem ffl_forces_second_raw_target
    {s : E.State} (hnull : ¬ E.nonnull E.null)
    (hffl : FalseFormalLegitimacyAt E s) :
    ∃ r, E.rawEmits s r ∧ E.nonnull r ∧ r ≠ E.null := by
  obtain ⟨⟨r, hemit, hn⟩, _⟩ := hffl
  refine ⟨r, hemit, hn, ?_⟩
  intro hr
  exact hnull (hr ▸ hn)

/-- With a raw emission of the null record, `FalseFormalLegitimacyAt` gives two distinct raw record targets. -/
theorem ffl_raw_peak_two_distinct_targets
    {s : E.State} (hnull : ¬ E.nonnull E.null)
    (hnullRaw : E.rawEmits s E.null)
    (hffl : FalseFormalLegitimacyAt E s) :
    ∃ r, E.rawEmits s E.null ∧ E.rawEmits s r ∧ E.null ≠ r := by
  obtain ⟨r, hemit, _, hne⟩ := ffl_forces_second_raw_target hnull hffl
  exact ⟨r, hnullRaw, hemit, fun h => hne h.symm⟩

/-! ## Echo dynamics -/

/-- An echo step adds one record unit and keeps the licensing state fixed. -/
structure EchoDynamics (E : Episode) where
  /-- Execution traces. -/
  Trace : Type
  /-- Accumulated record mass. -/
  mass : Trace → Nat
  /-- The licensing state a trace sits at. -/
  stateOf : Trace → E.State
  /-- One echo step. -/
  step : Trace → Trace
  /-- The step appends exactly one record. -/
  mass_grows : ∀ t, mass (step t) = mass t + 1
  /-- The step moves no licensing coordinate. -/
  state_fixed : ∀ t, stateOf (step t) = stateOf t

variable {D : EchoDynamics E}

/-- Iterate the echo step. -/
def run (D : EchoDynamics E) (t : D.Trace) : Nat → D.Trace
  | 0 => t
  | n + 1 => D.step (run D t n)

/-- **Record mass grows without bound along an echo run.** -/
theorem run_mass (D : EchoDynamics E) (t : D.Trace) (n : Nat) :
    D.mass (run D t n) = D.mass t + n := by
  induction n with
  | zero => simp [run]
  | succ k ih => simp [run, D.mass_grows, ih, Nat.add_assoc]

/-- **The licensing state never moves along an echo run.** -/
theorem run_state (D : EchoDynamics E) (t : D.Trace) (n : Nat) :
    D.stateOf (run D t n) = D.stateOf t := by
  induction n with
  | zero => rfl
  | succ k ih => rw [run, D.state_fixed, ih]

/-- A run of `n` echo steps has mass `D.mass t + n` and the same licensing state as `t`. -/
theorem echo_run_transport_without_progress
    (D : EchoDynamics E) (t : D.Trace) (n : Nat) :
    D.mass (run D t n) = D.mass t + n ∧ D.stateOf (run D t n) = D.stateOf t :=
  ⟨run_mass D t n, run_state D t n⟩

/-- A run that starts at an echo state remains at that state at every depth. -/
theorem echo_persists_along_run
    (D : EchoDynamics E) (t : D.Trace) (hecho : EchoAt E (D.stateOf t)) (n : Nat) :
    EchoAt E (D.stateOf (run D t n)) := by
  rw [run_state]
  exact hecho

/-- Under `LicensedSound` and `ObjectWitnessed`, no run starting at an echo state has a licensed non-null record at any depth. -/
theorem no_licensed_nonnull_at_any_run_depth
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    (D : EchoDynamics E) (t : D.Trace) (hecho : EchoAt E (D.stateOf t)) (n : Nat) :
    ¬ ∃ r, E.licensedEmits (D.stateOf (run D t n)) r ∧ E.nonnull r :=
  no_licensed_nonnull_at_echo hsound hwit (echo_persists_along_run D t hecho n)

end OperatorKO7.Meta.BoundaryGeneral.EchoLaw
