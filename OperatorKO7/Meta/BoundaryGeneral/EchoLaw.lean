import Mathlib.Logic.Relation
import OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord

/-!
# The echo law: endogenous return cannot license a distinction record

This module states and proves the general law that the program's three faces
instantiate. One carrier, one state, three readings:

* **information face** - the answer channel at a state either reads the object
  coordinate (`InformativeAt`) or ignores it (`EchoAt`);
* **rewrite face** - a record surface emits records, and a licensed surface
  emits a non-null record only where a target distinction exists;
* **execution face** - an echo run appends to a record trace while the
  licensing state stays fixed.

The law itself is `no_licensed_nonnull_at_echo`: on a distinction-sound,
object-witnessed episode, an echo state emits no licensed non-null record. Its
contrapositive `nonnull_licensed_record_forces_informative_channel` is the
positive form: every licensed non-null record is paid for by a channel that
actually reads the object.

`FalseFormalLegitimacyAt` names the gap between the raw and the licensed
surface at such a state, and `ffl_forces_second_raw_target` extracts the
distinct second target that makes the gap a rewrite-level fork.

## Claim typing (binding)
* PROVEN: every theorem below, on the declared `Episode` abstraction.
* SCOPE: `ObjectWitnessed` is a stated modelling hypothesis, not a theorem. It
  is the assumption that a target distinction has an object-side witness. The
  law is exactly as strong as that hypothesis and no stronger.

## Audit slots
- Relation: none in this module; the rewrite relation enters at the crown.
- Closure: `Relation.ReflTransGen` is imported for downstream use only.
- Trust: no `sorry`/`admit`/`axiom`/`native_decide`; Mathlib baseline.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.EchoLaw

/-! ## The episode: one carrier carrying all three faces -/

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

/-! ## Information face -/

/-- The channel at `s` is an **echo**: its answer ignores the object coordinate,
so the return is a function of the querant state alone. -/
def EchoAt (E : Episode) (s : E.State) : Prop :=
  ∀ o o', E.answer s o = E.answer s o'

/-- The channel at `s` is **informative**: some object change moves the answer. -/
def InformativeAt (E : Episode) (s : E.State) : Prop :=
  ∃ o o', E.answer s o ≠ E.answer s o'

/-- Echo is exactly non-informativeness. The converse direction is classical:
absence of an inequality witness recovers equality of arbitrary answers. -/
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

/-- The target distinction is **object-witnessed**: wherever the distinction
holds, the channel reads the object coordinate. This is the modelling
hypothesis that ties the information face to the record face; it says the
distinction is a property of the object, visible through the channel, and not a
free label attached to the state. -/
def ObjectWitnessed (E : Episode) : Prop :=
  ∀ s, E.Distinction s → InformativeAt E s

/-! ## The law -/

/-- **The echo law.** On a distinction-sound, object-witnessed episode, an echo
state emits no licensed non-null record: an endogenous return cannot license a
distinction. -/
theorem no_licensed_nonnull_at_echo
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    {s : E.State} (hecho : EchoAt E s) :
    ¬ ∃ r, E.licensedEmits s r ∧ E.nonnull r := by
  rintro ⟨r, hemit, hn⟩
  exact (echoAt_iff_not_informativeAt E s).mp hecho
    (hwit s (hsound s r hemit hn))

/-- **Positive form of the law.** Every licensed non-null record is paid for by a
channel that actually reads the object coordinate. -/
theorem nonnull_licensed_record_forces_informative_channel
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    {s : E.State} {r : E.Record}
    (hemit : E.licensedEmits s r) (hn : E.nonnull r) :
    InformativeAt E s :=
  hwit s (hsound s r hemit hn)

/-- The licensed surface is silent on the whole echo region at once. -/
theorem licensed_records_null_on_echo_region
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    {s : E.State} (hecho : EchoAt E s)
    {r : E.Record} (hemit : E.licensedEmits s r) :
    ¬ E.nonnull r := by
  intro hn
  exact no_licensed_nonnull_at_echo hsound hwit hecho ⟨r, hemit, hn⟩

/-! ## False formal legitimacy -/

/-- **False formal legitimacy at `s`**: the raw surface emits a non-null record
where the licensed surface emits none. The record is action-shaped and
unwarranted at the same state. -/
def FalseFormalLegitimacyAt (E : Episode) (s : E.State) : Prop :=
  (∃ r, E.rawEmits s r ∧ E.nonnull r) ∧ ¬ ∃ r, E.licensedEmits s r ∧ E.nonnull r

/-- **The diagnosis theorem.** A raw non-null emission at an echo state is false
formal legitimacy, on any distinction-sound, object-witnessed episode. -/
theorem ffl_of_raw_nonnull_at_echo
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    {s : E.State} (hecho : EchoAt E s)
    (hraw : ∃ r, E.rawEmits s r ∧ E.nonnull r) :
    FalseFormalLegitimacyAt E s :=
  ⟨hraw, no_licensed_nonnull_at_echo hsound hwit hecho⟩

/-- At a false-formal-legitimacy state the raw surface carries a target distinct
from the null record. This is the second edge of the rewrite-face fork. -/
theorem ffl_forces_second_raw_target
    {s : E.State} (hnull : ¬ E.nonnull E.null)
    (hffl : FalseFormalLegitimacyAt E s) :
    ∃ r, E.rawEmits s r ∧ E.nonnull r ∧ r ≠ E.null := by
  obtain ⟨⟨r, hemit, hn⟩, _⟩ := hffl
  refine ⟨r, hemit, hn, ?_⟩
  intro hr
  exact hnull (hr ▸ hn)

/-- With the null record also raw-reachable, a false-formal-legitimacy state is a
raw peak with two distinct targets: the warranted null record and the
manufactured non-null one. -/
theorem ffl_raw_peak_two_distinct_targets
    {s : E.State} (hnull : ¬ E.nonnull E.null)
    (hnullRaw : E.rawEmits s E.null)
    (hffl : FalseFormalLegitimacyAt E s) :
    ∃ r, E.rawEmits s E.null ∧ E.rawEmits s r ∧ E.null ≠ r := by
  obtain ⟨r, hemit, _, hne⟩ := ffl_forces_second_raw_target hnull hffl
  exact ⟨r, hnullRaw, hemit, fun h => hne h.symm⟩

/-! ## Execution face: the trap -/

/-- An **echo run**: a step that appends to a record trace while leaving the
licensing state fixed. Record mass is the only coordinate that moves. -/
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

/-- **Activity without progress.** Along an echo run the record grows by exactly
the number of steps taken while the licensing state stays fixed. -/
theorem echo_run_transport_without_progress
    (D : EchoDynamics E) (t : D.Trace) (n : Nat) :
    D.mass (run D t n) = D.mass t + n ∧ D.stateOf (run D t n) = D.stateOf t :=
  ⟨run_mass D t n, run_state D t n⟩

/-- **The trap cannot un-echo itself.** If the run starts at an echo state, every
state along the run is that same echo state, so the law applies at every depth
and no amount of record growth licenses a non-null record. -/
theorem echo_persists_along_run
    (D : EchoDynamics E) (t : D.Trace) (hecho : EchoAt E (D.stateOf t)) (n : Nat) :
    EchoAt E (D.stateOf (run D t n)) := by
  rw [run_state]
  exact hecho

/-- **The execution-face law.** No depth of echo run produces a licensed non-null
record. Self-generated record mass is never a license. -/
theorem no_licensed_nonnull_at_any_run_depth
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    (D : EchoDynamics E) (t : D.Trace) (hecho : EchoAt E (D.stateOf t)) (n : Nat) :
    ¬ ∃ r, E.licensedEmits (D.stateOf (run D t n)) r ∧ E.nonnull r :=
  no_licensed_nonnull_at_echo hsound hwit (echo_persists_along_run D t hecho n)

end OperatorKO7.Meta.BoundaryGeneral.EchoLaw
