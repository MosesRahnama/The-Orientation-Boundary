import OperatorKO7.Meta.BoundaryGeneral.EchoForkTrapCrown

/-!
# Non-vacuity: the equality-witness diagonal is an instance of the echo law

The echo law is stated over an abstraction, so it needs a witness that inhabits
every hypothesis and exhibits the conclusion. This module supplies one, built
from the equality-witness comparator that the Distinction Boundary paper
studies.

The episode compares a pair. The channel answers "distinct?" by reading an
object probe when the pair is genuinely distinct, and answering "same" without
reading anything when the pair is diagonal. The raw surface fires both
comparator rules unconditionally; the licensed surface guards the difference
rule by disequality.

The consequences are exactly the law's predictions, at the diagonal:

* `eqwEpisode_echo_on_diagonal` - the diagonal is an echo state;
* `eqwEpisode_informative_off_diagonal` - every off-diagonal state is exogenous;
* `eqwEpisode_licensedSound`, `eqwEpisode_objectWitnessed` - both hypotheses hold;
* `eqwEpisode_ffl_on_diagonal` - the raw surface manufactures a record there,
  so the diagonal carries false formal legitimacy;
* `eqwEpisode_fork_on_diagonal` - the emission graph loses confluence there.

Nothing is assumed: the witness is constructed and every field is discharged.

## Claim typing (binding)
* PROVEN: the theorems below, on the declared finite comparator episode.
* SCOPE: this is a comparator model of the `eqW` rule pair, not the KO7 kernel
  itself. The kernel-level co-location of the same two faces is
  `EqWDiagonalDeficit.eqW_diagonal_echo_vacuum_with_fork`, and the schema-level
  minimality is the `MinimalFork` stack.

## Audit slots
- Relation: `EchoForkTrapCrown.RawEmitStep` on the instance episode.
- Closure: `Quantitative.Reach`. Trust: no `sorry`/`admit`/`axiom`; Mathlib baseline.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.EchoLawInstance

open OperatorKO7.Meta.BoundaryGeneral.EchoLaw
open OperatorKO7.Meta.BoundaryGeneral.EchoForkTrapCrown
open OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord

variable {W : Type} [DecidableEq W]

/-- The comparator episode. States are compared pairs; the object probe is a
Boolean; the answer reads the probe exactly when the pair is distinct. -/
def eqwEpisode (W : Type) [DecidableEq W] : Episode where
  State := W × W
  Object := Bool
  Answer := Bool
  Record := Rec W
  null := Rec.void
  nonnull := Rec.nonnull
  answer := fun p o => if p.1 = p.2 then false else o
  Distinction := fun p => p.1 ≠ p.2
  rawEmits := fun p r => r = Rec.void ∨ r = Rec.diff p.1 p.2
  licensedEmits := fun p r => r = Rec.void ∨ (p.1 ≠ p.2 ∧ r = Rec.diff p.1 p.2)

/-- The diagonal is an echo: the answer ignores the probe. -/
theorem eqwEpisode_echo_on_diagonal (a : W) :
    EchoAt (eqwEpisode W) (a, a) := by
  intro o o'
  simp [eqwEpisode]

/-- Every off-diagonal state is exogenous: the answer tracks the probe. -/
theorem eqwEpisode_informative_off_diagonal {a b : W} (hab : a ≠ b) :
    InformativeAt (eqwEpisode W) (a, b) := by
  refine ⟨false, true, ?_⟩
  simp [eqwEpisode, hab]

/-- The licensed surface is distinction-sound. -/
theorem eqwEpisode_licensedSound : LicensedSound (eqwEpisode W) := by
  rintro ⟨a, b⟩ r (hr | ⟨hab, hr⟩) hn
  · subst hr; exact absurd hn (by simp [eqwEpisode, Rec.nonnull])
  · exact hab

/-- The target distinction is object-witnessed. -/
theorem eqwEpisode_objectWitnessed : ObjectWitnessed (eqwEpisode W) := by
  rintro ⟨a, b⟩ hab
  exact eqwEpisode_informative_off_diagonal hab

/-- The null record is null. -/
theorem eqwEpisode_null_is_null :
    ¬ (eqwEpisode W).nonnull (eqwEpisode W).null := by
  simp [eqwEpisode, Rec.nonnull]

/-- The raw surface emits the null record on the diagonal. -/
theorem eqwEpisode_raw_null (a : W) :
    (eqwEpisode W).rawEmits (a, a) (eqwEpisode W).null :=
  Or.inl rfl

/-- The raw surface also manufactures a non-null record on the diagonal: the
totalized difference rule fires against a zero-distinction input. -/
theorem eqwEpisode_raw_manufactures (a : W) :
    ∃ r, (eqwEpisode W).rawEmits (a, a) r ∧ (eqwEpisode W).nonnull r :=
  ⟨Rec.diff a a, Or.inr rfl, trivial⟩

/-- **The law fires.** The diagonal carries false formal legitimacy. -/
theorem eqwEpisode_ffl_on_diagonal (a : W) :
    FalseFormalLegitimacyAt (eqwEpisode W) (a, a) :=
  ffl_of_raw_nonnull_at_echo eqwEpisode_licensedSound eqwEpisode_objectWitnessed
    (eqwEpisode_echo_on_diagonal a) (eqwEpisode_raw_manufactures a)

/-- **The rewrite face fires.** The emission graph loses confluence at the
diagonal source. -/
theorem eqwEpisode_fork_on_diagonal (a : W) :
    ¬ OperatorKO7.Meta.DistinctionBoundary.Quantitative.ConfluentAt
        (RawEmitStep (eqwEpisode W)) (EmitNode.state (a, a)) :=
  ffl_not_confluentAt_source eqwEpisode_null_is_null
    (eqwEpisode_raw_null a) (eqwEpisode_ffl_on_diagonal a)

/-- **The licensed surface stays silent.** No licensed non-null record exists on
the diagonal, which is what makes the raw emission unwarranted. -/
theorem eqwEpisode_no_licensed_record_on_diagonal (a : W) :
    ¬ ∃ r, (eqwEpisode W).licensedEmits (a, a) r ∧ (eqwEpisode W).nonnull r :=
  no_licensed_nonnull_at_echo eqwEpisode_licensedSound eqwEpisode_objectWitnessed
    (eqwEpisode_echo_on_diagonal a)

/-! ## The execution face on the same episode -/

/-- An echo run on the comparator episode: a counter beside a fixed state. -/
def eqwEchoDynamics (W : Type) [DecidableEq W] : EchoDynamics (eqwEpisode W) where
  Trace := Nat × (W × W)
  mass := Prod.fst
  stateOf := Prod.snd
  step := fun t => (t.1 + 1, t.2)
  mass_grows := fun _ => rfl
  state_fixed := fun _ => rfl

/-- **Activity without progress on the witness.** The run grows the record by
exactly its depth while the compared pair never moves, and no depth licenses a
record. -/
theorem eqwEpisode_trap (a : W) (n : Nat) :
    (eqwEchoDynamics W).mass (run (eqwEchoDynamics W) (0, (a, a)) n) = n
      ∧ (eqwEchoDynamics W).stateOf (run (eqwEchoDynamics W) (0, (a, a)) n) = (a, a)
      ∧ ¬ ∃ r, (eqwEpisode W).licensedEmits
            ((eqwEchoDynamics W).stateOf (run (eqwEchoDynamics W) (0, (a, a)) n)) r
          ∧ (eqwEpisode W).nonnull r := by
  refine ⟨?_, run_state (eqwEchoDynamics W) (0, (a, a)) n, ?_⟩
  · have h := run_mass (eqwEchoDynamics W) (0, (a, a)) n
    simpa [eqwEchoDynamics] using h
  exact no_licensed_nonnull_at_any_run_depth eqwEpisode_licensedSound
    eqwEpisode_objectWitnessed (eqwEchoDynamics W) (0, (a, a))
    (eqwEpisode_echo_on_diagonal a) n

/-- **Non-vacuity receipt.** The comparator episode inhabits both hypotheses,
exhibits an echo state, exhibits an exogenous state, and realizes false formal
legitimacy together with the emission fork at the diagonal. -/
theorem eqwEpisode_nonvacuous (a b : W) (hab : a ≠ b) :
    LicensedSound (eqwEpisode W)
      ∧ ObjectWitnessed (eqwEpisode W)
      ∧ EchoAt (eqwEpisode W) (a, a)
      ∧ InformativeAt (eqwEpisode W) (a, b)
      ∧ FalseFormalLegitimacyAt (eqwEpisode W) (a, a)
      ∧ ¬ OperatorKO7.Meta.DistinctionBoundary.Quantitative.ConfluentAt
          (RawEmitStep (eqwEpisode W)) (EmitNode.state (a, a)) :=
  ⟨eqwEpisode_licensedSound, eqwEpisode_objectWitnessed,
    eqwEpisode_echo_on_diagonal a, eqwEpisode_informative_off_diagonal hab,
    eqwEpisode_ffl_on_diagonal a, eqwEpisode_fork_on_diagonal a⟩

end OperatorKO7.Meta.BoundaryGeneral.EchoLawInstance
