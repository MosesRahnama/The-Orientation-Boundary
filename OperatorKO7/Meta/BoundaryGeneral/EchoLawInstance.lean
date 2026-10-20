import OperatorKO7.Meta.BoundaryGeneral.EchoForkTrapCrown

/-!
# Concrete equality-comparator episode

`eqwEpisode W` uses pair states with Boolean objects and answers. At diagonal states, the answer is constant; at off-diagonal states, the answer reads the object probe. The raw emission relation includes both the null and difference cases without a diagonal guard, while the licensed relation permits the difference record only for distinct inputs.

The theorems establish `LicensedSound` and `ObjectWitnessed`, echo at diagonal states, and informative channels at off-diagonal states. A raw non-null diagonal emission gives `FalseFormalLegitimacyAt` and a nonconfluent emission graph. Runs from a diagonal state add one unit per step, keep the pair fixed, and produce no licensed non-null record. A separate theorem assumes a pair of distinct values and establishes the combined conclusions on both diagonal and off-diagonal states.

This is an abstract comparator model of two equality cases, not a description of the KO7 kernel. Trust: Mathlib baseline; no `sorry`, `admit`, or `axiom` occurs in this module.
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

/-- The episode satisfies `ObjectWitnessed`: every target distinction makes the answer informative. -/
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

/-- The raw relation also emits `diff a a` on a diagonal pair. -/
theorem eqwEpisode_raw_manufactures (a : W) :
    ∃ r, (eqwEpisode W).rawEmits (a, a) r ∧ (eqwEpisode W).nonnull r :=
  ⟨Rec.diff a a, Or.inr rfl, trivial⟩

/-- The diagonal satisfies `FalseFormalLegitimacyAt`. -/
theorem eqwEpisode_ffl_on_diagonal (a : W) :
    FalseFormalLegitimacyAt (eqwEpisode W) (a, a) :=
  ffl_of_raw_nonnull_at_echo eqwEpisode_licensedSound eqwEpisode_objectWitnessed
    (eqwEpisode_echo_on_diagonal a) (eqwEpisode_raw_manufactures a)

/-- The raw emission graph is not confluent at the diagonal source. -/
theorem eqwEpisode_fork_on_diagonal (a : W) :
    ¬ OperatorKO7.Meta.DistinctionBoundary.Quantitative.ConfluentAt
        (RawEmitStep (eqwEpisode W)) (EmitNode.state (a, a)) :=
  ffl_not_confluentAt_source eqwEpisode_null_is_null
    (eqwEpisode_raw_null a) (eqwEpisode_ffl_on_diagonal a)

/-- No licensed non-null record is emitted on the diagonal. -/
theorem eqwEpisode_no_licensed_record_on_diagonal (a : W) :
    ¬ ∃ r, (eqwEpisode W).licensedEmits (a, a) r ∧ (eqwEpisode W).nonnull r :=
  no_licensed_nonnull_at_echo eqwEpisode_licensedSound eqwEpisode_objectWitnessed
    (eqwEpisode_echo_on_diagonal a)

/-! ## Dynamics on the same episode -/

/-- An echo run stores record mass beside a fixed pair state. -/
def eqwEchoDynamics (W : Type) [DecidableEq W] : EchoDynamics (eqwEpisode W) where
  Trace := Nat × (W × W)
  mass := Prod.fst
  stateOf := Prod.snd
  step := fun t => (t.1 + 1, t.2)
  mass_grows := fun _ => rfl
  state_fixed := fun _ => rfl

/-- A run from `(a, a)` has mass `n`, keeps the pair fixed, and has no licensed non-null record at any depth. -/
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

/-- Given `a ≠ b`, the episode satisfies both hypotheses, is echo at `(a, a)` and informative at `(a, b)`, and has false formal legitimacy and graph nonconfluence at `(a, a)`. -/
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
