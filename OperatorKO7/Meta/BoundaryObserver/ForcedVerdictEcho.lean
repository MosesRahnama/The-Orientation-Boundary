import OperatorKO7.Meta.BoundaryGeneral.EchoLaw
import OperatorKO7.Meta.SchemaWitnessOrder

/-!
# The forced-output setting as an emission episode on a certificate tower

Manuscript: the forced-output paragraph after Theorem `thm:echo-law` of the
Observation-Boundary Principle.

An agent asked for the termination verdict at the direct interface emits a definite verdict
(`some b`) or the typed refusal (`none`). On a certificate tower `Tw` of a step-duplicating schema,
the emission episode licenses a definite verdict at an instance exactly when the instance has a
direct whole-term certificate, emits any record raw, and reads the direct certificate through its
channel. Then a licensed definite verdict needs a direct-level certificate, the echo states of the
channel are exactly the orientation-boundary states, at those states every licensed record is the
refusal and every raw definite verdict is a state of false formal legitimacy, and every output is
one of the three forced cases.
-/

set_option autoImplicit false

open OperatorKO7.Meta.BoundaryGeneral.EchoLaw
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.SchemaWitnessTower

namespace OperatorKO7.Meta.BoundaryObserver.ForcedVerdictEcho

variable {S : StepDuplicatingSchema}

/-- The forced-output emission episode on the tower `Tw`: states are instances, records are
definite verdicts or the refusal, the target distinction is a direct whole-term certificate, and
the channel reads that certificate against a two-point object coordinate. -/
def forcedEpisode (Tw : SchemaWitnessTower S) : Episode where
  State := S.T
  Object := Bool
  Answer := Prop
  Record := Option Bool
  null := none
  nonnull r := r ≠ none
  answer x o := o = true ∧ HasWitness Tw x WLevel.directWhole
  Distinction x := HasWitness Tw x WLevel.directWhole
  rawEmits _ _ := True
  licensedEmits x r := r = none ∨ HasWitness Tw x WLevel.directWhole

theorem forced_licensedSound (Tw : SchemaWitnessTower S) : LicensedSound (forcedEpisode Tw) := by
  intro x r hlic hn
  rcases hlic with h | h
  · exact absurd h hn
  · exact h

theorem forced_objectWitnessed (Tw : SchemaWitnessTower S) :
    ObjectWitnessed (forcedEpisode Tw) := by
  intro x hd
  refine ⟨true, false, ?_⟩
  intro h
  have : (true = true ∧ HasWitness Tw x WLevel.directWhole) :=  ⟨rfl, hd⟩
  have h' : (false = true ∧ HasWitness Tw x WLevel.directWhole) := by
    change (true = true ∧ HasWitness Tw x WLevel.directWhole) =
      (false = true ∧ HasWitness Tw x WLevel.directWhole) at h
    exact h ▸ this
  exact Bool.false_ne_true h'.1

/-- **A licensed definite verdict needs a direct-level certificate.** -/
theorem licensed_verdict_needs_direct (Tw : SchemaWitnessTower S) (x : S.T) (b : Bool)
    (h : (forcedEpisode Tw).licensedEmits x (some b)) : HasWitness Tw x WLevel.directWhole :=
  forced_licensedSound Tw x (some b) h (by simp [forcedEpisode])

/-- **The echo states of the channel are exactly the orientation-boundary states.** -/
theorem echo_iff_orientationBoundary (Tw : SchemaWitnessTower S) (x : S.T) :
    EchoAt (forcedEpisode Tw) x ↔ OB Tw x := by
  rw [OB_iff_no_directWhole, echoAt_iff_not_informativeAt]
  constructor
  · intro hne hw
    exact hne (forced_objectWitnessed Tw x hw)
  · rintro hnw ⟨o, o', hoo⟩
    apply hoo
    change (o = true ∧ HasWitness Tw x WLevel.directWhole) =
      (o' = true ∧ HasWitness Tw x WLevel.directWhole)
    exact propext ⟨fun h => absurd h.2 hnw, fun h => absurd h.2 hnw⟩

/-- **At an orientation-boundary state every licensed record is the refusal.** -/
theorem licensed_null_at_boundary (Tw : SchemaWitnessTower S) (x : S.T) (hOB : OB Tw x)
    (r : Option Bool) (h : (forcedEpisode Tw).licensedEmits x r) : r = none := by
  by_contra hr
  exact no_licensed_nonnull_at_echo (forced_licensedSound Tw) (forced_objectWitnessed Tw)
    ((echo_iff_orientationBoundary Tw x).2 hOB) ⟨r, h, hr⟩

/-- **At an orientation-boundary state every raw definite verdict is a state of false formal
legitimacy.** -/
theorem raw_verdict_ffl_at_boundary (Tw : SchemaWitnessTower S) (x : S.T) (hOB : OB Tw x)
    (b : Bool) : FalseFormalLegitimacyAt (forcedEpisode Tw) x :=
  ffl_of_raw_nonnull_at_echo (forced_licensedSound Tw) (forced_objectWitnessed Tw)
    ((echo_iff_orientationBoundary Tw x).2 hOB) ⟨some b, trivial, by simp [forcedEpisode]⟩

/-- **The three forced cases exhaust the outputs:** every record emitted at an instance is a
licensed definite verdict backed by a direct-level certificate, the refusal, or a raw definite
verdict at a state with no direct-level certificate. -/
theorem forced_trichotomy (Tw : SchemaWitnessTower S) (x : S.T) (r : Option Bool) :
    (r ≠ none ∧ (forcedEpisode Tw).licensedEmits x r ∧ HasWitness Tw x WLevel.directWhole) ∨
      r = none ∨
      (r ≠ none ∧ ¬ (forcedEpisode Tw).licensedEmits x r ∧ OB Tw x) := by
  by_cases hr : r = none
  · exact Or.inr (Or.inl hr)
  · by_cases hw : HasWitness Tw x WLevel.directWhole
    · exact Or.inl ⟨hr, Or.inr hw, hw⟩
    · refine Or.inr (Or.inr ⟨hr, ?_, (OB_iff_no_directWhole Tw x).2 hw⟩)
      rintro (h | h)
      · exact hr h
      · exact hw h

end OperatorKO7.Meta.BoundaryObserver.ForcedVerdictEcho
