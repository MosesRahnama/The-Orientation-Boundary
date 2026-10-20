import OperatorKO7.Meta.BoundaryGeneral.EchoLawInstance

/-!
# Gated readout

A `GatedReadout` provides a reading function when the target distinction holds, a fixed answer otherwise, and two object probes with different readings.

For every episode with a gated readout, `ObjectWitnessed` follows from the separated readings, and `EchoAt` holds exactly outside the distinction region. Under `LicensedSound`, echo states have no licensed non-null records; every licensed non-null record implies a distinction and an informative channel.

The Boolean comparator has a gated readout. The condition is sufficient but not necessary: `flipEpisode` is `ObjectWitnessed` and has no `GatedReadout`, because its reading varies across states where the distinction holds.

Scope: the two-probe requirement excludes an object carrier whose reading cannot separate two values. Trust: kernel-only; no `sorry`, `admit`, `axiom`, or `native_decide` occurs in this module.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.ReadoutGate

open OperatorKO7.Meta.BoundaryGeneral.EchoLaw
open OperatorKO7.Meta.BoundaryGeneral.EchoLawInstance

variable {E : Episode}

/-! ## The class -/

/-- A **gated readout** on an episode. The channel has two branches selected by
the distinction predicate: a fixed reading of the object probe on the
distinction region, and one fixed answer off it. The reading separates two named
probes. -/
structure GatedReadout (E : Episode) where
  /-- The branch consulted where the distinction holds. -/
  reading : E.Object → E.Answer
  /-- The branch returned where the distinction fails. -/
  silence : E.Answer
  /-- On the distinction region the answer is the reading of the probe. -/
  reads : ∀ s, E.Distinction s → ∀ o, E.answer s o = reading o
  /-- Off the distinction region the answer is constant. -/
  silent : ∀ s, ¬ E.Distinction s → ∀ o, E.answer s o = silence
  /-- First named probe. -/
  probe₀ : E.Object
  /-- Second named probe. -/
  probe₁ : E.Object
  /-- The reading tells the two probes apart. -/
  separates : reading probe₀ ≠ reading probe₁

/-! ## Consequences -/

/-- A `GatedReadout` implies `ObjectWitnessed`: on a state with a distinction, the two separated probes have different answers. -/
theorem objectWitnessed_of_gatedReadout (G : GatedReadout E) : ObjectWitnessed E := by
  intro s hs
  refine ⟨G.probe₀, G.probe₁, ?_⟩
  rw [G.reads s hs G.probe₀, G.reads s hs G.probe₁]
  exact G.separates

/-- Off the distinction region the channel is an echo. -/
theorem echoAt_of_not_distinction (G : GatedReadout E) {s : E.State}
    (hs : ¬ E.Distinction s) : EchoAt E s := by
  intro o o'
  rw [G.silent s hs o, G.silent s hs o']

/-- Under a gated readout, echo holds exactly when the target distinction does not. -/
theorem echoAt_iff_not_distinction (G : GatedReadout E) (s : E.State) :
    EchoAt E s ↔ ¬ E.Distinction s := by
  constructor
  · intro hecho hs
    refine G.separates ?_
    rw [← G.reads s hs G.probe₀, ← G.reads s hs G.probe₁]
    exact hecho G.probe₀ G.probe₁
  · exact echoAt_of_not_distinction G

/-- The positive half of the same dichotomy. -/
theorem informativeAt_iff_distinction (G : GatedReadout E) (s : E.State) :
    InformativeAt E s ↔ E.Distinction s := by
  constructor
  · intro hinf
    refine Classical.byContradiction (fun hs => ?_)
    exact (echoAt_iff_not_informativeAt E s).mp (echoAt_of_not_distinction G hs) hinf
  · exact objectWitnessed_of_gatedReadout G s

/-! ## Echo law from a gated readout -/

/-- Under `LicensedSound` and `GatedReadout`, an echo state has no licensed non-null record. -/
theorem echo_law_of_gatedReadout (hsound : LicensedSound E) (G : GatedReadout E)
    {s : E.State} (hecho : EchoAt E s) :
    ¬ ∃ r, E.licensedEmits s r ∧ E.nonnull r :=
  no_licensed_nonnull_at_echo hsound (objectWitnessed_of_gatedReadout G) hecho

/-- Under `LicensedSound`, a gated readout excludes licensed non-null records outside the distinction region. -/
theorem no_licensed_nonnull_off_distinction (hsound : LicensedSound E)
    (G : GatedReadout E) {s : E.State} (hs : ¬ E.Distinction s) :
    ¬ ∃ r, E.licensedEmits s r ∧ E.nonnull r :=
  echo_law_of_gatedReadout hsound G (echoAt_of_not_distinction G hs)

/-- Every licensed non-null record requires a target distinction and an informative channel. -/
theorem licensed_nonnull_forces_distinction_and_reading (hsound : LicensedSound E)
    (G : GatedReadout E) {s : E.State} {r : E.Record}
    (hemit : E.licensedEmits s r) (hn : E.nonnull r) :
    E.Distinction s ∧ InformativeAt E s :=
  ⟨hsound s r hemit hn, objectWitnessed_of_gatedReadout G s (hsound s r hemit hn)⟩

/-! ## Comparator example -/

/-- The comparator episode has a gated readout for every `W` with decidable equality. Its Boolean reading separates the probes, so `W` need not be inhabited. -/
def eqwGatedReadout (W : Type) [DecidableEq W] : GatedReadout (eqwEpisode W) where
  reading := fun o => o
  silence := false
  reads := by
    intro s hs o
    have h : s.1 ≠ s.2 := hs
    show (if s.1 = s.2 then false else o) = o
    rw [if_neg h]
  silent := by
    intro s hs o
    have h : s.1 = s.2 := not_not.mp hs
    show (if s.1 = s.2 then false else o) = false
    rw [if_pos h]
  probe₀ := false
  probe₁ := true
  separates := Bool.false_ne_true

/-- The comparator episode satisfies `ObjectWitnessed` by the gated-readout theorem. -/
theorem eqwEpisode_objectWitnessed_derived (W : Type) [DecidableEq W] :
    ObjectWitnessed (eqwEpisode W) :=
  objectWitnessed_of_gatedReadout (eqwGatedReadout W)

/-- The dichotomy on the comparator episode: the echo region is the diagonal. -/
theorem eqwEpisode_echo_iff_diagonal (W : Type) [DecidableEq W] (p : W × W) :
    EchoAt (eqwEpisode W) p ↔ p.1 = p.2 := by
  rw [echoAt_iff_not_distinction (eqwGatedReadout W) p]
  exact not_not

/-! ## Limits of the condition -/

/-- An episode whose channel flips with the state. Every state carries the
distinction and every state is informative, while the reading branch varies
across states. -/
def flipEpisode : Episode where
  State := Bool
  Object := Bool
  Answer := Bool
  Record := Unit
  null := ()
  nonnull := fun _ => False
  answer := fun s o => if s then o else !o
  Distinction := fun _ => True
  rawEmits := fun _ _ => True
  licensedEmits := fun _ _ => True

/-- The flip episode satisfies `ObjectWitnessed`. -/
theorem flipEpisode_objectWitnessed : ObjectWitnessed flipEpisode := by
  intro s _
  refine ⟨false, true, ?_⟩
  cases s <;> simp [flipEpisode]

/-- `flipEpisode` is `ObjectWitnessed` but has no `GatedReadout`, because its reading changes across states where the distinction holds. -/
theorem objectWitnessed_without_gatedReadout :
    ObjectWitnessed flipEpisode ∧ IsEmpty (GatedReadout flipEpisode) := by
  refine ⟨flipEpisode_objectWitnessed, ⟨?_⟩⟩
  intro G
  have htrue : flipEpisode.answer true true = G.reading true :=
    G.reads true trivial true
  have hfalse : flipEpisode.answer false true = G.reading true :=
    G.reads false trivial true
  rw [← hfalse] at htrue
  simp [flipEpisode] at htrue

/-! ## Combined results -/

/-- The combined result gives the `ObjectWitnessed` implication, the echo/distinction equivalence, a gated comparator example, and an `ObjectWitnessed` episode without a gated readout. -/
theorem gated_readout_law :
    (∀ (F : Episode), GatedReadout F → ObjectWitnessed F) ∧
    (∀ (F : Episode), GatedReadout F → ∀ (s : F.State),
      EchoAt F s ↔ ¬ F.Distinction s) ∧
    Nonempty (GatedReadout (eqwEpisode Bool)) ∧
    ObjectWitnessed flipEpisode ∧
    IsEmpty (GatedReadout flipEpisode) :=
  ⟨fun _ G => objectWitnessed_of_gatedReadout G,
   fun _ G s => echoAt_iff_not_distinction G s,
   ⟨eqwGatedReadout Bool⟩,
   objectWitnessed_without_gatedReadout.1,
   objectWitnessed_without_gatedReadout.2⟩

end OperatorKO7.Meta.BoundaryGeneral.ReadoutGate
