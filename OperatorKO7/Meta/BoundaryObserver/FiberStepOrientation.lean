import OperatorKO7.Meta.BoundaryObserver.RecursorDecidability
import OperatorKO7.Meta.InformationalIncompleteness.SharpnessCounterexample

set_option autoImplicit false

/-!
# A step inside a fiber defeats every record-determined measure

`lem:fiber-step` of the Observation-Boundary Principle (ledger row 09-038). For an observer
`q : X → Q` and a relation `R` on `X`, a measure determined by `q` takes one value at the two ends of
an `R`-step that stays inside a fiber of `q`, so it cannot fall there into a strict order. The exact
form: a measure determined by `q` with values in a well-founded order orients `R` if and only if the
record image of `R` (the relation between the records of the two ends of a step) is well founded.

The two mirror instances of the lemma: every counted pass stays inside a fiber of the content
observer, so no content-determined measure orients the passes (clause (ii) of
`thm:recursor-decidability`); the payload-lowering step on counter-payload pairs stays inside a
fiber of the counter, so no counter-determined measure orients it while the payload projection
does (`SharpnessCounterexample.payloadErasure_hypothesis_necessary`).

Relation: an arbitrary relation `R`; `RecursorDecidability.Pass`; the root step of
`SharpnessCounterexample.payloadDecreasingStep`. Trust: kernel-only. No `sorry`, `admit`,
`axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.FiberStepOrientation

open OperatorKO7.Meta.BoundaryObserver.MergedPair

universe u v w

/-- A measure `M` orients `R` into the order `lt` when it falls at every step: `R x x'` gives
`lt (M x') (M x)`. -/
def Orients {X : Type u} {A : Type w} (R : X → X → Prop) (M : X → A) (lt : A → A → Prop) :
    Prop :=
  ∀ x x', R x x' → lt (M x') (M x)

/-- Unfolding lemma of `Orients`. -/
theorem orients_iff {X : Type u} {A : Type w} (R : X → X → Prop) (M : X → A)
    (lt : A → A → Prop) : Orients R M lt ↔ ∀ x x', R x x' → lt (M x') (M x) := Iff.rfl

/-- The record image of `R` under `q`, in descent form: `recordImage q R r' r` holds when some
`R`-step leads from a state with record `r` to a state with record `r'`. -/
def recordImage {X : Type u} {Q : Type v} (q : X → Q) (R : X → X → Prop) : Q → Q → Prop :=
  fun r' r => ∃ x x', R x x' ∧ q x = r ∧ q x' = r'

/-- Unfolding lemma of `recordImage`. -/
theorem recordImage_iff {X : Type u} {Q : Type v} (q : X → Q) (R : X → X → Prop) (r' r : Q) :
    recordImage q R r' r ↔ ∃ x x', R x x' ∧ q x = r ∧ q x' = r' := Iff.rfl

/--
`lem:fiber-step`.

Proves: if `q` determines `M`, `lt` is irreflexive, and the `R`-step from `x` to `x'` has
`q x = q x'`, then `M` does not fall at that step.
Relation: an arbitrary relation `R`, one step. Trust: kernel-only.
-/
theorem fiberStep_not_falls {X : Type u} {Q : Type v} {A : Type w} (q : X → Q) (M : X → A)
    (lt : A → A → Prop) (hirr : ∀ a, ¬ lt a a) (hdet : Determines q M)
    {R : X → X → Prop} {x x' : X} (_hstep : R x x') (hfib : q x = q x') :
    ¬ lt (M x') (M x) := by
  intro h
  rw [hdet x x' hfib] at h
  exact hirr _ h

/--
`lem:fiber-step`, second sentence.

Proves: a measure determined by `q` that orients `R` into an irreflexive order leaves every
`R`-step outside the fibers of `q`: `R x x'` gives `q x ≠ q x'`.
Relation: an arbitrary relation `R`. Trust: kernel-only.
-/
theorem orients_no_fiberStep {X : Type u} {Q : Type v} {A : Type w} (q : X → Q) (M : X → A)
    (lt : A → A → Prop) (hirr : ∀ a, ¬ lt a a) (hdet : Determines q M)
    {R : X → X → Prop} (hor : Orients R M lt) :
    ∀ x x', R x x' → q x ≠ q x' :=
  fun x x' hstep hfib => fiberStep_not_falls q M lt hirr hdet hstep hfib (hor x x' hstep)

/-- The composite `m ∘ q` is determined by `q`. -/
theorem determines_comp {X : Type u} {Q : Type v} {A : Type w} (q : X → Q) (m : Q → A) :
    Determines q (m ∘ q) := by
  intro x y h
  simp only [Function.comp_apply, h]

/--
Proves: if a measure determined by `q` orients `R` into a well-founded order, the record image of
`R` under `q` is well founded.
Relation: an arbitrary relation `R`. Trust: kernel-only.
-/
theorem recordImage_wellFounded_of_orients {X : Type u} {Q : Type v} {A : Type w} (q : X → Q)
    (M : X → A) (lt : A → A → Prop) (hwf : WellFounded lt) (hdet : Determines q M)
    {R : X → X → Prop} (hor : Orients R M lt) : WellFounded (recordImage q R) := by
  have key : ∀ a : A, ∀ r : Q, (∀ x, q x = r → M x = a) → Acc (recordImage q R) r := by
    intro a
    induction a using hwf.induction with
    | _ a ih =>
      intro r hr
      constructor
      intro r' hr'
      obtain ⟨x, x', hstep, hx, hx'⟩ := hr'
      have hlt : lt (M x') a := by
        rw [← hr x hx]
        exact hor x x' hstep
      apply ih (M x') hlt r'
      intro y hy
      exact hdet y x' (hy.trans hx'.symm)
  constructor
  intro r
  by_cases hex : ∃ x, q x = r
  · obtain ⟨x0, hx0⟩ := hex
    exact key (M x0) r (fun x hx => hdet x x0 (hx.trans hx0.symm))
  · constructor
    intro r' hr'
    obtain ⟨x, _, _, hx, _⟩ := hr'
    exact absurd ⟨x, hx⟩ hex

/--
Proves: the record itself orients `R` into the record image of `R`; with a well-founded record
image this is an orienting measure determined by `q`.
Trust: kernel-only.
-/
theorem record_orients_recordImage {X : Type u} {Q : Type v} (q : X → Q) (R : X → X → Prop) :
    Orients R q (recordImage q R) :=
  fun x x' hstep => ⟨x, x', hstep, rfl, rfl⟩

/--
`lem:fiber-step`, exact form.

Proves: some measure determined by `q`, with values in a well-founded order on a type of the
universe of `Q`, orients `R` if and only if the record image of `R` under `q` is well founded.
Relation: an arbitrary relation `R`. Trust: kernel-only.
-/
theorem exists_determined_orienting_iff {X : Type u} {Q : Type v} (q : X → Q)
    (R : X → X → Prop) :
    (∃ (A : Type v) (lt : A → A → Prop) (M : X → A),
        WellFounded lt ∧ Determines q M ∧ Orients R M lt) ↔
      WellFounded (recordImage q R) := by
  constructor
  · rintro ⟨A, lt, M, hwf, hdet, hor⟩
    exact recordImage_wellFounded_of_orients q M lt hwf hdet hor
  · intro hwf
    exact ⟨Q, recordImage q R, q, hwf, fun _ _ h => h, record_orients_recordImage q R⟩

/--
Proves: an `R`-step inside a fiber of `q` makes the record image of `R` fail to be well founded,
so no measure determined by `q` into a well-founded order orients `R`.
Trust: kernel-only.
-/
theorem not_wellFounded_recordImage_of_fiberStep {X : Type u} {Q : Type v} (q : X → Q)
    {R : X → X → Prop} {x x' : X} (hstep : R x x') (hfib : q x = q x') :
    ¬ WellFounded (recordImage q R) := by
  intro hwf
  have hloop : recordImage q R (q x) (q x) := ⟨x, x', hstep, rfl, hfib.symm⟩
  have hirr : ∀ r : Q, Acc (recordImage q R) r → ¬ recordImage q R r r := by
    intro r hr
    induction hr with
    | intro r _ ih => exact fun h => ih r h h
  exact hirr (q x) (hwf.apply (q x)) hloop

/-! ## The counted passes: every pass stays inside a content fiber -/

open OperatorKO7.Meta.BoundaryObserver.RecursorDecidability in
/--
`thm:recursor-decidability` (ii) as an instance of `lem:fiber-step`.

Proves: on `T × ℕ` with nonempty `T`, no measure determined by the content observer orients the
counted passes into a strict order; the counter orients them into `<`.
Relation: `RecursorDecidability.Pass`. Trust: kernel-only.
-/
theorem countedPass_instance {T : Type u} [Nonempty T] {A : Type w} (M : T × ℕ → A)
    (lt : A → A → Prop) (hirr : ∀ a, ¬ lt a a) (hdet : Determines content M) :
    ¬ Orients Pass M lt ∧ Orients (X := T × ℕ) Pass counter (· < ·) := by
  refine ⟨?_, fun x x' h => counter_orients x x' h⟩
  intro hor
  obtain ⟨t⟩ := ‹Nonempty T›
  have hpass : Pass (t, 1) (t, 0) := pass_of_step (t, 0)
  exact orients_no_fiberStep content M lt hirr hdet hor (t, 1) (t, 0) hpass rfl

/-! ## The payload step: it stays inside a counter fiber -/

/-- The root step of `SharpnessCounterexample.payloadDecreasingStep` as a relation on
counter-payload pairs `(counter, payload)`: `(n, s + 1)` steps to `(n, s)`. -/
def payloadStep : ℕ × ℕ → ℕ × ℕ → Prop :=
  fun x x' => ∃ s n : ℕ,
    x = OperatorKO7.Meta.InformationalIncompleteness.SharpnessCounterexample.payloadDecreasingStep.lhs
        () s n ∧
    x' = OperatorKO7.Meta.InformationalIncompleteness.SharpnessCounterexample.payloadDecreasingStep.rhs
        () s n

/-- Unfolding lemma of `payloadStep` at the explicit pairs. -/
theorem payloadStep_iff (x x' : ℕ × ℕ) :
    payloadStep x x' ↔ ∃ s n : ℕ, x = (n, s + 1) ∧ x' = (n, s) := Iff.rfl

/--
The mirror instance of `lem:fiber-step`.

Proves: no measure determined by the counter `Prod.fst` orients `payloadStep` into a strict order,
while the payload projection `Prod.snd` orients it into `<`.
Relation: the root step of `SharpnessCounterexample.payloadDecreasingStep`. Trust: kernel-only.
-/
theorem payloadStep_instance {A : Type w} (M : ℕ × ℕ → A) (lt : A → A → Prop)
    (hirr : ∀ a, ¬ lt a a) (hdet : Determines Prod.fst M) :
    ¬ Orients payloadStep M lt ∧ Orients payloadStep Prod.snd (· < ·) := by
  refine ⟨?_, ?_⟩
  · intro hor
    have hstep : payloadStep (0, 1) (0, 0) := ⟨0, 0, rfl, rfl⟩
    exact orients_no_fiberStep Prod.fst M lt hirr hdet hor (0, 1) (0, 0) hstep rfl
  · rintro x x' ⟨s, n, rfl, rfl⟩
    exact Nat.lt_succ_self s

/--
The two mirror instances together with the sharpness theorem they mirror.

Proves: the content observer blocks every orienting measure of the counted passes, the counter
blocks every orienting measure of the payload step, and the payload-erasure hypothesis of the
counter-domination theorem is necessary (`payloadErasure_hypothesis_necessary`).
Trust: kernel-only.
-/
theorem fiberStep_mirror_instances :
    (∀ (A : Type) (M : Unit × ℕ → A) (lt : A → A → Prop), (∀ a, ¬ lt a a) →
        Determines RecursorDecidability.content M →
        ¬ Orients RecursorDecidability.Pass M lt) ∧
      (∀ (A : Type) (M : ℕ × ℕ → A) (lt : A → A → Prop), (∀ a, ¬ lt a a) →
        Determines Prod.fst M → ¬ Orients payloadStep M lt) ∧
      (∃ (R : OperatorKO7.RDRSDescentLens.RDRSStep Unit ℕ ℕ (ℕ × ℕ))
          (M : OperatorKO7.RDRSSemanticDirectMeasure.SemanticMeasureData (ℕ × ℕ)),
        OperatorKO7.RDRSDescentLens.Orients R M.μ M.ltA ∧
          ¬ OperatorKO7.RDRSSemanticPayloadSensitivity.CounterDominated R M) :=
  ⟨fun _A M lt hirr hdet => (countedPass_instance M lt hirr hdet).1,
    fun _A M lt hirr hdet => (payloadStep_instance M lt hirr hdet).1,
    OperatorKO7.Meta.InformationalIncompleteness.SharpnessCounterexample.payloadErasure_hypothesis_necessary⟩

/-- Non-vacuity: the identity order `<` on `ℕ` is irreflexive, and the counter is an orienting
measure of the passes determined by itself, so the hypotheses of the lemma are inhabited. -/
example : Orients (RecursorDecidability.Pass (T := Unit)) RecursorDecidability.counter (· < ·) ∧
    (∀ a : ℕ, ¬ a < a) :=
  ⟨fun x x' h => RecursorDecidability.counter_orients x x' h, fun a => Nat.lt_irrefl a⟩

end OperatorKO7.Meta.BoundaryObserver.FiberStepOrientation
