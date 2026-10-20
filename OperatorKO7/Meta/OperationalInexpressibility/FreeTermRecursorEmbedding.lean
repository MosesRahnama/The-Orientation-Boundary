import OperatorKO7.Meta.Methods.OrientationClosure.AttainedPairs
import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorWitnessOrder

/-!
# The four-constructor free recursor inside the seven-constructor recursor syntax

The free recursor of the Orientation Boundary has two Lean term types: the
four-constructor syntax `SchemaCore.FreeTerm ν` with its root relation
`RootStep`, and the closed seven-constructor syntax `RecursorTerm` with its root
relation `FreeRecursorStep`. The map `toRecursorTerm` sends `zero` to `void`,
`succ` to `delta`, `wrap` to `app` and `recur` to `recR`. It is injective, it
keeps the counter and payload observations, it sends each instance of a root
rule to the instance of the same rule at the images, and every root step out of
an image term is the image of a root step. The root height of the
four-constructor syntax is defined by recursion at every variable type; it is
the pointwise least natural-valued ranking of both root rules, it does not
factor through the observed profile, and on closed terms it equals
`derivationHeight` of the image.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel

/-! ## The embedding -/

/--
Proves: nothing; this is the map from closed four-constructor free terms to
seven-constructor recursor terms: `zero` to `void`, `succ` to `delta`, `wrap` to
`app`, `recur` to `recR`.
Does not prove: any property of the map; the theorems below state injectivity,
the observation equations and the correspondence of root steps.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: definition only.
Scope: every closed term of `FreeTerm Empty`.
-/
def toRecursorTerm : FreeTerm Empty → RecursorTerm
  | .var x => x.elim
  | .zero => .void
  | .succ t => .delta (toRecursorTerm t)
  | .wrap s t => .app (toRecursorTerm s) (toRecursorTerm t)
  | .recur b s n => .recR (toRecursorTerm b) (toRecursorTerm s) (toRecursorTerm n)

/--
Proves: `toRecursorTerm` is injective.
Does not prove: surjectivity; terms headed by `integrate`, `merge` or `eqWit`
lie outside the image.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: Lean kernel; structural induction.
Scope: every pair of closed terms of `FreeTerm Empty`.
-/
theorem toRecursorTerm_injective : Function.Injective toRecursorTerm := by
  intro a
  induction a with
  | var x => exact x.elim
  | zero =>
      intro c h
      cases c with
      | var y => exact y.elim
      | zero => rfl
      | succ u => simp [toRecursorTerm] at h
      | wrap u v => simp [toRecursorTerm] at h
      | recur u v w => simp [toRecursorTerm] at h
  | succ t ih =>
      intro c h
      cases c with
      | var y => exact y.elim
      | zero => simp [toRecursorTerm] at h
      | succ u =>
          simp only [toRecursorTerm, RecursorTerm.delta.injEq] at h
          rw [ih h]
      | wrap u v => simp [toRecursorTerm] at h
      | recur u v w => simp [toRecursorTerm] at h
  | wrap s t ihs iht =>
      intro c h
      cases c with
      | var y => exact y.elim
      | zero => simp [toRecursorTerm] at h
      | succ u => simp [toRecursorTerm] at h
      | wrap u v =>
          simp only [toRecursorTerm, RecursorTerm.app.injEq] at h
          rw [ihs h.1, iht h.2]
      | recur u v w => simp [toRecursorTerm] at h
  | recur b s n ihb ihs ihn =>
      intro c h
      cases c with
      | var y => exact y.elim
      | zero => simp [toRecursorTerm] at h
      | succ u => simp [toRecursorTerm] at h
      | wrap u v => simp [toRecursorTerm] at h
      | recur u v w =>
          simp only [toRecursorTerm, RecursorTerm.recR.injEq] at h
          rw [ihb h.1, ihs h.2.1, ihn h.2.2]

/-! ## The observations -/

/--
Proves: the length of the leading `delta` prefix of the image equals the length
of the leading `succ` prefix of the closed free term.
Does not prove: anything about terms outside the image.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: Lean kernel; structural induction.
Scope: every closed term of `FreeTerm Empty`.
-/
theorem deltaPrefix_toRecursorTerm (t : FreeTerm Empty) :
    deltaPrefix (toRecursorTerm t) =
      OperatorKO7.Methods.OrientationClosure.AttainedPairs.succPrefix t := by
  induction t with
  | var x => exact x.elim
  | zero => rfl
  | succ t ih =>
      show deltaPrefix (toRecursorTerm t) + 1 =
        OperatorKO7.Methods.OrientationClosure.AttainedPairs.succPrefix t + 1
      rw [ih]
  | wrap s t _ _ => rfl
  | recur b s n _ _ _ => rfl

/--
Proves: the counter observation of `FreeRecursorWitnessOrder` on the image equals
the counter observation of `AttainedPairs` on the closed free term.
Does not prove: anything about terms outside the image.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: Lean kernel; structural induction.
Scope: every closed term of `FreeTerm Empty`.
-/
theorem counterObservation_toRecursorTerm (t : FreeTerm Empty) :
    FreeRecursorWitnessOrder.counterObservation (toRecursorTerm t) =
      OperatorKO7.Methods.OrientationClosure.AttainedPairs.counterObservation t := by
  induction t with
  | var x => exact x.elim
  | zero => rfl
  | succ t _ => rfl
  | wrap s t _ iht =>
      show FreeRecursorWitnessOrder.counterObservation (toRecursorTerm t) =
        OperatorKO7.Methods.OrientationClosure.AttainedPairs.counterObservation t
      exact iht
  | recur b s n ihb _ _ =>
      show deltaPrefix (toRecursorTerm n) +
          FreeRecursorWitnessOrder.counterObservation (toRecursorTerm b) =
        OperatorKO7.Methods.OrientationClosure.AttainedPairs.succPrefix n +
          OperatorKO7.Methods.OrientationClosure.AttainedPairs.counterObservation b
      rw [deltaPrefix_toRecursorTerm, ihb]

/--
Proves: the payload observation of `FreeRecursorWitnessOrder` on the image equals
the payload observation of `AttainedPairs` on the closed free term.
Does not prove: anything about terms outside the image.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: Lean kernel; structural induction.
Scope: every closed term of `FreeTerm Empty`.
-/
theorem payloadObservation_toRecursorTerm (t : FreeTerm Empty) :
    FreeRecursorWitnessOrder.payloadObservation (toRecursorTerm t) =
      OperatorKO7.Methods.OrientationClosure.AttainedPairs.payloadObservation t := by
  induction t with
  | var x => exact x.elim
  | zero => rfl
  | succ t _ => rfl
  | wrap s t ihs iht =>
      show FreeRecursorWitnessOrder.payloadObservation (toRecursorTerm s) +
          FreeRecursorWitnessOrder.payloadObservation (toRecursorTerm t) + 1 =
        OperatorKO7.Methods.OrientationClosure.AttainedPairs.payloadObservation s +
          OperatorKO7.Methods.OrientationClosure.AttainedPairs.payloadObservation t + 1
      rw [ihs, iht]
  | recur b s n ihb _ _ =>
      show FreeRecursorWitnessOrder.payloadObservation (toRecursorTerm b) =
        OperatorKO7.Methods.OrientationClosure.AttainedPairs.payloadObservation b
      exact ihb

/--
Proves: every profile measure takes the same value on a closed free term and on
its image, the profile of `FreeRecursorWitnessOrder` on the image and the profile
of `AttainedPairs` on the term.
Does not prove: anything about terms outside the image.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: Lean kernel; the two observation equations.
Scope: every `m : Nat → Nat → Nat` and every closed term of `FreeTerm Empty`.
-/
theorem profileMeasure_toRecursorTerm (m : Nat → Nat → Nat) (t : FreeTerm Empty) :
    FreeRecursorWitnessOrder.profileMeasure m (toRecursorTerm t) =
      OperatorKO7.Methods.OrientationClosure.AttainedPairs.profileMeasure m t := by
  unfold FreeRecursorWitnessOrder.profileMeasure
    OperatorKO7.Methods.OrientationClosure.AttainedPairs.profileMeasure
  rw [counterObservation_toRecursorTerm, payloadObservation_toRecursorTerm]

/-! ## The root steps -/

/--
Proves: the image of the successor-rule source `recur b s (succ n)` is the
successor-rule source `recR b' s' (delta n')` at the images, and the image of its
target `wrap s (recur b s n)` is the successor-rule target `app s' (recR b' s' n')`.
Does not prove: anything about the zero rule, which `toRecursorTerm_rootStep`
covers with the successor rule.
Relation: the successor rules of `RootStep` and of `FreeRecursorStep`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; definitional unfolding.
Scope: every closed `b s n`.
-/
theorem toRecursorTerm_successor_instance (b s n : FreeTerm Empty) :
    toRecursorTerm (.recur b s (.succ n)) =
        .recR (toRecursorTerm b) (toRecursorTerm s) (.delta (toRecursorTerm n)) ∧
      toRecursorTerm (.wrap s (.recur b s n)) =
        .app (toRecursorTerm s) (.recR (toRecursorTerm b) (toRecursorTerm s) (toRecursorTerm n)) :=
  ⟨rfl, rfl⟩

/--
Proves: the map sends each root step of the closed four-constructor syntax to a
root step of the seven-constructor syntax: the zero rule to `FreeRecursorStep.zero`
and the successor rule to `FreeRecursorStep.succ`.
Does not prove: the reverse direction, which `freeRecursorStep_from_image` states.
Relation: `RootStep` on `FreeTerm Empty` and `FreeRecursorStep` on `RecursorTerm`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; case analysis on the two root rules.
Scope: every closed root step.
-/
theorem toRecursorTerm_rootStep {a b : FreeTerm Empty} (h : RootStep a b) :
    FreeRecursorStep (toRecursorTerm a) (toRecursorTerm b) := by
  cases h with
  | recurZero b s => exact FreeRecursorStep.zero _ _
  | recurSucc b s n => exact FreeRecursorStep.succ _ _ _

/--
Proves: every root step of the seven-constructor syntax out of the image of a
closed free term is the image of a root step of that term.
Does not prove: anything about root steps out of terms outside the image.
Relation: `FreeRecursorStep` on `RecursorTerm` and `RootStep` on `FreeTerm Empty`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; case analysis on the source term and on the step.
Scope: every closed term of `FreeTerm Empty` and every `RecursorTerm` target.
-/
theorem freeRecursorStep_from_image {a : FreeTerm Empty} {c : RecursorTerm}
    (h : FreeRecursorStep (toRecursorTerm a) c) :
    ∃ b : FreeTerm Empty, RootStep a b ∧ toRecursorTerm b = c := by
  cases a with
  | var x => exact x.elim
  | zero =>
      change FreeRecursorStep .void c at h
      cases h
  | succ t =>
      change FreeRecursorStep (.delta (toRecursorTerm t)) c at h
      cases h
  | wrap s t =>
      change FreeRecursorStep (.app (toRecursorTerm s) (toRecursorTerm t)) c at h
      cases h
  | recur b s n =>
      cases n with
      | var x => exact x.elim
      | zero =>
          change FreeRecursorStep (.recR (toRecursorTerm b) (toRecursorTerm s) .void) c at h
          cases h
          exact ⟨b, RootStep.recurZero b s, rfl⟩
      | succ m =>
          change FreeRecursorStep
            (.recR (toRecursorTerm b) (toRecursorTerm s) (.delta (toRecursorTerm m))) c at h
          cases h
          exact ⟨.wrap s (.recur b s m), RootStep.recurSucc b s m, rfl⟩
      | wrap u v =>
          change FreeRecursorStep (.recR (toRecursorTerm b) (toRecursorTerm s)
            (.app (toRecursorTerm u) (toRecursorTerm v))) c at h
          cases h
      | recur u v w =>
          change FreeRecursorStep (.recR (toRecursorTerm b) (toRecursorTerm s)
            (.recR (toRecursorTerm u) (toRecursorTerm v) (toRecursorTerm w))) c at h
          cases h

/--
Proves: two closed free terms are related by `RootStep` if and only if their
images are related by `FreeRecursorStep`.
Does not prove: anything about terms outside the image.
Relation: `RootStep` on `FreeTerm Empty` and `FreeRecursorStep` on `RecursorTerm`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; `toRecursorTerm_rootStep`, `freeRecursorStep_from_image` and
injectivity.
Scope: every pair of closed terms of `FreeTerm Empty`.
-/
theorem rootStep_iff_freeRecursorStep {a b : FreeTerm Empty} :
    RootStep a b ↔ FreeRecursorStep (toRecursorTerm a) (toRecursorTerm b) := by
  constructor
  · exact toRecursorTerm_rootStep
  · intro h
    obtain ⟨b', hab', hb'⟩ := freeRecursorStep_from_image h
    rw [toRecursorTerm_injective hb'] at hab'
    exact hab'

/--
Proves: at every variable type `ν`, orientation of every successor root instance
of the seven-constructor syntax by the profile measure of `FreeRecursorWitnessOrder`
is equivalent to orientation of every successor root instance of `FreeTerm ν` by
the profile measure of `AttainedPairs`; both are the numeric condition
`OrientsDupStep m`.
Does not prove: anything about measures that do not factor through the observed
profile.
Relation: the successor rules of `FreeRecursorStep` and of `RootStep`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with the axioms of the two `profile_orients_successors_iff`
theorems.
Scope: every `ν : Type` and every `m : Nat → Nat → Nat`.
-/
theorem successor_orientation_iff_across_term_types {ν : Type} (m : Nat → Nat → Nat) :
    (∀ b s n : RecursorTerm,
      FreeRecursorWitnessOrder.profileMeasure m (.app s (.recR b s n)) <
        FreeRecursorWitnessOrder.profileMeasure m (.recR b s (.delta n))) ↔
    (∀ b s n : FreeTerm ν,
      OperatorKO7.Methods.OrientationClosure.AttainedPairs.profileMeasure m
          (.wrap s (.recur b s n)) <
        OperatorKO7.Methods.OrientationClosure.AttainedPairs.profileMeasure m
          (.recur b s (.succ n))) :=
  (FreeRecursorWitnessOrder.profile_orients_successors_iff m).trans
    (OperatorKO7.Methods.OrientationClosure.AttainedPairs.profile_orients_successors_iff m).symm

/-! ## The least root height on the four-constructor syntax -/

/--
Proves: nothing; this is the executable root height of a free term: one more
than the height of the base for `recur b s zero`, one for `recur b s (succ n)`
(the successor rule emits a wrapper, which is root-normal), and zero at every
other term.
Does not prove: the ranking and leastness properties, which the theorems below
state.
Relation: `RootStep` on `FreeTerm ν`.
Closure: root rewriting.
Strategy: not applicable.
Trust: definition only.
Scope: every `ν : Type`.
-/
def freeRootHeight {ν : Type} : FreeTerm ν → Nat
  | .recur b _ .zero => freeRootHeight b + 1
  | .recur _ _ (.succ _) => 1
  | _ => 0

/--
Proves: the defining equation of the root height at the zero rule source.
Does not prove: anything at other terms.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: Lean kernel; definitional unfolding.
Scope: every `ν : Type` and every `b s : FreeTerm ν`.
-/
theorem freeRootHeight_recurZero {ν : Type} (b s : FreeTerm ν) :
    freeRootHeight (.recur b s .zero) = freeRootHeight b + 1 := rfl

/--
Proves: the defining equation of the root height at the successor rule source.
Does not prove: anything at other terms.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: Lean kernel; definitional unfolding.
Scope: every `ν : Type` and every `b s n : FreeTerm ν`.
-/
theorem freeRootHeight_recurSucc {ν : Type} (b s n : FreeTerm ν) :
    freeRootHeight (.recur b s (.succ n)) = 1 := rfl

/--
Proves: every root step lowers the root height by exactly one.
Does not prove: anything about contextual steps.
Relation: `RootStep` on `FreeTerm ν`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; case analysis on the two root rules.
Scope: every `ν : Type` and every root step.
-/
theorem freeRootHeight_step {ν : Type} {a b : FreeTerm ν} (h : RootStep a b) :
    freeRootHeight a = freeRootHeight b + 1 := by
  cases h with
  | recurZero b s => rfl
  | recurSucc b s n => rfl

/--
Proves: the root height is a natural-valued ranking of both root rules: it
strictly decreases along every root step.
Does not prove: decrease along contextual steps.
Relation: `RootStep` on `FreeTerm ν`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; `freeRootHeight_step`.
Scope: every `ν : Type` and every root step.
-/
theorem freeRootHeight_decreases {ν : Type} {a b : FreeTerm ν} (h : RootStep a b) :
    freeRootHeight b < freeRootHeight a := by
  rw [freeRootHeight_step h]
  exact Nat.lt_succ_self _

/--
Proves: the root height of a term is zero if and only if no root step leaves it.
Does not prove: anything about contextual normal forms.
Relation: `RootStep` on `FreeTerm ν`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; case analysis on the term.
Scope: every `ν : Type` and every `t : FreeTerm ν`.
-/
theorem freeRootHeight_eq_zero_iff {ν : Type} (t : FreeTerm ν) :
    freeRootHeight t = 0 ↔ ∀ u : FreeTerm ν, ¬ RootStep t u := by
  cases t with
  | var x =>
      exact ⟨fun _ u hu => (by cases hu), fun _ => rfl⟩
  | zero =>
      exact ⟨fun _ u hu => (by cases hu), fun _ => rfl⟩
  | succ t =>
      exact ⟨fun _ u hu => (by cases hu), fun _ => rfl⟩
  | wrap s t =>
      exact ⟨fun _ u hu => (by cases hu), fun _ => rfl⟩
  | recur b s n =>
      cases n with
      | var x =>
          exact ⟨fun _ u hu => (by cases hu), fun _ => rfl⟩
      | zero =>
          refine ⟨fun h0 => absurd h0 (Nat.succ_ne_zero _), fun h => ?_⟩
          exact absurd (RootStep.recurZero b s) (h b)
      | succ m =>
          refine ⟨fun h0 => absurd h0 Nat.one_ne_zero, fun h => ?_⟩
          exact absurd (RootStep.recurSucc b s m) (h _)
      | wrap u v =>
          exact ⟨fun _ w hw => (by cases hw), fun _ => rfl⟩
      | recur u v w =>
          exact ⟨fun _ x hx => (by cases hx), fun _ => rfl⟩

/--
Proves: the root height is the pointwise least natural-valued ranking of both root
rules: every `r : FreeTerm ν → Nat` that strictly decreases along every root step
bounds the root height from above at every term.
Does not prove: anything about rankings of the contextual relation.
Relation: `RootStep` on `FreeTerm ν`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; structural induction on the term.
Scope: every `ν : Type`, every ranking `r` and every `t : FreeTerm ν`.
-/
theorem freeRootHeight_pointwise_least {ν : Type} (r : FreeTerm ν → Nat)
    (hr : ∀ {a b : FreeTerm ν}, RootStep a b → r b < r a) (t : FreeTerm ν) :
    freeRootHeight t ≤ r t := by
  induction t with
  | var x => exact Nat.zero_le _
  | zero => exact Nat.zero_le _
  | succ t _ => exact Nat.zero_le _
  | wrap s t _ _ => exact Nat.zero_le _
  | recur b s n ihb _ _ =>
      cases n with
      | var x => exact Nat.zero_le _
      | zero =>
          have hd := hr (RootStep.recurZero b s)
          show freeRootHeight b + 1 ≤ r (.recur b s .zero)
          omega
      | succ m =>
          have hd := hr (RootStep.recurSucc b s m)
          show 1 ≤ r (.recur b s (.succ m))
          omega
      | wrap u v => exact Nat.zero_le _
      | recur u v w => exact Nat.zero_le _

/--
Proves: the root height does not factor through the observed profile: no
`m : Nat → Nat → Nat` gives `freeRootHeight t = m (c t) (p t)` at every term.
The terms `zero` and `recur zero zero zero` share the profile `(0, 0)` and have
heights zero and one.
Does not prove: anything about other observations.
Relation: `RootStep` on `FreeTerm ν`, through the height.
Closure: root rewriting.
Strategy: not applicable.
Trust: Lean kernel; two evaluations.
Scope: every `ν : Type`.
-/
theorem freeRootHeight_not_profile_factored {ν : Type} :
    ¬ ∃ m : Nat → Nat → Nat, ∀ t : FreeTerm ν,
      freeRootHeight t =
        OperatorKO7.Methods.OrientationClosure.AttainedPairs.profileMeasure m t := by
  rintro ⟨m, hm⟩
  have h0 : (0 : Nat) = m 0 0 := hm .zero
  have h1 : (1 : Nat) = m 0 0 := hm (.recur .zero .zero .zero)
  omega

/--
Proves: on closed terms the root height equals `derivationHeight` of the image,
the executable root height of the seven-constructor syntax.
Does not prove: anything about terms outside the image.
Relation: `RootStep` on `FreeTerm Empty` and `FreeRecursorStep` on `RecursorTerm`,
through their heights.
Closure: root rewriting.
Strategy: not applicable.
Trust: Lean kernel; structural induction with the two height equations of
`FreeRecursorWitnessOrder`.
Scope: every closed term of `FreeTerm Empty`.
-/
theorem derivationHeight_toRecursorTerm (t : FreeTerm Empty) :
    FreeRecursorWitnessOrder.derivationHeight (toRecursorTerm t) = freeRootHeight t := by
  induction t with
  | var x => exact x.elim
  | zero => exact rootMachine.cost_terminal rfl
  | succ t _ => exact rootMachine.cost_terminal rfl
  | wrap s t _ _ => exact rootMachine.cost_terminal rfl
  | recur b s n ihb _ _ =>
      cases n with
      | var x => exact x.elim
      | zero =>
          show FreeRecursorWitnessOrder.derivationHeight
              (.recR (toRecursorTerm b) (toRecursorTerm s) .void) = freeRootHeight b + 1
          rw [FreeRecursorWitnessOrder.derivationHeight_zero_rule, ihb]
      | succ m =>
          exact FreeRecursorWitnessOrder.derivationHeight_successor _ _ _
      | wrap u v => exact rootMachine.cost_terminal rfl
      | recur u v w => exact rootMachine.cost_terminal rfl

/--
Proves: the least-height theorem `derivationHeight_pointwise_least` read on the
closed four-constructor syntax: every natural ranking of the seven-constructor
root rules bounds the root height of a closed free term at its image.
Does not prove: anything about terms outside the image.
Relation: `FreeRecursorStep` on `RecursorTerm`, read through the embedding.
Closure: root rewriting.
Strategy: not applicable.
Trust: Lean kernel with the axioms of `derivationHeight_pointwise_least`.
Scope: every `ImportedWholeWitness` and every closed term of `FreeTerm Empty`.
-/
theorem freeRootHeight_le_importedRanking
    (w : FreeRecursorWitnessOrder.ImportedWholeWitness) (t : FreeTerm Empty) :
    freeRootHeight t ≤ w.ranking (toRecursorTerm t) := by
  rw [← derivationHeight_toRecursorTerm]
  exact FreeRecursorWitnessOrder.derivationHeight_pointwise_least w (toRecursorTerm t)

end OperatorKO7.Meta.OperationalInexpressibility.FreeTermRecursorEmbedding
