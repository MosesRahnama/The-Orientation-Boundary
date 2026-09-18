import OperatorKO7.Meta.Recursor.CircularIdentity

/-!
# Pointwise mass-profile identity: the recursor and a circular reference

This module closes the gap between the class-level statement of
`Meta/Recursor/CircularIdentity.lean` (both orbits satisfy `LinearGrowth`) and the
separation-failure claim the manuscript draws from it.

Satisfying the same existential growth predicate leaves two profiles distinguishable by
their slope and intercept, so `LinearGrowth` on both sides does not by itself block a
mass-profile observer. The merge-chain circular witness used upstream in fact never
matches the recursor pointwise (`mergeChainOrbit_massProfile_never_eq_recursorOrbit`).

The repair is to name the circular reference the manuscript's schematic actually
describes, namely the self-embedding rule `t → delta t`, whose right-hand side contains
its own left-hand side as a proper subterm. Under that witness the two mass profiles
agree pointwise and unconditionally, from a shared initial state, and every observer
that factors through the mass profile therefore returns the same value on both orbits.

Relation: the kernel constructor-cost equations of `DirectMeasureProofSystem`.
Closure: orbit-indexed (one state per index), not the reflexive-transitive kernel closure.
Strategy: not applicable (the statements are about mass profiles, not reduction strategy).
Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`, no native reduction.
-/

set_option autoImplicit false

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.Recursor.CircularIdentity

universe u

namespace OperatorKO7.Meta.Recursor.MassProfileIdentity

/-! ### The self-embedding circular reference -/

/--
Intent: the one-rule rewrite relation `t → delta t`, whose right-hand side contains its
own left-hand side as a proper subterm. This is the circular reference in the schematic
sense used by the manuscript: firing the rule reproduces the redex inside the reduct.

Relation: this relation alone, not the KO7 kernel `Step`.
Closure: one-step, at the root of the whole term.
-/
inductive SelfEmbeddingStep : Trace → Trace → Prop
  | fire : ∀ t : Trace, SelfEmbeddingStep t (delta t)

/-- The orbit of `SelfEmbeddingStep` from `A`: the state after `n` firings. -/
def selfEmbeddingOrbit (A : Trace) : Nat → Trace
  | 0 => A
  | n + 1 => delta (selfEmbeddingOrbit A n)

/--
Proves: consecutive orbit states are related by the self-embedding rule.
Scope: every index and every start term.
-/
theorem selfEmbeddingStep_orbit_succ (A : Trace) (n : Nat) :
    SelfEmbeddingStep (selfEmbeddingOrbit A n) (selfEmbeddingOrbit A (n + 1)) :=
  SelfEmbeddingStep.fire _

/--
Proves: the relation has no normal form at all, so every state is a redex.
Does not prove: anything about the KO7 kernel relation `Step`.
-/
theorem selfEmbeddingStep_has_no_normalForm (t : Trace) :
    ∃ u : Trace, SelfEmbeddingStep t u :=
  ⟨delta t, SelfEmbeddingStep.fire t⟩

/--
Proves: no measure into `Nat` decreases strictly across the self-embedding rule.
This is the non-termination content of the circular witness stated in exactly the
vocabulary a direct-measure proof system uses, so it is the statement the separation
claim needs.

Trust: kernel-only. The argument instantiates the assumed descent along the orbit and
contradicts it at index `f t + 1`.
-/
theorem selfEmbeddingStep_admits_no_strictlyDecreasing_natMeasure
    (f : Trace → Nat) :
    ¬ (∀ t u : Trace, SelfEmbeddingStep t u → f u < f t) := by
  intro hdec
  have key : ∀ (t : Trace) (n : Nat), f (selfEmbeddingOrbit t n) + n ≤ f t := by
    intro t n
    induction n with
    | zero => simp [selfEmbeddingOrbit]
    | succ k ih =>
        have hstep :
            f (selfEmbeddingOrbit t (k + 1)) < f (selfEmbeddingOrbit t k) :=
          hdec _ _ (selfEmbeddingStep_orbit_succ t k)
        omega
  have := key void (f void + 1)
  omega

/-- Structural size of a trace, used only to separate consecutive orbit states. -/
def traceSize : Trace → Nat
  | .void => 1
  | .delta t => traceSize t + 1
  | .integrate t => traceSize t + 1
  | .merge x y => traceSize x + traceSize y + 1
  | .app x y => traceSize x + traceSize y + 1
  | .recΔ x y z => traceSize x + traceSize y + traceSize z + 1
  | .eqW x y => traceSize x + traceSize y + 1

/-- The `delta` constructor-cost equation for `traceSize`. -/
theorem traceSize_delta (t : Trace) : traceSize (delta t) = traceSize t + 1 := rfl

/--
Proves: firing the rule always changes the state, so the orbit never stalls.
-/
theorem selfEmbeddingOrbit_succ_ne (A : Trace) (n : Nat) :
    selfEmbeddingOrbit A (n + 1) ≠ selfEmbeddingOrbit A n := by
  intro h
  have hstep :
      traceSize (selfEmbeddingOrbit A (n + 1))
        = traceSize (selfEmbeddingOrbit A n) + 1 :=
    traceSize_delta (selfEmbeddingOrbit A n)
  rw [h] at hstep
  omega

/-! ### The mass profile of the self-embedding orbit -/

/--
Proves: the self-embedding orbit's whole-term mass is the start mass plus the index.
Relation: any `mu` obeying the `delta` constructor-cost equation.
-/
theorem selfEmbeddingOrbit_mass
    (A : Trace) (n : Nat)
    (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1) :
    mu (selfEmbeddingOrbit A n) = mu A + n := by
  induction n with
  | zero => simp [selfEmbeddingOrbit]
  | succ k ih =>
      show mu (delta (selfEmbeddingOrbit A k)) = mu A + (k + 1)
      rw [mu_delta, ih]
      omega

/-! ### The two orbits share their initial state -/

/--
Proves: the recursor orbit and the self-embedding orbit started at the recursor's own
index-zero state are the same term at index zero.
-/
theorem recursorOrbit_selfEmbeddingOrbit_initialState_eq (b s : Trace) :
    RecursorOrbit b s 0 = selfEmbeddingOrbit (recΔ b s void) 0 :=
  rfl

/-! ### The headline: pointwise identity of the two mass profiles -/

/--
Intent: under every direct measure obeying the constructor-cost equations, the
step-duplicating recursor orbit and the circular self-embedding orbit launched from the
recursor's own initial state carry **equal mass at every index**, not merely profiles of
a common growth class.

Relation: the constructor-cost equations for `delta` and `recΔ`.
Closure: orbit-indexed.
Strategy: not applicable.
Trust: kernel-only.
Non-vacuity witness: `recursorOrbit_selfEmbeddingOrbit_initialState_eq` gives a shared
start state, and `selfEmbeddingStep_admits_no_strictlyDecreasing_natMeasure` certifies
that the circular side genuinely fails every direct measure.
-/
theorem recursorOrbit_selfEmbeddingOrbit_massProfile_pointwise_eq
    (b s : Trace)
    (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, mu (recΔ b' s' u) = mu u + 1)
    (n : Nat) :
    mu (RecursorOrbit b s n) = mu (selfEmbeddingOrbit (recΔ b s void) n) := by
  rw [step_duplicator_orbit_mass_grows_linearly b s n mu mu_delta mu_rec,
      selfEmbeddingOrbit_mass (recΔ b s void) n mu mu_delta, mu_rec]
  omega

/--
Proves: the two mass profiles are equal as functions `Nat → Nat`.
-/
theorem recursorOrbit_selfEmbeddingOrbit_massProfile_funext
    (b s : Trace)
    (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, mu (recΔ b' s' u) = mu u + 1) :
    (fun n => mu (RecursorOrbit b s n))
      = (fun n => mu (selfEmbeddingOrbit (recΔ b s void) n)) := by
  funext n
  exact recursorOrbit_selfEmbeddingOrbit_massProfile_pointwise_eq b s mu mu_delta mu_rec n

/--
Intent: **the separation-failure theorem**. Every observer whose input is the orbit's
mass profile returns the same value on the terminating recursor orbit and on the
non-terminating circular orbit. The quantifier ranges over all observers of that shape,
so the statement covers every decision procedure, every classifier, and every predicate
that reads the profile and nothing else.

Does not prove: that no observer whatsoever separates the two orbits. Observers with
access to the rule syntax, to the counter coordinate, or to the states themselves are
outside the hypothesis, and the dependency-pair projection is exactly such an observer.

Relation: the constructor-cost equations for `delta` and `recΔ`.
Trust: kernel-only.
-/
theorem massProfileObserver_cannot_separate_recursorOrbit_from_selfEmbeddingOrbit
    {α : Sort u} (Φ : (Nat → Nat) → α)
    (b s : Trace)
    (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1) :
    Φ (fun n => D.mu (RecursorOrbit b s n))
      = Φ (fun n => D.mu (selfEmbeddingOrbit (recΔ b s void) n)) := by
  rw [recursorOrbit_selfEmbeddingOrbit_massProfile_funext b s D.mu mu_delta mu_rec]

/-! ### The descent verdict, which is what a direct measure actually consumes -/

/-- The verdict a strict-decrease direct-measure system reads at index `n`. -/
def descentVerdict (mu : Trace → Nat) (o : Nat → Trace) (n : Nat) : Bool :=
  decide (mu (o (n + 1)) < mu (o n))

/--
Proves: along the recursor orbit the direct measure never records a descent.
-/
theorem descentVerdict_recursorOrbit_eq_false
    (b s : Trace) (n : Nat)
    (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, mu (recΔ b' s' u) = mu u + 1) :
    descentVerdict mu (RecursorOrbit b s) n = false := by
  have h1 := step_duplicator_orbit_mass_grows_linearly b s n mu mu_delta mu_rec
  have h2 := step_duplicator_orbit_mass_grows_linearly b s (n + 1) mu mu_delta mu_rec
  simp only [descentVerdict, decide_eq_false_iff_not, Nat.not_lt, h1, h2]
  omega

/--
Proves: along the circular orbit the direct measure never records a descent either.
-/
theorem descentVerdict_selfEmbeddingOrbit_eq_false
    (A : Trace) (n : Nat)
    (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1) :
    descentVerdict mu (selfEmbeddingOrbit A) n = false := by
  have h1 := selfEmbeddingOrbit_mass A n mu mu_delta
  have h2 := selfEmbeddingOrbit_mass A (n + 1) mu mu_delta
  simp only [descentVerdict, decide_eq_false_iff_not, Nat.not_lt, h1, h2]
  omega

/--
Proves: the descent-verdict sequences of the two orbits are equal at every index, so the
observable a strict-decrease direct-measure system actually consumes carries zero
separating evidence.
-/
theorem descentVerdict_pointwise_eq_on_recursorOrbit_and_selfEmbeddingOrbit
    (b s : Trace) (n : Nat)
    (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, mu (recΔ b' s' u) = mu u + 1) :
    descentVerdict mu (RecursorOrbit b s) n
      = descentVerdict mu (selfEmbeddingOrbit (recΔ b s void)) n := by
  rw [descentVerdict_recursorOrbit_eq_false b s n mu mu_delta mu_rec,
      descentVerdict_selfEmbeddingOrbit_eq_false _ n mu mu_delta]

/-! ### Why the merge-chain witness could only support the class-level claim -/

/--
Proves: the upstream merge-chain circular orbit **never** matches the recursor orbit's
mass profile pointwise, for any choice of `A`, `B` and any conforming measure.

This is the precise reason the class-level `LinearGrowth` statement fails to deliver the
separation claim on the merge-chain witness, and the reason the self-embedding witness
above is the one the argument needs.

Trust: kernel-only. The argument reads the profile identity at indices `0` and `1`.
-/
theorem mergeChainOrbit_massProfile_never_eq_recursorOrbit
    (b s A B : Trace)
    (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, mu (recΔ b' s' u) = mu u + 1)
    (mu_merge : ∀ x y : Trace, mu (merge x y) = mu x + mu y + 1) :
    ¬ (∀ n : Nat,
        mu (RecursorOrbit b s n) = mu (CircularReferenceOrbit A B n)) := by
  intro hall
  have h0 := hall 0
  have h1 := hall 1
  rw [step_duplicator_orbit_mass_grows_linearly b s 0 mu mu_delta mu_rec,
      circular_reference_orbit_mass_grows_linearly A B 0 mu mu_merge] at h0
  rw [step_duplicator_orbit_mass_grows_linearly b s 1 mu mu_delta mu_rec,
      circular_reference_orbit_mass_grows_linearly A B 1 mu mu_merge] at h1
  omega

end OperatorKO7.Meta.Recursor.MassProfileIdentity
