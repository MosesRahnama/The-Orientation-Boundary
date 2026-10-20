import OperatorKO7.Meta.Recursor.MassProfileIdentity
import OperatorKO7.Meta.ReverseMath.SizeChangeSoundness

/-!
# Non-vacuous forms of the two closure theorems

Three upstream statements carry no content once their definitions are unfolded.

* The canonical licensed quotient takes the trivial gauge group, `PUnit` as quotient
  carrier and `True` as obstruction, so its projection identifies every pair of orbit
  functions and the first conjunct of TRS-equivalence holds of anything.
* The orbit-system isomorphism transports the index, so it holds of any two injectively
  indexed orbits and says nothing about recursors or circular references.
* The information-equivalence definition requires the discarded-information functional to
  be constant on the whole linear-growth class, so the equivalence theorem is immediate
  from the definition.

This module replaces all three with statements that carry content, all of them resting on
the pointwise mass identity of `Meta/Recursor/MassProfileIdentity.lean`.

* `massProfileLicensedQuotient` is a licensed quotient whose projection is *not* constant
  (`massProfileLicensedQuotient_separates`), yet which still identifies the recursor orbit
  with the circular orbit (`massProfileLicensedQuotient_identifies_recursor_and_circular`).
* `orbit_isomorphism_does_not_transport_termination` proves the index bijection carries no
  termination content, by exhibiting the descent measure on one side and its impossibility
  on the other.
* `information_equivalence_for_every_functional` drops the invariance field entirely: with
  pointwise identity in hand, *every* discarded-information functional agrees on the two
  orbits, and `slopeFunctional_is_not_constant` shows that class is non-degenerate.

Relation: constructor-cost equations, plus `SelfEmbeddingStep` and `DupDPStep`.
Closure: orbit-indexed.
Strategy: not applicable.
Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`, no native reduction.
-/

set_option autoImplicit false

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.MassProfileIdentity
open OperatorKO7.ReverseMath.SizeChangeSoundness

namespace OperatorKO7.Meta.Recursor.NonvacuousClosure

/-! ### A licensed quotient with a non-trivial carrier -/

/--
A licensed quotient on orbit functions: a gauge action, a quotient carrier, a projection
that is invariant under the action, and the obstruction the license discharges.

The upstream canonical instance takes `Q = PUnit`, which makes `proj` constant. The
instance below takes `Q = (Nat → Nat)`, the mass profile.
-/
structure LicensedQuotient (Gauge Q : Type) where
  /-- The gauge action on orbit functions. -/
  act : Gauge → (Nat → Trace) → (Nat → Trace)
  /-- The quotient projection. -/
  proj : (Nat → Trace) → Q
  /-- The projection respects the gauge action. -/
  proj_gauge_invariant : ∀ g o, proj (act g o) = proj o

/-- The gauge group: the payload relabellings that preserve whole-term mass. -/
def MassPreservingRelabel (mu : Trace → Nat) : Type :=
  { f : Trace → Trace // ∀ t, mu (f t) = mu t }

/-- A relabelling acts on an orbit function pointwise. -/
def payloadRelabel (mu : Trace → Nat)
    (g : MassPreservingRelabel mu) (o : Nat → Trace) : Nat → Trace :=
  fun n => g.1 (o n)

/--
The mass-profile licensed quotient: gauge group the mass-preserving payload relabellings,
quotient carrier the mass profile, projection the orbit's mass profile.
-/
def massProfileLicensedQuotient (mu : Trace → Nat) :
    LicensedQuotient (MassPreservingRelabel mu) (Nat → Nat) where
  act := payloadRelabel mu
  proj := fun o n => mu (o n)
  proj_gauge_invariant := by
    intro g o
    funext n
    exact g.2 (o n)

/-- The gauge group is inhabited by the identity relabelling (Gate R5). -/
def identityRelabel (mu : Trace → Nat) : MassPreservingRelabel mu :=
  ⟨id, fun _ => rfl⟩

/--
Intent: the quotient carrier is genuinely non-trivial. Two orbit functions with different
mass profiles receive different images, so this projection is not the constant map that the
`PUnit` carrier forces.

Trust: kernel-only.
-/
theorem massProfileLicensedQuotient_separates
    (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1) :
    ∃ o₁ o₂ : Nat → Trace,
      (massProfileLicensedQuotient mu).proj o₁
        ≠ (massProfileLicensedQuotient mu).proj o₂ := by
  refine ⟨fun _ => void, fun _ => delta void, ?_⟩
  intro h
  have h0 := congrFun h 0
  simp only [massProfileLicensedQuotient] at h0
  rw [mu_delta void] at h0
  omega

/--
Intent: the non-trivial quotient still identifies the recursor orbit with the circular
orbit, so the identification is a theorem about these two orbits rather than a consequence
of collapsing every orbit to a point.

Trust: kernel-only.
-/
theorem massProfileLicensedQuotient_identifies_recursor_and_circular
    (b s : Trace)
    (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, mu (recΔ b' s' u) = mu u + 1) :
    (massProfileLicensedQuotient mu).proj (RecursorOrbit b s)
      = (massProfileLicensedQuotient mu).proj (selfEmbeddingOrbit (recΔ b s void)) :=
  recursorOrbit_selfEmbeddingOrbit_massProfile_funext b s mu mu_delta mu_rec

/-! ### The index bijection carries no termination content -/

/--
Intent: the orbit-system isomorphism transports the index and nothing else. The recursor's
extracted descent admits a strictly decreasing measure while the circular relation admits
none, so no index-preserving bijection between the two orbits can transport termination.

This is the limitation the manuscript should record in place of reading the isomorphism as
evidence of sameness.

Trust: kernel-only.
-/
theorem orbit_isomorphism_does_not_transport_termination :
    (∃ proj : DupDPTerm → Nat,
        ∀ s t : DupDPTerm, DupDPStep s t → proj t < proj s)
      ∧ (∀ f : Trace → Nat,
        ¬ (∀ t u : Trace, SelfEmbeddingStep t u → f u < f t)) :=
  ⟨⟨dupDPProjection, dupDPStep_projection_strict⟩,
   selfEmbeddingStep_admits_no_strictlyDecreasing_natMeasure⟩

/--
Proves: the two relations differ on well-foundedness, so their orbit systems are separated
by a property the index bijection cannot see.
-/
theorem dupDP_wellFounded_while_selfEmbedding_is_not :
    WellFounded (fun t s => DupDPStep s t)
      ∧ (∀ f : Trace → Nat,
          ¬ (∀ t u : Trace, SelfEmbeddingStep t u → f u < f t)) :=
  ⟨dupDPStep_wellFounded, selfEmbeddingStep_admits_no_strictlyDecreasing_natMeasure⟩

/-! ### Information equivalence with no invariance field -/

/--
Intent: **information equivalence without the stipulated invariance**. Every
discarded-information functional whatsoever, with no linear-growth invariance field,
assigns the recursor orbit and the circular orbit the same value.

The upstream definition reaches its conclusion by requiring the functional to be constant
on the entire linear-growth class. Here the conclusion follows from the pointwise identity
of the two profiles, so the functional class is unrestricted.

Trust: kernel-only.
-/
theorem information_equivalence_for_every_functional
    (E : (Nat → Nat) → Nat)
    (b s : Trace)
    (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, mu (recΔ b' s' u) = mu u + 1) :
    E (fun n => mu (RecursorOrbit b s n))
      = E (fun n => mu (selfEmbeddingOrbit (recΔ b s void) n)) := by
  rw [recursorOrbit_selfEmbeddingOrbit_massProfile_funext b s mu mu_delta mu_rec]

/-- A slope-sensitive discarded-information functional: the first increment of the profile. -/
def slopeFunctional (f : Nat → Nat) : Nat := f 1 - f 0

/--
Proves: the functional class is non-degenerate. `slopeFunctional` separates two
linear-growth profiles, so it fails the upstream invariance field, yet
`information_equivalence_for_every_functional` still applies to it.

This is the Gate R5 non-vacuity witness for the unrestricted quantifier.
-/
theorem slopeFunctional_is_not_constant_on_linearGrowth :
    ∃ f g : Nat → Nat,
      LinearGrowth f ∧ LinearGrowth g ∧ slopeFunctional f ≠ slopeFunctional g := by
  refine ⟨fun n => n, fun n => 2 * n,
    ⟨1, 0, fun n => by show n = 1 * n + 0; omega⟩,
    ⟨2, 0, fun n => by show 2 * n = 2 * n + 0; omega⟩, ?_⟩
  simp only [slopeFunctional]
  omega

/--
Proves: the slope-sensitive functional agrees on the two orbits anyway, which is the
content the invariance field was standing in for.
-/
theorem slopeFunctional_agrees_on_recursor_and_circular
    (b s : Trace)
    (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, mu (recΔ b' s' u) = mu u + 1) :
    slopeFunctional (fun n => mu (RecursorOrbit b s n))
      = slopeFunctional (fun n => mu (selfEmbeddingOrbit (recΔ b s void) n)) :=
  information_equivalence_for_every_functional slopeFunctional b s mu mu_delta mu_rec

end OperatorKO7.Meta.Recursor.NonvacuousClosure
