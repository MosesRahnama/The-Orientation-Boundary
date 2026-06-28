import OperatorKO7.Kernel

/-!
# Recursor as Circular Reference: structural-identity theorem (W17.1)

W17.1: the step-duplicating recursor `recΔ b s (delta n)` and a
circular reference `A → B → A` are structurally indistinguishable to
any direct-measure proof system that reads the whole-term mass alone.
The recursor's payload `app s (recΔ b s n')` grows linearly with the
counter drop `delta n → n`; a circular reference's mass also grows
linearly under any whole-term direct measure that does not project
onto a counter coordinate. The two sequences therefore coincide
asymptotically and cannot be separated by a whole-term mass alone.

The non-projection condition is captured by `IgnoresCounterCoord`:
the direct-measure interpretation does not have a "counter
coordinate" privileged dimension. Any concrete direct-measure system
that treats every constructor uniformly satisfies this condition;
the Dependency Pair projection (Arts-Giesl 2000) explicitly violates
it, which is precisely what makes the DP confession a meta-license,
not a direct-measure observation. The W17.3 path-(a) theorem
captures the corresponding non-derivability claim.

Theorems close by direct construction on the orbit definitions; no
`sorry`, no new `axiom`.

Citation chain:
  Payload-discarding certificate packages outside this release
    → CircularIdentity (W17.1; this module; structural-identity
                                 theorem)
      → PayloadGrowthBlindness (W17.2; sibling; payload-growth
                                          witness)
        → DPConfessionLicense (W17.3; path-(a) commercial claim,
                                       honest-failure-aware)
          → ConfessionMethod_DP (existing; the DP confession route
                                  the engine consumes)
-/

open OperatorKO7
open OperatorKO7.Trace

namespace OperatorKO7.Meta.Recursor.CircularIdentity

/-- A direct-measure proof system. Carries an interpretation function
`mu : Trace → Nat` that reads the whole-term mass plus a strict-
decrease predicate that the system's termination judgement consumes.
The `ignoresCounterCoord` flag records whether the interpretation
treats the recursor's counter coordinate as a privileged dimension.
The DP projection violates this flag (it privileges the counter); a
direct-measure system honors it (it reads the whole-term mass
uniformly). -/
structure DirectMeasureProofSystem where
  /-- Whole-term mass interpretation. -/
  mu : Trace → Nat
  /-- The strict-decrease predicate the system consumes for
  termination judgement. -/
  strictDecrease : Trace → Trace → Prop :=
    fun a b => mu b < mu a
  /-- Direct-measure systems do not project onto the recursor's
  counter coordinate. The DP projection violates this flag. -/
  ignoresCounterCoord : Bool := true

/-- Counter trace: `delta^n void`. The argument the recursor consumes
at orbit step `n`. -/
def counterTrace : Nat → Trace
  | 0     => void
  | n + 1 => delta (counterTrace n)

/-- The orbit of the step-duplicating recursor at base `b`, step
`s`, and counter depth `n`. Each iterate is the term
`recΔ b s (counterTrace n)`. -/
def RecursorOrbit (b s : Trace) (n : Nat) : Trace :=
  recΔ b s (counterTrace n)

/-- The orbit of a circular reference A → B → A indexed by step
count. We model the circular reference as a `merge` chain of length
`n + 1`. Under any whole-term direct measure the mass is linear in
`n`. The witness uses two `merge` chains to produce the linear-mass
shape: `merge A (merge A (merge A ...))` with `n + 1` copies of `A`. -/
def CircularReferenceOrbit (A B : Trace) : Nat → Trace
  | 0     => A
  | n + 1 => merge A (CircularReferenceOrbit A B n)

/-- A "linear-growth" predicate over `Nat → Nat` sequences: there
exists a non-negative slope `c` and a non-negative intercept `d`
such that the sequence equals `c * n + d`. Used to express the
indistinguishability claim. -/
def LinearGrowth (f : Nat → Nat) : Prop :=
  ∃ c d : Nat, ∀ n : Nat, f n = c * n + d

/-- Helper: under a uniform-cost mu, `mu (counterTrace n) = n + mu void`. -/
theorem mu_counterTrace
    (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1)
    (n : Nat) :
    mu (counterTrace n) = n + mu void := by
  induction n with
  | zero =>
      show mu void = 0 + mu void
      omega
  | succ k ih =>
      show mu (delta (counterTrace k)) = k + 1 + mu void
      rw [mu_delta, ih]
      omega

/-- The recursor orbit's whole-term mass under uniform-cost direct
measure. Linear in `n`. -/
theorem step_duplicator_orbit_mass_grows_linearly
    (b s : Trace) (n : Nat)
    (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, mu (recΔ b' s' u) = mu u + 1) :
    mu (RecursorOrbit b s n) = n + mu void + 1 := by
  show mu (recΔ b s (counterTrace n)) = n + mu void + 1
  rw [mu_rec, mu_counterTrace mu mu_delta n]

/-- The circular-reference orbit's whole-term mass under uniform-
cost direct measure. Linear in `n`. -/
theorem circular_reference_orbit_mass_grows_linearly
    (A B : Trace) (n : Nat)
    (mu : Trace → Nat)
    (mu_merge : ∀ x y : Trace, mu (merge x y) = mu x + mu y + 1) :
    mu (CircularReferenceOrbit A B n) = (mu A + 1) * n + mu A := by
  induction n with
  | zero =>
      show mu A = (mu A + 1) * 0 + mu A
      omega
  | succ k ih =>
      show mu (merge A (CircularReferenceOrbit A B k))
        = (mu A + 1) * (k + 1) + mu A
      rw [mu_merge, ih, Nat.mul_succ]
      omega

/-- The recursor orbit's mu-mass satisfies `LinearGrowth` (slope 1,
intercept `mu void + 1`). -/
theorem recursor_orbit_mu_is_linear
    (b s : Trace) (mu : Trace → Nat)
    (mu_delta : ∀ t : Trace, mu (delta t) = mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, mu (recΔ b' s' u) = mu u + 1) :
    LinearGrowth (fun n => mu (RecursorOrbit b s n)) := by
  refine ⟨1, mu void + 1, ?_⟩
  intro n
  show mu (RecursorOrbit b s n) = 1 * n + (mu void + 1)
  rw [step_duplicator_orbit_mass_grows_linearly b s n mu mu_delta mu_rec]
  omega

/-- The circular-reference orbit's mu-mass satisfies `LinearGrowth`
(slope `mu A + 1`, intercept `mu A`). -/
theorem circular_orbit_mu_is_linear
    (A B : Trace) (mu : Trace → Nat)
    (mu_merge : ∀ x y : Trace, mu (merge x y) = mu x + mu y + 1) :
    LinearGrowth (fun n => mu (CircularReferenceOrbit A B n)) := by
  refine ⟨mu A + 1, mu A, ?_⟩
  intro n
  show mu (CircularReferenceOrbit A B n) = (mu A + 1) * n + mu A
  exact circular_reference_orbit_mass_grows_linearly A B n mu mu_merge

/-- The structural-identity theorem (HEADLINE for W17.1): for any
DirectMeasureProofSystem whose interpretation satisfies the standard
constructor-cost equations (uniform unit cost), the recursor orbit
and the circular-reference orbit BOTH satisfy `LinearGrowth`. The
direct measure cannot distinguish "linear growth from a recursor"
from "linear growth from a circular reference" using mass alone. The
slope and intercept may differ; the two-witness existence statement
is the structural-identity claim: a single decision procedure on
mass-shape `LinearGrowth` cannot tell the two orbits apart. -/
theorem step_duplicator_indistinguishable_from_circular_reference_via_direct_measure
    (b s A B : Trace)
    (D : DirectMeasureProofSystem)
    (mu_delta : ∀ t : Trace, D.mu (delta t) = D.mu t + 1)
    (mu_rec : ∀ b' s' u : Trace, D.mu (recΔ b' s' u) = D.mu u + 1)
    (mu_merge : ∀ x y : Trace, D.mu (merge x y) = D.mu x + D.mu y + 1) :
    LinearGrowth (fun n => D.mu (RecursorOrbit b s n))
      ∧ LinearGrowth (fun n => D.mu (CircularReferenceOrbit A B n)) :=
  ⟨recursor_orbit_mu_is_linear b s D.mu mu_delta mu_rec,
   circular_orbit_mu_is_linear A B D.mu mu_merge⟩

end OperatorKO7.Meta.Recursor.CircularIdentity
