import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSSeedCollapse
import OperatorKO7.Meta.RDRSProjectionTransaction

set_option autoImplicit false

/-!
# RDRS Retained Coordinate Hypotheses and Counter Factorisation (Milestone U3)

Roadmap source: `OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone U3 -- canonical retained coordinate + counter factorisation.

## Audit slots (Lean Development Bible W8 / R4)

```
Relation:  RDRSStep B S N T (source). The non-descending / gauge-
           invariance hypotheses are stated about R's lhs / rhs at a
           single step (b, s, n); no transitive closure or contextual
           closure is invoked.
Closure:   root.
Strategy:  N/A.
Trust:     kernel-only. No `sorry`, `admit`, `axiom`, `opaque`,
           `unsafe`, `native_decide`, `bv_decide`, `csimp`, `extern`,
           `implemented_by`, or `addDeclWithoutChecking`.
Scope:     parametric over a `StaticRetainedHypotheses R` package the
           caller supplies. No claim that arbitrary RDRS satisfies the
           package. The counter-factorisation theorem ships in its
           factor-map-hypothesis form (structural blocker:
           blocker_id `retained_coordinate_factor_map_required`,
           category `structural_blocker`; the unconditional version
           is mathematically false in general -- not every projection's
           retained coordinate factors through the recursion counter
           without the caller-supplied factor map). The module never
           asserts an unconditional factorisation.
```

The roadmap line:

```
valid static projection transaction
  + payload gauge covariance
  + payload multiplicity discard
  + strict retained descent
  + fixed canonical trace basis
        |
        v
retained coordinate factors through the recursion counter
```

is implemented as a hypothesis package `StaticRetainedHypotheses` plus
a conditional implication `retainedCoordinate_factorsThrough_counter`.

Provided surfaces:

* `StaticRetainedHypotheses R` -- structural hypothesis package on an
  RDRS step `R`. Records the canonical trace coordinates (payload
  multiplicity, wrapper multiplicity, recursion counter), their
  non-descending witnesses, and an abstract payload-gauge action under
  which the counter is invariant.
* `counter_gaugeInvariant` -- payload-gauge invariance of the counter.
* `payloadMultiplicity_not_descending` -- payload multiplicity does
  not strictly descend along any step (in fact: `lhs ≤ rhs`).
* `wrapperMultiplicity_not_descending` -- wrapper multiplicity does
  not strictly descend along any step (in fact: `lhs ≤ rhs`).
* `seedPayload_cannot_carry_strict_descent_after_collapse` -- any
  observable factoring through a seed-collapse cannot witness strict
  descent across an RDRS step on which the carrier value is preserved.
* `retainedCoordinate_factorsThrough_counter` -- if the projection
  transaction's retained coordinate factors through the recursion
  counter (the caller exhibits an explicit factor map), then the
  projected measure on the original term type factors through the
  recursion counter as well.

## Non-vacuity status

* `StaticRetainedHypotheses R` is **unconditionally** inhabited via
  the trivial-counter witness `StaticRetainedHypotheses.trivial`
  (constant-zero counters, unit-typed gauge transformation). The
  witness records inhabitation only; it does not exhibit a
  termination measure.

## Honesty discipline

* The static-hypothesis package must be supplied by the caller. No
  claim is made that every RDRS satisfies the package.
* The counter-factorisation conclusion is stated as a conditional:
  the caller supplies an explicit `factor : Nat -> CounterIndex`
  witnessing "fixed canonical trace basis"; the theorem then composes
  to the measure-level factorisation. No unconditional version is
  asserted.
* No claim that arbitrary projections, arbitrary semantic quotients,
  full DP processors, full MSPO, or full WPO/gWPO satisfy these
  hypotheses.

Scope: no `sorry`, `admit`, `axiom`, or production `example :`. No U2
imports.
-/

namespace OperatorKO7.RDRSRetainedCoordinate

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSeedCollapse
open OperatorKO7.RDRSProjectionTransaction

/-- Static-transaction structural hypothesis package for an RDRS step.

Records the canonical trace coordinates, their non-descending
witnesses, and an abstract payload-gauge action under which the
counter is invariant. This is the structural content of "payload
gauge covariance + payload multiplicity discard + fixed canonical
trace basis" in the roadmap.

The package is parametric and must be supplied by the caller -- no
claim is made that every RDRS satisfies these properties.

**Audit slots.**

* **Proves:** the existence of the canonical trace-coordinate data
  with the stated non-descending and gauge-invariance equations.
* **Does not prove:** that any specific RDRS family satisfies the
  package; does not prove SN or confluence.
* **Relation:** RDRSStep B S N T at a single step.
* **Closure:** root.
* **Strategy:** N/A.
* **Trust:** kernel-only.
* **Scope:** parametric. -/
structure StaticRetainedHypotheses
    {B S N T : Type} (R : RDRSStep B S N T) where
  /-- Payload-multiplicity coordinate on the source term type. -/
  payloadMultiplicity : T → Nat
  /-- Wrapper-multiplicity coordinate on the source term type. -/
  wrapperMultiplicity : T → Nat
  /-- Recursion-counter coordinate on the source term type. -/
  counter             : T → Nat
  /-- Payload multiplicity is non-descending along every step. -/
  payloadMultiplicity_not_descending_field :
    ∀ b s n,
      payloadMultiplicity (R.lhs b s n)
        ≤ payloadMultiplicity (R.rhs b s n)
  /-- Wrapper multiplicity is non-descending along every step. -/
  wrapperMultiplicity_not_descending_field :
    ∀ b s n,
      wrapperMultiplicity (R.lhs b s n)
        ≤ wrapperMultiplicity (R.rhs b s n)
  /-- Abstract payload-gauge transformation type. -/
  PayloadGaugeTransformation : Type
  /-- The payload-gauge action on the source term type. -/
  payloadGaugeAction         : PayloadGaugeTransformation → T → T
  /-- The counter is invariant under every payload-gauge
  transformation. -/
  counter_gaugeInvariant_field :
    ∀ g t, counter (payloadGaugeAction g t) = counter t

variable {B S N T : Type} {R : RDRSStep B S N T}

/-! ### Non-vacuity witness (Lean Development Bible R5 / S09) -/

/-- Trivial `StaticRetainedHypotheses` witness: constant-zero
multiplicities and counter; unit-typed gauge transformation acting as
identity. Documents inhabitation only; does **not** exhibit a
substantive descent measure. -/
def StaticRetainedHypotheses.trivial
    {B S N T : Type} (R : RDRSStep B S N T) :
    StaticRetainedHypotheses R where
  payloadMultiplicity                       := fun _ => 0
  wrapperMultiplicity                       := fun _ => 0
  counter                                   := fun _ => 0
  payloadMultiplicity_not_descending_field  := fun _ _ _ => Nat.le_refl 0
  wrapperMultiplicity_not_descending_field  := fun _ _ _ => Nat.le_refl 0
  PayloadGaugeTransformation                := Unit
  payloadGaugeAction                        := fun _ t => t
  counter_gaugeInvariant_field              := fun _ _ => rfl

/-- **Non-vacuity (unconditional):** `StaticRetainedHypotheses R` is
non-empty for every RDRS step. The witness uses constant-zero
coordinates, so inhabitation is documented but the witness does not
establish termination. -/
theorem StaticRetainedHypotheses_nonempty
    {B S N T : Type} (R : RDRSStep B S N T) :
    Nonempty (StaticRetainedHypotheses R) :=
  ⟨StaticRetainedHypotheses.trivial R⟩

/-! ### Named exports of the hypothesis-package fields -/

/-- **Payload-gauge invariance of the counter.** Under the static-
hypothesis package, the recursion counter is invariant under every
payload-gauge transformation.

**Audit slots.**

* **Proves:** `SH.counter (SH.payloadGaugeAction g t) = SH.counter t`.
* **Does not prove:** invariance of the payload or wrapper coordinates
  under the gauge; does not claim the gauge group has any structure
  beyond a typed action.
* **Relation:** N/A (purely about the coordinate function).
* **Trust:** kernel-only (field accessor). -/
theorem counter_gaugeInvariant
    (SH : StaticRetainedHypotheses R)
    (g : SH.PayloadGaugeTransformation) (t : T) :
    SH.counter (SH.payloadGaugeAction g t) = SH.counter t :=
  SH.counter_gaugeInvariant_field g t

/-- **Payload multiplicity is not descending.** Under the static-
hypothesis package, the payload multiplicity does not strictly descend
along any RDRS step.

**Audit slots.**

* **Proves:** `SH.payloadMultiplicity (R.lhs b s n)
                  ≤ SH.payloadMultiplicity (R.rhs b s n)`.
* **Does not prove:** equality (the bound is `≤`, not `=`); does not
  prove anything about non-payload coordinates.
* **Relation:** RDRSStep at the single step `(b, s, n)`.
* **Closure:** root.
* **Trust:** kernel-only (field accessor). -/
theorem payloadMultiplicity_not_descending
    (SH : StaticRetainedHypotheses R) (b : B) (s : S) (n : N) :
    SH.payloadMultiplicity (R.lhs b s n)
      ≤ SH.payloadMultiplicity (R.rhs b s n) :=
  SH.payloadMultiplicity_not_descending_field b s n

/-- **Wrapper multiplicity is not descending.** Under the static-
hypothesis package, the wrapper multiplicity does not strictly descend
along any RDRS step.

**Audit slots.**

* **Proves:** `SH.wrapperMultiplicity (R.lhs b s n)
                  ≤ SH.wrapperMultiplicity (R.rhs b s n)`.
* **Does not prove:** equality; does not constrain non-wrapper
  coordinates.
* **Relation:** RDRSStep at `(b, s, n)`.
* **Closure:** root.
* **Trust:** kernel-only (field accessor). -/
theorem wrapperMultiplicity_not_descending
    (SH : StaticRetainedHypotheses R) (b : B) (s : S) (n : N) :
    SH.wrapperMultiplicity (R.lhs b s n)
      ≤ SH.wrapperMultiplicity (R.rhs b s n) :=
  SH.wrapperMultiplicity_not_descending_field b s n

/-! ### Seed-collapse / strict-descent incompatibility -/

/-- **Seed payload cannot carry strict descent after collapse.**

If an observable `obs : T → X` factors through a seed-collapse `SC`,
and the seed-collapse value is preserved across an RDRS step
`(b, s, n)`, then `obs` cannot witness a strict descent on that step
under any irreflexive strict relation.

This is the structural sense in which collapsing payload coordinates
eliminates strict-descent candidates: the post-collapse observable is
determined by the carrier value, and the carrier value is fixed across
the step.

**Audit slots.**

* **Proves:** `¬ lt (obs (R.rhs b s n)) (obs (R.lhs b s n))` under the
  pointwise carrier-preservation hypothesis and irreflexivity of `lt`.
* **Does not prove:** non-descent for steps on which the carrier value
  changes; does not establish termination, only single-step
  obstruction.
* **Relation:** RDRSStep at `(b, s, n)`.
* **Closure:** root (single step).
* **Strategy:** N/A.
* **Trust:** kernel-only (`rw` + irreflexivity).
* **Scope:** pointwise on `(b, s, n)`. -/
theorem seedPayload_cannot_carry_strict_descent_after_collapse
    {PayloadCarrier : Type} (SC : SeedCollapse PayloadCarrier T)
    {X : Type} {obs : T → X} (F : FactorsThroughSeedCollapse SC obs)
    {lt : X → X → Prop} (irrefl : ∀ x, ¬ lt x x)
    (b : B) (s : S) (n : N)
    (carrier_preserved :
      SC.collapse (R.lhs b s n) = SC.collapse (R.rhs b s n)) :
    ¬ lt (obs (R.rhs b s n)) (obs (R.lhs b s n)) := by
  intro h
  have eq_obs : obs (R.rhs b s n) = obs (R.lhs b s n) := by
    rw [F.obs_eq (R.rhs b s n), F.obs_eq (R.lhs b s n),
        carrier_preserved]
  rw [eq_obs] at h
  exact irrefl _ h

/-! ### Retained-coordinate factorisation through the recursion counter -/

/-- **Retained coordinate factors through the recursion counter
(factor-map-hypothesis form; structural blocker for the unconditional
version).**

Under the static-transaction hypotheses (a `StaticRetainedHypotheses`
package, plus the "fixed canonical trace basis" datum: an explicit
factor map exhibiting the projection's retained coordinate as a
function of the recursion counter), the projected measure on the
original term type factors through the recursion counter.

The hypothesis structure is honest: we do **not** claim that every
projection transaction's retained coordinate factors through the
counter. The caller must supply the factor map; the conclusion is
then the composed factorisation through the counter, derived from
`ProjectionTransaction.mu'_factors_counter`.

**Structural blocker on the unconditional form.** The unconditional
version of this theorem ("for every `P : ProjectionTransaction R`,
there exists `factor : Nat -> P.CounterIndex` ...") is mathematically
false in general: the projection's retained coordinate can be any
function of the projected space, and there is no canonical way to
identify which `Nat`-indexed factor corresponds to the recursion
counter without the caller-supplied data. Recorded as
`blocker_id: retained_coordinate_factor_map_required`,
`category: structural_blocker`.

**Audit slots.**

* **Proves:** if there exists `factor : Nat -> P.CounterIndex` with
  `P.retainedCoordinate (P.pi t) = factor (SH.counter t)` for every
  `t`, then there exists `factorFromCounter : Nat -> P.A'` with
  `P.mu' (P.pi t) = factorFromCounter (SH.counter t)` for every `t`.
* **Does not prove:** an unconditional factorisation. The
  unconditional version is mathematically false; see the structural
  blocker note above. The capstone re-exports the factor-map-
  hypothesis shape unchanged.
* **Relation:** N/A at the conclusion level (structural about a
  pre-orientation factorisation).
* **Trust:** kernel-only (`rw`).
* **Scope:** factor-map-hypothesis form only; the unconditional
  version is a structural blocker. -/
theorem retainedCoordinate_factorsThrough_counter
    (P : ProjectionTransaction R)
    (SH : StaticRetainedHypotheses R)
    (h : ∃ factor : Nat → P.CounterIndex,
        ∀ t, P.retainedCoordinate (P.pi t) = factor (SH.counter t)) :
    ∃ factorFromCounter : Nat → P.A',
      ∀ t, P.mu' (P.pi t) = factorFromCounter (SH.counter t) := by
  obtain ⟨factor, hfactor⟩ := h
  refine ⟨fun n => P.counterFactor (factor n), ?_⟩
  intro t
  rw [P.mu'_factors_counter (P.pi t), hfactor t]



/-! ### Exact maximality of the counter-factorisation hypothesis -/

/-- Boolean source step used to show that retained-coordinate factorisation is
not automatic.  The source type has two points while the static counter below
is constant. -/
def retainedCoordinateCounterexampleStep : RDRSStep Unit Unit Unit Bool where
  lhs := fun _ _ _ => false
  rhs := fun _ _ _ => true

/-- A valid projection transaction whose retained coordinate is the identity on
`Bool`.  It satisfies every field of `ProjectionTransaction`; what fails is
factorisation of that coordinate through a constant `Nat` counter. -/
def retainedCoordinateCounterexampleTransaction :
    ProjectionTransaction retainedCoordinateCounterexampleStep where
  T' := Bool
  pi := id
  Rproj := retainedCoordinateCounterexampleStep
  pi_commutes_lhs := by intro b s n; rfl
  pi_commutes_rhs := by intro b s n; rfl
  A' := Bool
  mu' := id
  ltA' := fun _ _ => False
  PayloadCarrier := Bool
  seedCollapse := SeedCollapse.id Bool
  pi_factors_seedCollapse := {
    factor := id
    obs_eq := by intro t; rfl
  }
  CounterIndex := Bool
  counterFactor := id
  retainedCoordinate := id
  mu'_factors_counter := by intro t; rfl

/-- The unrestricted factor-map assertion is false.  Consequently the explicit
factor-map premise of `retainedCoordinate_factorsThrough_counter` cannot be
removed from a theorem quantified over arbitrary projection transactions and
static retained-coordinate packages. -/
theorem retainedCoordinate_unconditional_factorization_false :
    ¬ (∀ (P : ProjectionTransaction retainedCoordinateCounterexampleStep)
        (SH : StaticRetainedHypotheses retainedCoordinateCounterexampleStep),
        ∃ factor : Nat → P.CounterIndex,
          ∀ t, P.retainedCoordinate (P.pi t) = factor (SH.counter t)) := by
  intro h
  rcases h retainedCoordinateCounterexampleTransaction
      (StaticRetainedHypotheses.trivial retainedCoordinateCounterexampleStep) with
    ⟨factor, hf⟩
  have hfalse := hf false
  have htrue := hf true
  change false = factor 0 at hfalse
  change true = factor 0 at htrue
  have hbad : false = true := hfalse.trans htrue.symm
  cases hbad

/-- Exact boundary package: the factor-map premise is sufficient for
measure-level counter factorisation, and a concrete valid transaction proves
that the premise is not derivable uniformly. -/
structure RetainedCoordinateFactorizationExactBoundary : Prop where
  sufficient :
    ∀ {B S N T : Type} {R : RDRSStep B S N T}
      (P : ProjectionTransaction R)
      (SH : StaticRetainedHypotheses R),
      (∃ factor : Nat → P.CounterIndex,
        ∀ t, P.retainedCoordinate (P.pi t) = factor (SH.counter t)) →
      ∃ factorFromCounter : Nat → P.A',
        ∀ t, P.mu' (P.pi t) = factorFromCounter (SH.counter t)
  unrestrictedFalse :
    ¬ (∀ (P : ProjectionTransaction retainedCoordinateCounterexampleStep)
        (SH : StaticRetainedHypotheses retainedCoordinateCounterexampleStep),
        ∃ factor : Nat → P.CounterIndex,
          ∀ t, P.retainedCoordinate (P.pi t) = factor (SH.counter t))

/-- Fully proved maximality certificate for retained-coordinate factorisation. -/
theorem retainedCoordinate_factorization_exact_boundary :
    RetainedCoordinateFactorizationExactBoundary where
  sufficient := fun P SH h => retainedCoordinate_factorsThrough_counter P SH h
  unrestrictedFalse := retainedCoordinate_unconditional_factorization_false

/-- Audit anchor for the U3 retained-coordinate factorisation surface.
Downstream classifiers cite this String when wiring the retained-
coordinate branch through the projection-transaction surface. -/
def rdrs_retained_coordinate_anchor : String :=
  "OperatorKO7.RDRSRetainedCoordinate.retainedCoordinate_factorsThrough_counter"

end OperatorKO7.RDRSRetainedCoordinate
