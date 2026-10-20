import OperatorKO7.Meta.DistinctionBoundary.MinimalFork
import OperatorKO7.Meta.EqGuardedConfluence
import OperatorKO7.Kernel

/-!
# What the generic diagonal-fork schema does not provide

Most Distinction rows are already schema-generic: their Lean statements quantify over an abstract
carrier and mention no KO7 constructor. The rows that are not generic need a specific datum of the
seven-constructor kernel signature, and this module names which one, as a compiled fence rather
than as prose.

A fence here is a pair. `SchemaSupplies` says what the generic diagonal-fork schema does supply: a
carrier, a one-step relation, a diagonal source, and two distinct exits from it. The three theorems
below say what it does not, each proved on `tinyFork`, the smallest inhabitant of the schema:

* `schema_lacks_equality_query`: the bare fixed-exit fork interface does not force an
  equality-sensitive query.
* `schema_lacks_injective_pairing`: no constructor that pairs two carrier elements injectively.
  This is what `merge` supplies.
* `schema_lacks_infinite_generation`: no infinite generated carrier. This is what the seven
  constructors together supply.

The KO7 guarded root relation supplies the stronger parameterized query law separately:
`ko7_guarded_equality_query` proves the diagonal and off-diagonal branches of `eqW` with their
actual argument-dependent target. Thus the positive side is not inferred from the negative tiny
model.

Relation: the diagonal fork. Closure: root.
External trust: none. Mathlib only.
-/

namespace OperatorKO7.Methods.DiagonalForkSchemaFence

open OperatorKO7

/-! ## What the schema supplies -/

/-- The data a generic diagonal-fork schema carries: a carrier, a one-step relation, a source that
sits on the diagonal, and two distinct exits from it. -/
structure SchemaSupplies where
  Carrier : Type
  step : Carrier → Carrier → Prop
  source : Carrier
  exitA : Carrier
  exitB : Carrier
  stepA : step source exitA
  stepB : step source exitB
  exits_differ : exitA ≠ exitB

/-- The two-exit fork: the smallest carrier that inhabits the schema. -/
inductive TinyFork where
  | src
  | left
  | right
  deriving DecidableEq, Repr, Fintype

inductive TinyStep : TinyFork → TinyFork → Prop
  | toLeft : TinyStep TinyFork.src TinyFork.left
  | toRight : TinyStep TinyFork.src TinyFork.right

/-- Only the source has outgoing steps. -/
theorem tinyStep_source {x y : TinyFork} (h : TinyStep x y) : x = TinyFork.src := by
  cases h <;> rfl

/-- The tiny fork inhabits the schema, so the schema is not empty and the fence below is a
statement about a real object. -/
def tinyFork : SchemaSupplies where
  Carrier := TinyFork
  step := TinyStep
  source := TinyFork.src
  exitA := TinyFork.left
  exitB := TinyFork.right
  stepA := TinyStep.toLeft
  stepB := TinyStep.toRight
  exits_differ := by decide

/-! ## Extension predicates and what the schema does not force -/

/-- The existing relation computes equality through the schema's two distinguished exits. -/
def HasEqualityQuery (X : SchemaSupplies) : Prop :=
  ∃ q : X.Carrier → X.Carrier → X.Carrier,
    (∀ a, X.step (q a a) X.exitA ∧ ¬ X.step (q a a) X.exitB) ∧
      (∀ a b, a ≠ b → X.step (q a b) X.exitB)

/-- The carrier already contains an injective binary pairing constructor. -/
def HasInjectivePairing (X : SchemaSupplies) : Prop :=
  ∃ m : X.Carrier → X.Carrier → X.Carrier,
    Function.Injective (fun p : X.Carrier × X.Carrier => m p.1 p.2)

/-- The schema carrier is infinite. -/
def HasInfiniteCarrier (X : SchemaSupplies) : Prop := Infinite X.Carrier

/-- **No fixed-exit equality query.** An equality-query constructor is a map `q` whose reduct records whether
its two arguments are equal: on the diagonal it exits one way and only that way, off the diagonal
it exits the other. The tiny fork has no such map, because its only source has both exits available
unconditionally. -/
theorem schema_lacks_equality_query :
    ¬ HasEqualityQuery tinyFork := by
  rintro ⟨q, hdiag, -⟩
  obtain ⟨hleft, hright⟩ := hdiag TinyFork.src
  have hsrc : q TinyFork.src TinyFork.src = TinyFork.src := tinyStep_source hleft
  rw [hsrc] at hright
  exact hright TinyStep.toRight

/-- **No injective pairing.** A pairing constructor combines two carrier elements into one and
keeps them apart. The tiny fork has three elements and nine pairs, so no injective pairing exists.
This is the datum `merge` supplies. -/
theorem schema_lacks_injective_pairing :
    ¬ HasInjectivePairing tinyFork := by
  change ¬ ∃ m : TinyFork → TinyFork → TinyFork,
    Function.Injective (fun p : TinyFork × TinyFork => m p.1 p.2)
  rintro ⟨m, hm⟩
  have hcard : Fintype.card (TinyFork × TinyFork) ≤ Fintype.card TinyFork :=
    Fintype.card_le_of_injective _ hm
  have hpair : Fintype.card (TinyFork × TinyFork) = 9 := by decide
  have hsingle : Fintype.card TinyFork = 3 := by decide
  rw [hpair, hsingle] at hcard
  omega

/-- **No infinite generation.** The tiny fork's carrier is finite. -/
theorem schema_lacks_infinite_generation :
    ¬ HasInfiniteCarrier tinyFork := by
  change ¬ Infinite TinyFork
  intro hInf
  exact hInf.false

/-- The bare fork data does not imply an equality query. -/
theorem diagonalForkSchema_does_not_force_equality_query :
    ¬ ∀ X : SchemaSupplies, HasEqualityQuery X := by
  intro h
  exact schema_lacks_equality_query (h tinyFork)

/-- The bare fork data does not imply an injective pairing constructor. -/
theorem diagonalForkSchema_does_not_force_injective_pairing :
    ¬ ∀ X : SchemaSupplies, HasInjectivePairing X := by
  intro h
  exact schema_lacks_injective_pairing (h tinyFork)

/-- The bare fork data does not imply an infinite carrier. -/
theorem diagonalForkSchema_does_not_force_infinite_carrier :
    ¬ ∀ X : SchemaSupplies, HasInfiniteCarrier X := by
  intro h
  exact schema_lacks_infinite_generation (h tinyFork)

/-! ## The missing carrier structures really exist on KO7 syntax -/

/-- The actual parameterized equality-query law of the guarded KO7 root relation. Unlike
`HasEqualityQuery`, the negative target retains the two queried terms. -/
def KO7ParameterizedEqualityQuery : Prop :=
  (∀ a : Trace,
      OperatorKO7.EqGuardedConfluence.EqGuardedStep (Trace.eqW a a) Trace.void
        ∧ ¬ OperatorKO7.EqGuardedConfluence.EqGuardedStep (Trace.eqW a a)
          (Trace.integrate (Trace.merge a a)))
    ∧ (∀ a b : Trace, a ≠ b →
      OperatorKO7.EqGuardedConfluence.EqGuardedStep (Trace.eqW a b)
        (Trace.integrate (Trace.merge a b)))

/-- `eqW` computes the parameterized equality distinction in the guarded relation: exactly the
reflexive branch is present on the diagonal, and the difference branch is present off it. -/
theorem ko7_guarded_equality_query : KO7ParameterizedEqualityQuery := by
  constructor
  · intro a
    refine ⟨OperatorKO7.EqGuardedConfluence.EqGuardedStep.R_eq_refl a, ?_⟩
    intro hdiff
    have heq : Trace.void = Trace.integrate (Trace.merge a a) :=
      OperatorKO7.EqGuardedConfluence.eqGuarded_unique_target
        (OperatorKO7.EqGuardedConfluence.EqGuardedStep.R_eq_refl a) hdiff
    exact Trace.noConfusion heq
  · intro a b hne
    exact OperatorKO7.EqGuardedConfluence.EqGuardedStep.R_eq_diff a b hne

/-- A constructor tower witnessing that `Trace` has infinitely many terms. -/
def traceDeltaTower : Nat → Trace
  | 0 => Trace.void
  | n + 1 => Trace.delta (traceDeltaTower n)

theorem traceDeltaTower_injective : Function.Injective traceDeltaTower := by
  intro m n h
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ n => cases h
  | succ m ih =>
      cases n with
      | zero => cases h
      | succ n =>
          exact congrArg Nat.succ (ih (Trace.delta.inj h))

/-- KO7 syntax is genuinely infinite, not merely equipped with one injective endomap. -/
theorem trace_has_infinite_carrier : Infinite Trace :=
  Infinite.of_injective traceDeltaTower traceDeltaTower_injective

/-- `merge` is an injective pairing constructor on KO7 syntax. -/
theorem trace_has_injective_pairing :
    ∃ m : Trace → Trace → Trace,
      Function.Injective (fun p : Trace × Trace => m p.1 p.2) := by
  refine ⟨Trace.merge, ?_⟩
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  exact Prod.ext (Trace.merge.inj h).1 (Trace.merge.inj h).2

/-- **The fence, stated once.** The bare schema is inhabited and does not force any of the three
extra structures. KO7 syntax supplies infinite generation and injective pairing, while the guarded
KO7 root relation supplies the actual parameterized equality query. -/
theorem diagonal_fork_schema_fence :
    Nonempty SchemaSupplies
      ∧ tinyFork.exitA ≠ tinyFork.exitB
      ∧ ¬ HasEqualityQuery tinyFork
      ∧ ¬ HasInjectivePairing tinyFork
      ∧ ¬ HasInfiniteCarrier tinyFork
      ∧ (¬ ∀ X : SchemaSupplies, HasEqualityQuery X)
      ∧ (¬ ∀ X : SchemaSupplies, HasInjectivePairing X)
      ∧ (¬ ∀ X : SchemaSupplies, HasInfiniteCarrier X)
      ∧ KO7ParameterizedEqualityQuery
      ∧ Infinite Trace
      ∧ ∃ m : Trace → Trace → Trace,
          Function.Injective (fun p : Trace × Trace => m p.1 p.2) :=
  ⟨⟨tinyFork⟩, tinyFork.exits_differ, schema_lacks_equality_query,
    schema_lacks_injective_pairing, schema_lacks_infinite_generation,
    diagonalForkSchema_does_not_force_equality_query,
    diagonalForkSchema_does_not_force_injective_pairing,
    diagonalForkSchema_does_not_force_infinite_carrier,
    ko7_guarded_equality_query, trace_has_infinite_carrier, trace_has_injective_pairing⟩

end OperatorKO7.Methods.DiagonalForkSchemaFence
