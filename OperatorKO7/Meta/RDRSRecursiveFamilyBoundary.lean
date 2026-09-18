import OperatorKO7.Meta.Recursor.CircularIdentity
import OperatorKO7.Meta.Recursor.PayloadGrowthBlindness

/-!
# RDRS Recursive-Family Boundary (FOUNDATIONAL; unconditional)

This module lands the foundational unconditional boundary theorem for
step-duplicating recursive families inside the RDRS termination-method
universe. It composes the W17.1 structural-identity layer
(`Meta/Recursor/CircularIdentity.lean`) and the W17.2 payload-growth-
blindness layer (`Meta/Recursor/PayloadGrowthBlindness.lean`) into a
single named boundary that downstream cluster modules — escape
catalog, escape characterization, family closeout — extend.

## What the boundary partitions

A step-duplicating recursive family is parameterised by a base
trace `b : Trace` and a step trace `s : Trace`; its orbit at
counter depth `n` is `recΔ b s (counterTrace n)`. A direct-measure
proof system that satisfies the standard `delta` / `recΔ` / `merge`
unit-cost equations is on the "outside" side of the boundary:
the orbit mass is `LinearGrowth` and therefore cannot be strictly
decreased by mass alone, which is the orientation requirement.

Any DM that escapes the boundary necessarily violates at least one
of the three unit-cost equations — equivalently, it privileges some
coordinate (the DP projection on the counter coordinate is the
canonical example; cf. `Meta/Recursor/DPConfessionLicenseUnconditional.lean`).

## Statement (unconditional, baseline-only)

`rdrs_recursive_family_boundary_unconditional` : every
`RecursiveFamily` is outside the uniform-cost direct-measure
orientation boundary. The proof is direct composition of the
linear-mass lemmas of W17.1; no `sorry`, no `axiom`, no
`native_decide`, no `@[csimp]`, no `unsafe`, no `partial`, no
`opaque` introduced.

Companion theorem
`recursiveFamily_indistinguishable_from_circular_reference` lifts
W17.2's `MassIndistinguishable` to the family level: every family
is mass-indistinguishable from any circular-reference orbit under
any uniform-cost DM. This is the operational-inexpressibility
content for the family layer.

Downstream cluster modules (escape catalog, escape characterization,
recursive-family closeout) extend the `RecursiveFamilyBoundaryCatalog`
carrier; its boundary-witness field is discharged automatically from
the unconditional theorem above, so adding a named family to a
catalog is a one-line definitional extension.

## Audit-slot record

- Citation chain (downstream consumers will extend):
    CircularIdentity (W17.1) + PayloadGrowthBlindness (W17.2)
      → RDRSRecursiveFamilyBoundary (this module; foundational)
        → RDRSRecursiveFamilyEscapeCatalog (future; built on this)
          → RDRSRecursiveFamilyEscapeCharacterization (future)
            → RDRSRecursiveFamilyCloseoutCatalog (future)
- Trust surface: kernel-only. Composes already-baseline theorems.
- Audit anchor (Sup A flips placeholder → verified post-review):
    `audit_theory_expansion_recursive_family_boundary_module_anchor`
-/

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.PayloadGrowthBlindness

namespace OperatorKO7.Meta.RDRSRecursiveFamilyBoundary

/-- A step-duplicating recursive family carrier. Parameterised by a
base trace `b` and a step trace `s`; the orbit at counter depth `n`
is `recΔ b s (counterTrace n)` (see `recursorOrbitOf` below).
This carrier is the substrate downstream cluster modules consume. -/
structure RecursiveFamily where
  base : Trace
  step : Trace

namespace RecursiveFamily

/-- Step-duplicator base / step convenience constructor. -/
def mk' (b s : Trace) : RecursiveFamily := { base := b, step := s }

end RecursiveFamily

/-- The orbit of a recursive family at counter depth `n`: literally
`recΔ F.base F.step (counterTrace n)`, the W17.1 `RecursorOrbit`
specialised to this family's parameters. -/
def recursorOrbitOf (F : RecursiveFamily) (n : Nat) : Trace :=
  RecursorOrbit F.base F.step n

/-- A uniform-cost direct-measure proof system bundles a
`DirectMeasureProofSystem` together with the three standard
unit-cost equations on `delta`, `recΔ`, and `merge`. Any whole-term
direct measure that treats every constructor uniformly satisfies
these equations on its image. The Dependency-Pair projection
explicitly does NOT satisfy them — it privileges the recursor's
counter coordinate (`Meta/Recursor/DPConfessionLicenseUnconditional.lean`).
The recursive-family boundary lives precisely at the boundary
between DMs that DO satisfy these equations (mass-blind side) and
DMs that DO NOT (escape side). -/
structure UniformCostDirectMeasure where
  system : DirectMeasureProofSystem
  mu_delta : ∀ t : Trace, system.mu (delta t) = system.mu t + 1
  mu_rec : ∀ b s u : Trace, system.mu (recΔ b s u) = system.mu u + 1
  mu_merge : ∀ x y : Trace, system.mu (merge x y) = system.mu x + system.mu y + 1

/-- A recursive family is OUTSIDE the direct-measure orientation
boundary under uniform-cost interpretations iff, for every uniform-
cost DM, the orbit mass satisfies `LinearGrowth`. Equivalently: mass
alone cannot strictly decrease along the orbit, so the family cannot
be oriented by any uniform-cost DM. -/
def IsOutsideDirectMeasureBoundary (F : RecursiveFamily) : Prop :=
  ∀ U : UniformCostDirectMeasure,
    LinearGrowth (fun n => U.system.mu (recursorOrbitOf F n))

/-- The whole-term mass of `F`'s orbit under any uniform-cost DM
equals `n + mu void + 1`. Direct unfolding of `recursorOrbitOf` and
`mu_counterTrace`. -/
theorem mu_recursorOrbitOf
    (F : RecursiveFamily) (U : UniformCostDirectMeasure) (n : Nat) :
    U.system.mu (recursorOrbitOf F n) = n + U.system.mu void + 1 := by
  show U.system.mu (recΔ F.base F.step (counterTrace n)) = _
  rw [U.mu_rec, mu_counterTrace U.system.mu U.mu_delta n]

/-- For every recursive family, the orbit mass under any uniform-cost
DM is `LinearGrowth` with slope `1` and intercept `mu void + 1`.
Direct compositional corollary of `mu_recursorOrbitOf`. -/
theorem recursiveFamily_orbit_is_linear_under_uniform_cost
    (F : RecursiveFamily) (U : UniformCostDirectMeasure) :
    LinearGrowth (fun n => U.system.mu (recursorOrbitOf F n)) := by
  refine ⟨1, U.system.mu void + 1, ?_⟩
  intro n
  show U.system.mu (recursorOrbitOf F n) = 1 * n + (U.system.mu void + 1)
  rw [mu_recursorOrbitOf F U n]
  omega

/-- **UNCONDITIONAL FOUNDATIONAL THEOREM.** Every step-duplicating
recursive family is OUTSIDE the direct-measure orientation boundary
under uniform-cost whole-term interpretations: for every uniform-
cost direct-measure proof system, the orbit mass satisfies
`LinearGrowth`. The orbit cannot be oriented by mass alone; the
family is structurally indistinguishable from a circular reference
under any such DM.

This is the foundational substrate downstream cluster modules
(escape catalog, escape characterization, closeout) extend. -/
theorem rdrs_recursive_family_boundary_unconditional :
    ∀ F : RecursiveFamily, IsOutsideDirectMeasureBoundary F := by
  intro F U
  exact recursiveFamily_orbit_is_linear_under_uniform_cost F U

/-- Companion theorem: every recursive family's orbit is mass-
indistinguishable from any circular-reference orbit under any
uniform-cost DM. Lifts W17.2's `MassIndistinguishable` to the
family level. Operationally: the recursor is structurally
indistinguishable from a circular reference under the boundary's
mass-blind DMs. -/
theorem recursiveFamily_indistinguishable_from_circular_reference
    (F : RecursiveFamily) (A B : Trace) (U : UniformCostDirectMeasure) :
    MassIndistinguishable
      (fun n => U.system.mu (recursorOrbitOf F n))
      (fun n => U.system.mu (CircularReferenceOrbit A B n)) := by
  refine ⟨?_, ?_⟩
  · exact recursiveFamily_orbit_is_linear_under_uniform_cost F U
  · exact circular_orbit_mu_is_linear A B U.system.mu U.mu_merge

/-- A boundary catalog for the recursive-family cluster.
Downstream modules (escape catalog, escape characterization,
closeout) extend this with named families paired with the
universal boundary witness. The witness field is discharged by
the unconditional boundary theorem above, so adding a named
family to a catalog is a one-line definitional extension. -/
structure RecursiveFamilyBoundaryCatalog where
  families : List RecursiveFamily
  boundary_witness :
    ∀ F : RecursiveFamily, F ∈ families → IsOutsideDirectMeasureBoundary F

/-- The empty boundary catalog. Provides the base case for the
downstream cluster's inductive extensions. -/
def emptyRecursiveFamilyBoundaryCatalog : RecursiveFamilyBoundaryCatalog where
  families := []
  boundary_witness := by
    intro F hF
    cases hF

/-- Build a boundary catalog from any finite list of recursive
families. The witness is the unconditional theorem applied
pointwise; no per-family proof obligation. This is the helper
downstream cluster modules invoke. -/
def recursiveFamilyBoundaryCatalogOfList
    (fs : List RecursiveFamily) : RecursiveFamilyBoundaryCatalog where
  families := fs
  boundary_witness := fun F _ =>
    rdrs_recursive_family_boundary_unconditional F

/-- The size of the catalog. Trivial accessor exposed for the
downstream cluster's cardinality lemmas. -/
def RecursiveFamilyBoundaryCatalog.size
    (C : RecursiveFamilyBoundaryCatalog) : Nat :=
  C.families.length

@[simp] theorem emptyRecursiveFamilyBoundaryCatalog_size :
    emptyRecursiveFamilyBoundaryCatalog.size = 0 := rfl

@[simp] theorem recursiveFamilyBoundaryCatalogOfList_size
    (fs : List RecursiveFamily) :
    (recursiveFamilyBoundaryCatalogOfList fs).size = fs.length := rfl

/-- Every catalog's families satisfy the boundary witness — restated
as a direct corollary so downstream consumers can dispatch a single
`IsOutsideDirectMeasureBoundary` query through the catalog API
without re-proving the universal theorem. -/
theorem RecursiveFamilyBoundaryCatalog.member_isOutsideBoundary
    (C : RecursiveFamilyBoundaryCatalog) (F : RecursiveFamily)
    (hF : F ∈ C.families) :
    IsOutsideDirectMeasureBoundary F :=
  C.boundary_witness F hF

end OperatorKO7.Meta.RDRSRecursiveFamilyBoundary
