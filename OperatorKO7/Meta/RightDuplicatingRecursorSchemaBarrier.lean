import OperatorKO7.Meta.RightDuplicatingRecursorSchema
import OperatorKO7.Meta.Recursor.CircularIdentity
import OperatorKO7.Meta.Recursor.PayloadGrowthBlindness
import OperatorKO7.Meta.RDRSRecursiveFamilyBoundary

/-!
# Right-Duplicating Recursor Schema, Barrier / Escape Classification (Phase B)

UNCONDITIONAL barrier-side classification for the Phase A right-duplicating
recursor schema (the recursor variant whose rewrite duplicates the
distinguished payload on its right argument). Strictly additive on top of
the already-landed Phase A shell
(`OperatorKO7.StepDuplicating.RightDuplicatingRecursorSchema`) and the
W17.1 / W17.2 / `RDRSRecursiveFamilyBoundary` substrate (Brief C-065).

## What this module adds

- A canonical KO7-Trace embedding `schemaToRecursiveFamily : S → b → s →
  RecursiveFamily`, sending each Phase A schema (paired with base/step
  traces) to the corresponding RDRS recursive family.
- A schema-level barrier predicate `IsOutsideBoundaryFor S`: every base/step
  pair `(b, s)` sends `S` to an `IsOutsideDirectMeasureBoundary` family.
- The HEADLINE UNCONDITIONAL theorem
  `right_duplicating_recursor_schema_unconditional`: every Phase A
  right-duplicating recursor schema is outside the uniform-cost direct-
  measure orientation boundary, mass alone cannot orient any orbit derived
  from the schema, regardless of the abstract count function the schema
  carries.
- A companion W17.2 lift
  `schema_orbit_indistinguishable_from_circular_reference`: every schema's
  KO7 orbit is mass-indistinguishable from any circular-reference orbit
  under any uniform-cost direct measure.
- A barrier catalog carrier
  (`RightDuplicatingRecursorSchemaBarrierCatalog`) for downstream cluster
  modules (escape catalog, schema closeout) to extend without re-deriving
  the universal theorem.

## What this module deliberately does NOT touch

- The Phase A shell itself remains untouched. The
  `OperatorKO7.StepDuplicating` namespace is unchanged.
- The escape side of the classification (DP projection on the counter
  coordinate, the canonical violator of the uniform-cost equations) lives
  in `Meta/Recursor/DPConfessionLicenseUnconditional.lean` and is
  referenced by docstring only, no co-modification.
- No aggregator import line is added; the reach test imports this module
  directly and `lake build OperatorKO7` is unaffected.

## Audit-slot record

- Citation chain (downstream consumers extend through the catalog):
    PayloadDiscarding (Axiom 5)
      then CircularIdentity (W17.1)
        then PayloadGrowthBlindness (W17.2)
          then RDRSRecursiveFamilyBoundary (Brief C-065, foundational)
            then RightDuplicatingRecursorSchema (Phase A, pre-existing)
              then RightDuplicatingRecursorSchemaBarrier (this module, Phase B)
- Trust surface: kernel only. Strict composition of already-baseline
  theorems.
- Audit anchor
  `audit_theory_expansion_right_duplicating_recursor_schema_module_anchor`
  remains under Supervisor A control. The Phase A shell's verification
  record is preserved unchanged.
- No `sorry`, no user `axiom`, no `native_decide`, no `@[csimp]`, no
  `unsafe`, no `partial`, no `opaque` introduced on any load-bearing decl.
-/

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.Meta.Recursor.CircularIdentity
open OperatorKO7.Meta.Recursor.PayloadGrowthBlindness
open OperatorKO7.Meta.RDRSRecursiveFamilyBoundary

namespace OperatorKO7.Meta.RightDuplicatingRecursorSchemaBarrier

/-- KO7-Trace embedding of a Phase A right-duplicating recursor schema.
Given any schema `S` and a choice of base / step traces `(b, s)`, build the
corresponding RDRS `RecursiveFamily`. The schema parameter `S` carries the
abstract count-asymmetry data (`S.distinguishedDuplicationGap` is at least
one), but the boundary theorem at the KO7 Trace level only requires the
base/step traces, the schema's abstract count function does not need to be
transported into the Trace algebra to land the unconditional barrier. -/
def schemaToRecursiveFamily
    (_S : RightDuplicatingRecursorSchema) (b s : Trace) : RecursiveFamily :=
  RecursiveFamily.mk' b s

/-- Schema-level barrier predicate. Every base/step pair sends the schema to
an `IsOutsideDirectMeasureBoundary` family. This is the schema-level lift of
the family-level boundary predicate established in
`RDRSRecursiveFamilyBoundary`. -/
def IsOutsideBoundaryFor (S : RightDuplicatingRecursorSchema) : Prop :=
  ∀ b s : Trace, IsOutsideDirectMeasureBoundary (schemaToRecursiveFamily S b s)

/-- HEADLINE UNCONDITIONAL THEOREM. Every right-duplicating recursor schema
is outside the uniform-cost direct-measure orientation boundary: for every
base/step choice and every uniform-cost direct-measure proof system, the
orbit mass satisfies `LinearGrowth` and the orbit cannot be oriented by
mass alone.

The proof composes the RDRS Recursive-Family Boundary theorem
(`rdrs_recursive_family_boundary_unconditional`, Brief C-065) through the
canonical embedding. The schema's abstract count asymmetry
(`S.rhs_duplicates_payload`, `S.lhs_has_payload`) is what makes this
classification non-trivial in general, the unconditional content survives
even without invoking those count constraints inside the proof because the
KO7 recursor `recΔ` already realizes the right-duplication phenomenon at
the trace level, every base/step instance is on the barrier side. -/
theorem right_duplicating_recursor_schema_unconditional :
    ∀ S : RightDuplicatingRecursorSchema, IsOutsideBoundaryFor S := by
  intro S b s
  exact rdrs_recursive_family_boundary_unconditional (schemaToRecursiveFamily S b s)

/-- Companion (W17.2 lift). Every schema's KO7 orbit is mass-
indistinguishable from any circular-reference orbit under any uniform-cost
direct measure. -/
theorem schema_orbit_indistinguishable_from_circular_reference
    (S : RightDuplicatingRecursorSchema) (b s A B : Trace)
    (U : UniformCostDirectMeasure) :
    MassIndistinguishable
      (fun n => U.system.mu (recursorOrbitOf (schemaToRecursiveFamily S b s) n))
      (fun n => U.system.mu (CircularReferenceOrbit A B n)) :=
  recursiveFamily_indistinguishable_from_circular_reference
    (schemaToRecursiveFamily S b s) A B U

/-- Barrier catalog for the right-duplicating-recursor-schema cluster.
Downstream modules (escape catalog, schema closeout) extend this carrier
with named schemas paired with the universal barrier witness. The witness
field is discharged by the unconditional theorem above, so adding a named
schema to a catalog is a one-line definitional extension. -/
structure RightDuplicatingRecursorSchemaBarrierCatalog where
  schemas : List RightDuplicatingRecursorSchema
  barrier_witness :
    ∀ S : RightDuplicatingRecursorSchema, S ∈ schemas → IsOutsideBoundaryFor S

/-- The empty barrier catalog. Base case for inductive cluster extensions. -/
def emptyRightDuplicatingRecursorSchemaBarrierCatalog :
    RightDuplicatingRecursorSchemaBarrierCatalog where
  schemas := []
  barrier_witness := by
    intro S hS
    cases hS

/-- Build a barrier catalog from any finite list of schemas. The witness is
the unconditional theorem applied pointwise, no per-schema proof
obligation. -/
def rightDuplicatingRecursorSchemaBarrierCatalogOfList
    (Ss : List RightDuplicatingRecursorSchema) :
    RightDuplicatingRecursorSchemaBarrierCatalog where
  schemas := Ss
  barrier_witness := fun S _ =>
    right_duplicating_recursor_schema_unconditional S

/-- Cardinality of the barrier catalog. -/
def RightDuplicatingRecursorSchemaBarrierCatalog.size
    (C : RightDuplicatingRecursorSchemaBarrierCatalog) : Nat :=
  C.schemas.length

@[simp] theorem emptyRightDuplicatingRecursorSchemaBarrierCatalog_size :
    emptyRightDuplicatingRecursorSchemaBarrierCatalog.size = 0 := rfl

@[simp] theorem rightDuplicatingRecursorSchemaBarrierCatalogOfList_size
    (Ss : List RightDuplicatingRecursorSchema) :
    (rightDuplicatingRecursorSchemaBarrierCatalogOfList Ss).size = Ss.length := rfl

/-- Every catalog's listed schemas satisfy the barrier witness. Direct
corollary so downstream consumers can dispatch a single barrier query
through the catalog API without re-deriving the universal theorem. -/
theorem RightDuplicatingRecursorSchemaBarrierCatalog.member_isOutsideBoundary
    (C : RightDuplicatingRecursorSchemaBarrierCatalog)
    (S : RightDuplicatingRecursorSchema) (hS : S ∈ C.schemas) :
    IsOutsideBoundaryFor S :=
  C.barrier_witness S hS

end OperatorKO7.Meta.RightDuplicatingRecursorSchemaBarrier
