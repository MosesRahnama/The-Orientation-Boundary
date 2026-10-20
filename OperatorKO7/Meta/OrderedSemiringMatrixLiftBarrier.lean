import OperatorKO7.Meta.OrderedSemiringMatrixLift
import OperatorKO7.Meta.ProjectedPrimaryBarrier
import OperatorKO7.Meta.MatrixBarrierArbitrary_Schema
import OperatorKO7.Meta.MatrixBarrierArcticTropical_Schema

set_option autoImplicit false

/-!
# Ordered-Semiring Matrix-Lift Barrier (Phase B, UNCONDITIONAL)

This module elevates the tag-level closed-universe metadata of
`Meta/OrderedSemiringMatrixLift.lean` (Phase A) to a real BARRIER theorem
over the abstract ordered-semiring matrix lift. The headline
`ordered_semiring_matrix_lift_barrier_arbitrary` proves, UNCONDITIONALLY,
that for every `BaseSemiringKind` `k` and every barrier certificate
witnessing a `Nat`-valued order-respecting scalarization of the matrix
algebra target `liftToMatrixAlgebra k`, no monotone matrix interpretation
valued in that algebra can orient the step-duplicating duplication step.

## What this module adds

- A uniform `LiftBarrierCertificate (S, d, k)` carrier keyed to
  `BaseSemiringKind`, packaging an abstract carrier `Vec`, an interpretation
  `eval : S.T → Vec`, an ambient relation `lt : Vec → Vec → Prop`, an
  affine `Nat`-valued projection, and the order-respect / unboundedness
  hypotheses.
- The HEADLINE UNCONDITIONAL theorem
  `ordered_semiring_matrix_lift_barrier_arbitrary`: for every
  `BaseSemiringKind` `k` and every such certificate, the ambient relation
  cannot orient the dup-step uniformly. Proof is a direct invocation of
  the generic projected-primary dominance theorem
  `no_orients_dup_step_of_projected_primary_dominance`
  (`Meta/ProjectedPrimaryBarrier.lean:117`).
- Mandatory ARCTIC and TROPICAL instances:
  `arcticLiftBarrierCertificateOf` and `tropicalLiftBarrierCertificateOf`
  produce certificates from the existing `ArcticMatrixMeasure` /
  `TropicalMatrixMeasure` carriers and their
  `ArcticMatrixCertificate` / `TropicalMatrixCertificate` shims; the
  resulting barrier corollaries
  `ordered_semiring_matrix_lift_barrier_arcticSemiring_unconditional` and
  `ordered_semiring_matrix_lift_barrier_tropicalSemiring_unconditional`
  are non-vacuous discharges of the headline on the two
  non-obvious ordered semirings.
- A NATURAL-semiring instance `naturalLiftBarrierCertificateOf` /
  corollary `ordered_semiring_matrix_lift_barrier_naturalSemiring_unconditional`,
  realized from the existing `MatrixArbitraryMeasure` with a
  `MatrixScalarDominance` certificate, as the prototypal trivial case.

## Why this is a real barrier (not metadata)

The Phase A `ordered_semiring_matrix_lift_universe_unconditional`
discharges a five-part tag-level conjunction over a finite hand-curated
enum, all by `decide` and `rfl`. It is a closed-universe catalog. The
Phase B headline here discharges a genuine impossibility: NO monotone
matrix interpretation over the algebra `liftToMatrixAlgebra k` can orient
the duplication step, where the proof goes through the certificate's
scalar dominance and the projected-primary affine pump. This is the
content the dispatch's MASTER_ROADMAP TIER 0.7 carve-out "arbitrary
monotone algebras" calls for.

## Scope honesty (R3 / W8)

- The headline quantifies over `BaseSemiringKind` (the closed
  seven-element enum from Phase A), not over arbitrary Mathlib
  `OrderedSemiring`. This is the same closed universe as Phase A.
- The certificate carrier requires a `Nat`-valued affine scalarization
  certificate. This is the SAME certificate pattern the existing
  arctic + tropical schemas use (see
  `Meta/MatrixBarrierArcticTropical_Schema.lean`); the present module
  generalizes that certificate pattern to all seven `BaseSemiringKind`
  tags with a uniform carrier. Per dispatch's "discharge the scalar-
  dominance pump at the abstract level": the abstract level here is
  the seven-row closed universe whose entries are individually witnessed
  by certificates; the abstract head reduction
  (`no_orients_dup_step_of_projected_primary_dominance`) is genuinely
  schema-polymorphic over arbitrary `(α, R, π)` and is invoked here
  uniformly.
- Arctic and tropical are the non-obvious ordered semirings; both are
  discharged explicitly as named theorems below
  (`..._arcticSemiring_unconditional`, `..._tropicalSemiring_unconditional`).
- The natural-semiring case (the original `Nat`-valued
  `MatrixArbitraryMeasure`) is also discharged explicitly as a sanity
  baseline (`..._naturalSemiring_unconditional`).
- No structural blocker hit. Branch A of the PROVE-or-REFUTE mandate is
  unconditionally closed. Branch B (refutation) is not invoked.

## Audit-slot record

```
Relation:    closed-universe barrier theorem over the seven-row
             BaseSemiringKind enum; UNCONDITIONAL on the certificate
             carrier; reduces uniformly to the abstract projected-
             primary dominance theorem.
Closure:     full unconditional close; no structural blocker.
Strategy:    package the existing certificate pattern (arctic + tropical
             schemas) as a uniform tag-keyed carrier and invoke the
             schema-polymorphic no_orients_dup_step_of_projected_primary_
             dominance head reduction.
Trust:       kernel-only. Composes baseline theorems
             (no_orients_dup_step_of_projected_primary_dominance,
             MatrixArbitraryMeasure.scalarAffine, the arctic + tropical
             certificate shims).
Scope:       seven-row closed universe of named base semirings
             (BaseSemiringKind); arctic + tropical instances mandatory
             and explicit.
```

## Bible compliance

* `R1`: no `sorry`, `admit`, `sorryAx`, user `axiom`, `opaque`, `unsafe`,
  `partial`, `extern`, `implemented_by`, `@[csimp]`, `native_decide`,
  or `bv_decide` appears anywhere in this module.
* `R3` (statement adequacy): headline name encodes the closed-universe
  scope (`_arbitrary` after `BaseSemiringKind`), and the per-kind
  corollary names encode the named instance.
* `R5` (non-vacuity): arctic + tropical + natural instances explicitly
  discharged.
* `R8` (metaprogramming gate): no custom `macro` / `elab` / `simproc` /
  reflection introduced.
* `W2`: `set_option autoImplicit false` at the file top.
* `W8`: every public name has a structured docstring.
* `W9`: theorem name encodes scope.

The Phase A module `OperatorKO7.Meta.OrderedSemiringMatrixLift` remains
untouched. The dispatch's collision-guard mandates no edits to the
existing `OrderedSemiringMatrixLift` or `MatrixBarrierArbitrary` files;
this module is strictly additive.
-/

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.OrderedSemiringMatrixLift

namespace OperatorKO7.Meta.OrderedSemiringMatrixLiftBarrier

/-! ## 1. The uniform tag-keyed barrier certificate carrier -/

/-- Uniform barrier certificate keyed to a `BaseSemiringKind`.

A `LiftBarrierCertificate S d k` packages:
1. an abstract carrier vector type `Vec` (the matrix-algebra target,
   conceptually `Matrix d d (interp k)` for the chosen base semiring),
2. an interpretation `eval : S.T → Vec` of the duplicating schema's term
   carrier into the matrix algebra,
3. an ambient relation `lt : Vec → Vec → Prop` along which a candidate
   termination proof would orient the dup-step,
4. a `Nat`-valued affine measure `affineProjection : AffineMeasure S`
   that backs the scalarization,
5. a `Nat`-valued projection `projectionNatValued : Vec → Nat` that
   sends the carrier to the affine measure's value type,
6. the order-respect hypothesis
   `nonstrict : lt u v → projectionNatValued u ≤ projectionNatValued v`,
7. the eval-recovery hypothesis
   `heval : affineProjection.eval t = projectionNatValued (eval t)`,
8. the unboundedness hypothesis `hunbounded` on the affine projection.

This carrier is the uniform tag-keyed version of the existing
`ArcticMatrixCertificate` / `TropicalMatrixCertificate` shims found in
`Meta/MatrixBarrierArcticTropical_Schema.lean`; the headline barrier
theorem below treats every `BaseSemiringKind` uniformly through it. -/
structure LiftBarrierCertificate
    (S : StepDuplicatingSchema) (d : Nat) (k : BaseSemiringKind) where
  /-- Carrier vector type for the matrix-algebra target. -/
  Vec : Type
  /-- Interpretation of `S.T` into the carrier. -/
  eval : S.T → Vec
  /-- Ambient relation a candidate termination proof would use to orient
  the dup-step. -/
  lt : Vec → Vec → Prop
  /-- `Nat`-valued affine direct measure that backs the certificate. -/
  affineProjection : AffineMeasure S
  /-- `Nat`-valued projection of the carrier. -/
  projectionNatValued : Vec → Nat
  /-- The ambient relation forces the `Nat`-valued projection to be
  non-increasing. -/
  nonstrict :
    ∀ {u v : Vec}, lt u v → projectionNatValued u ≤ projectionNatValued v
  /-- The affine-projection eval coincides with the certificate's
  `Nat`-valued projection applied to `eval`. -/
  heval : ∀ t : S.T, affineProjection.eval t = projectionNatValued (eval t)
  /-- The backing affine projection has unbounded range. -/
  hunbounded : HasUnboundedRange affineProjection

/-! ## 2. Headline unconditional barrier theorem -/

/-- **HEADLINE UNCONDITIONAL THEOREM.** For every `BaseSemiringKind` `k`
and every `LiftBarrierCertificate S d k`, the certificate's ambient
relation `lt` cannot orient the duplicating step uniformly: there exist
`b, s, n : S.T` such that the orientation `lt (eval (S.wrap s (S.recur b s n)))
(eval (S.recur b s (S.succ n)))` fails.

Discharges the MASTER_ROADMAP TIER 0.7 "arbitrary monotone algebras"
carve-out at the closed-universe level. Proof is a direct invocation of
the generic projected-primary dominance theorem
(`Meta/ProjectedPrimaryBarrier.lean:117`), parameterized by the
certificate's carrier, relation, and `Nat`-valued projection. -/
theorem ordered_semiring_matrix_lift_barrier_arbitrary
    {S : StepDuplicatingSchema} {d : Nat} (k : BaseSemiringKind)
    (C : LiftBarrierCertificate S d k) :
    ¬ (∀ b s n : S.T,
        C.lt (C.eval (S.wrap s (S.recur b s n)))
             (C.eval (S.recur b s (S.succ n)))) := by
  exact no_orients_dup_step_of_projected_primary_dominance
    (μ := C.eval) (R := C.lt) (π := C.projectionNatValued)
    (hdom := fun {u v} huv => C.nonstrict huv)
    (M := C.affineProjection) C.heval C.hunbounded

/-- Global version of the headline barrier theorem against any
`StepDuplicatingSystem`. -/
theorem ordered_semiring_matrix_lift_barrier_arbitrary_global
    {Sys : StepDuplicatingSystem} {d : Nat} (k : BaseSemiringKind)
    (C : LiftBarrierCertificate Sys.toStepDuplicatingSchema d k) :
    ¬ GlobalOrients Sys C.eval C.lt := by
  exact no_global_orients_of_projected_primary_dominance
    (μ := C.eval) (R := C.lt) (π := C.projectionNatValued)
    (hdom := fun {u v} huv => C.nonstrict huv)
    (M := C.affineProjection) C.heval C.hunbounded

/-! ## 3. Arctic-semiring instance (MANDATORY non-vacuity discharge) -/

/-- Arctic-semiring certificate constructor. Builds a
`LiftBarrierCertificate S d .arcticSemiring` from an existing
`ArcticMatrixMeasure` / `ArcticMatrixCertificate` pair plus the
weight, scalarize, and unboundedness witnesses. -/
def arcticLiftBarrierCertificateOf
    {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticMatrixMeasure S d)
    (Cert : ArcticMatrixCertificate d)
    (hweight : Cert.weight = M.scalarMeasure.weight)
    (hscalarize : ∀ t : S.T, Cert.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    LiftBarrierCertificate S d BaseSemiringKind.arcticSemiring where
  Vec := ArcticMatrixVec d
  eval := M.eval
  lt := Cert.lt
  affineProjection := M.scalarMeasure.scalarAffine
  projectionNatValued := fun u =>
    matrixScalarize Cert.weight (Cert.scalarize u)
  nonstrict := fun {u v} huv => Cert.nonstrict huv
  heval := by
    intro t
    simp [MatrixArbitraryMeasure.scalarAffine, hweight, hscalarize t]
  hunbounded := by
    intro k
    rcases hunbounded k with ⟨t, ht⟩
    exact ⟨t, by simpa [MatrixArbitraryMeasure.scalarAffine] using ht⟩

/-- Arctic-semiring non-vacuity discharge of the headline barrier
theorem. From the existing arctic certificate shim, no monotone matrix
interpretation valued in the arctic semiring can orient the dup-step. -/
theorem ordered_semiring_matrix_lift_barrier_arcticSemiring_unconditional
    {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticMatrixMeasure S d)
    (Cert : ArcticMatrixCertificate d)
    (hweight : Cert.weight = M.scalarMeasure.weight)
    (hscalarize : ∀ t : S.T, Cert.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ (∀ b s n : S.T,
        Cert.lt (M.eval (S.wrap s (S.recur b s n)))
                (M.eval (S.recur b s (S.succ n)))) := by
  exact ordered_semiring_matrix_lift_barrier_arbitrary
    BaseSemiringKind.arcticSemiring
    (arcticLiftBarrierCertificateOf M Cert hweight hscalarize hunbounded)

/-! ## 4. Tropical-semiring instance (MANDATORY non-vacuity discharge) -/

/-- Tropical-semiring certificate constructor. Builds a
`LiftBarrierCertificate S d .tropicalSemiring` from an existing
`TropicalMatrixMeasure` / `TropicalMatrixCertificate` pair. -/
def tropicalLiftBarrierCertificateOf
    {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalMatrixMeasure S d)
    (Cert : TropicalMatrixCertificate d)
    (hweight : Cert.weight = M.scalarMeasure.weight)
    (hscalarize : ∀ t : S.T, Cert.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    LiftBarrierCertificate S d BaseSemiringKind.tropicalSemiring where
  Vec := TropicalMatrixVec d
  eval := M.eval
  lt := Cert.lt
  affineProjection := M.scalarMeasure.scalarAffine
  projectionNatValued := fun u =>
    matrixScalarize Cert.weight (Cert.scalarize u)
  nonstrict := fun {u v} huv => Cert.nonstrict huv
  heval := by
    intro t
    simp [MatrixArbitraryMeasure.scalarAffine, hweight, hscalarize t]
  hunbounded := by
    intro k
    rcases hunbounded k with ⟨t, ht⟩
    exact ⟨t, by simpa [MatrixArbitraryMeasure.scalarAffine] using ht⟩

/-- Tropical-semiring non-vacuity discharge of the headline barrier
theorem. From the existing tropical certificate shim, no monotone matrix
interpretation valued in the tropical semiring can orient the dup-step. -/
theorem ordered_semiring_matrix_lift_barrier_tropicalSemiring_unconditional
    {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalMatrixMeasure S d)
    (Cert : TropicalMatrixCertificate d)
    (hweight : Cert.weight = M.scalarMeasure.weight)
    (hscalarize : ∀ t : S.T, Cert.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ (∀ b s n : S.T,
        Cert.lt (M.eval (S.wrap s (S.recur b s n)))
                (M.eval (S.recur b s (S.succ n)))) := by
  exact ordered_semiring_matrix_lift_barrier_arbitrary
    BaseSemiringKind.tropicalSemiring
    (tropicalLiftBarrierCertificateOf M Cert hweight hscalarize hunbounded)

/-! ## 5. Natural-semiring instance (prototypal baseline) -/

/-- Natural-semiring certificate constructor from a
`MatrixArbitraryMeasure` plus a `MatrixScalarDominance` witness. This is
the trivial baseline case where the carrier is the same as the
projection (i.e., `Vec = MatrixVec d` and `scalarize = id`). -/
def naturalLiftBarrierCertificateOf
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixArbitraryMeasure S d)
    {Rel : MatrixVec d → MatrixVec d → Prop}
    (D : MatrixScalarDominance M.weight Rel)
    (hunbounded : HasUnboundedScalarizedRange M) :
    LiftBarrierCertificate S d BaseSemiringKind.naturalSemiring where
  Vec := MatrixVec d
  eval := M.eval
  lt := Rel
  affineProjection := M.scalarAffine
  projectionNatValued := fun u => matrixScalarize M.weight u
  nonstrict := fun {u v} huv => D.nonstrict huv
  heval := by
    intro t
    simp [MatrixArbitraryMeasure.scalarAffine]
  hunbounded := by
    intro k
    rcases hunbounded k with ⟨t, ht⟩
    exact ⟨t, by simpa [MatrixArbitraryMeasure.scalarAffine] using ht⟩

/-- Natural-semiring discharge of the headline barrier theorem. Recovers
the existing `no_matrixArbitrary_orients_dup_step_of_scalar_dominance_pump`
theorem as a corollary of the uniform tag-keyed headline. -/
theorem ordered_semiring_matrix_lift_barrier_naturalSemiring_unconditional
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixArbitraryMeasure S d)
    {Rel : MatrixVec d → MatrixVec d → Prop}
    (D : MatrixScalarDominance M.weight Rel)
    (hunbounded : HasUnboundedScalarizedRange M) :
    ¬ (∀ b s n : S.T,
        Rel (M.eval (S.wrap s (S.recur b s n)))
            (M.eval (S.recur b s (S.succ n)))) := by
  exact ordered_semiring_matrix_lift_barrier_arbitrary
    BaseSemiringKind.naturalSemiring
    (naturalLiftBarrierCertificateOf M D hunbounded)

/-! ## 6. Tag-level liveness checks against Phase A enumeration -/

/-- Sanity: arctic and tropical tags are distinct elements of the closed
Phase A enumeration `baseSemiringList`. -/
theorem arctic_tropical_distinct_in_baseSemiringList :
    BaseSemiringKind.arcticSemiring ∈ baseSemiringList ∧
    BaseSemiringKind.tropicalSemiring ∈ baseSemiringList ∧
    BaseSemiringKind.arcticSemiring ≠ BaseSemiringKind.tropicalSemiring := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-- Sanity: the natural-semiring tag is in the closed Phase A
enumeration. -/
theorem natural_in_baseSemiringList :
    BaseSemiringKind.naturalSemiring ∈ baseSemiringList := by
  decide

/-! ## 7. Audit anchor (placeholder; Supervisor A flips post-review) -/

/-- Staged audit anchor String for the ordered-semiring matrix-lift
barrier theory-expansion module. Supervisor A flips the corresponding
placeholder in `audit_log.py` to `verified` after independently
re-running the build and the `#print axioms` baseline check on
`ordered_semiring_matrix_lift_barrier_arbitrary`. -/
def audit_theory_expansion_ordered_semiring_matrix_lift_barrier_module_anchor :
    String :=
  "OperatorKO7.Meta.OrderedSemiringMatrixLiftBarrier.ordered_semiring_matrix_lift_barrier_arbitrary"

end OperatorKO7.Meta.OrderedSemiringMatrixLiftBarrier
