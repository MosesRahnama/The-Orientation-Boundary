import OperatorKO7.Meta.BarrierPumpDischarge_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import OperatorKO7.Meta.MatrixProjectionCoverage_Schema

set_option autoImplicit false

/-!
# KO7 specializations of the pump-discharge barrier layer

`Meta/BarrierPumpDischarge_Schema.lean` proves that the growth hypotheses carried by the
direct barrier stack (`HasUnboundedRange`, successor pumps, wrap pumps) are consequences of
the wrapper-positivity fields that every measure class already stores. This module
instantiates those schema theorems at the KO7 kernel: schema `ko7Schema`, system `ko7System`,
duplicating step `recΔ b s (delta n) → app s (recΔ b s n)`.

Every declaration here is an application of the schema theorem of the same suffix. No
hypothesis is added, and each surviving hypothesis is the load-bearing one of its family:

* nothing at all for affine, restricted quadratic, max-plus, arctic and tropical primary
  projections, tracked componentwise vectors and pairs, weighted scalar projections, and
  balanced mixed coordinates;
* a base-point dominance or boundedness condition for the cross-term quadratic, multilinear,
  polynomial, and WPO-polynomial families;
* one positive value of the tracked scalar for the families whose order only forces
  nonincrease (lexicographic pair, finite and permutation lexicographic vectors, scalar
  dominance on arbitrary mixed matrices). `zeroAffineMeasure_nonstrict_orients` shows that
  this last premise cannot be dropped.

Relation: full kernel `Step` through `ko7System`; the affine and row-sum rows use the
`MetaConjectureBoundary.GlobalOrients` interface, every other row uses
`StepDuplicatingSchema.GlobalOrients ko7System`.
Closure: root. Context-closed lifts live in `Meta/ContextClosedBarrier_PumpDischarge.lean`.
Strategy: not applicable.
Trust: kernel-only. Mathlib and the schema layer.
Scope: the KO7 duplicating rule. Nothing here claims termination or non-termination of KO7.
-/

namespace OperatorKO7.BarrierPumpDischarge

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-! ## Affine constructor-local measures -/

/--
Proves: no affine KO7 measure with positive `app` coefficients strictly orients the
duplicating rule `recΔ b s (delta n) → app s (recΔ b s n)`.
Does not prove: anything about measures whose `app` coefficients may vanish.
Relation: the KO7 duplicating rule at the root.
Trust: kernel-only.
Scope: unconditional; the unbounded-range premise of
`no_affine_compositional_orients_rec_succ_of_unbounded` is discharged by the schema layer.
-/
theorem no_affine_compositional_orients_rec_succ (M : AffineCompositionalMeasure) :
    ¬ (∀ (b s n : Trace),
      M.eval (app s (recΔ b s n)) < M.eval (recΔ b s (delta n))) := by
  intro h
  exact StepDuplicatingSchema.no_affine_orients_dup_step
    (S := ko7Schema) M.toSchemaMeasure h

/-- Unconditional affine barrier for full KO7 `Step`. -/
theorem no_global_step_orientation_affine (M : AffineCompositionalMeasure) :
    ¬ MetaConjectureBoundary.GlobalOrients M.eval (· < ·) := by
  simpa [ko7System, StepDuplicatingSchema.GlobalOrients,
    MetaConjectureBoundary.GlobalOrients, AffineCompositionalMeasure.toSchemaMeasure] using
    (StepDuplicatingSchema.no_global_orients_affine
      (Sys := ko7System) (M := M.toSchemaMeasure))

/-! ## Restricted quadratic measures -/

/-- Unconditional restricted-quadratic barrier for full KO7 `Step`. -/
theorem no_global_step_orientation_quadratic
    (M : StepDuplicatingSchema.QuadraticCounterMeasure ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) :=
  StepDuplicatingSchema.no_global_orients_quadratic (Sys := ko7System) M

/-! ## Bounded cross-term quadratic measures -/

/-- Cross-term quadratic barrier with only the base-point coupling bound left. -/
theorem no_global_step_orientation_cross_quadratic_of_bounded
    (M : StepDuplicatingSchema.CrossTermQuadraticMeasure ko7Schema)
    (hbounded : StepDuplicatingSchema.CrossTermBoundedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) :=
  StepDuplicatingSchema.no_global_orients_cross_quadratic_of_bounded
    (Sys := ko7System) M hbounded

/-! ## Bounded multilinear measures -/

/-- Multilinear barrier with only the frozen base-point dominance left. -/
theorem no_global_step_orientation_multilinear_of_dominated
    (M : StepDuplicatingSchema.BoundedMultilinearMeasure ko7Schema)
    (hdom : StepDuplicatingSchema.MultilinearDominatedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) :=
  StepDuplicatingSchema.no_global_orients_multilinear_of_dominated
    (Sys := ko7System) M hdom

/-! ## Generalized degree-bounded polynomial measures -/

/-- Polynomial barrier with only eventual frozen base-point dominance left. -/
theorem no_global_step_orientation_polynomial_of_dominated
    (M : StepDuplicatingSchema.BoundedPolynomialMeasure ko7Schema)
    (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) :=
  StepDuplicatingSchema.no_global_orients_polynomial_of_dominated
    (Sys := ko7System) M hdom

/-- Every polynomial orienter of the KO7 duplicating rule violates frozen base dominance,
with no growth premise. -/
theorem polynomial_orienter_violates_base_dominance
    (M : StepDuplicatingSchema.BoundedPolynomialMeasure ko7Schema)
    (horient : ∀ (b s n : Trace),
      M.eval (app s (recΔ b s n)) < M.eval (recΔ b s (delta n))) :
    ¬ StepDuplicatingSchema.EventuallyDominatedAtBase M :=
  StepDuplicatingSchema.polynomial_orienter_violates_base_dominance
    (S := ko7Schema) M horient

/-- WPO-facing polynomial branch with only the dominance premise left. -/
theorem no_global_step_orientation_wpoPolynomialDirect_of_dominated
    (W : StepDuplicatingSchema.WPOPolynomialDirectOrder ko7Schema)
    (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase W.measure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System (fun t => t) (fun x y => W.gt y x) :=
  StepDuplicatingSchema.no_global_orients_wpoPolynomialDirect_of_dominated
    (Sys := ko7System) W hdom

/-! ## Max-plus and its arctic and tropical primary projections -/

/-- Unconditional max-plus barrier for full KO7 `Step`. -/
theorem no_global_step_orientation_max
    (M : StepDuplicatingSchema.MaxMeasure ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) :=
  StepDuplicatingSchema.no_global_orients_max (Sys := ko7System) M

/-- Unconditional arctic primary-projection barrier for full KO7 `Step`. -/
theorem no_global_step_orientation_arctic_primary
    (M : StepDuplicatingSchema.ArcticPrimaryMeasure ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.ArcticLt := by
  intro h
  exact StepDuplicatingSchema.no_arctic_primary_orients_dup_step (S := ko7Schema) M
    (fun b s n => h (ko7System.dup_step b s n))

/-- Unconditional tropical primary-projection barrier for full KO7 `Step`. -/
theorem no_global_step_orientation_tropical_primary
    {β : Type} (M : StepDuplicatingSchema.TropicalPrimaryMeasure ko7Schema β) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval M.lt := by
  intro h
  exact StepDuplicatingSchema.no_tropical_primary_orients_dup_step (S := ko7Schema) M
    (fun b s n => h (ko7System.dup_step b s n))

/-! ## Vector and pair families -/

/-- Unconditional tracked componentwise vector barrier, any finite dimension. -/
theorem no_global_step_orientation_matrixD
    {d : Nat} {tracked : Fin d}
    (M : StepDuplicatingSchema.MatrixMeasureD ko7Schema d tracked) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.VecLt :=
  StepDuplicatingSchema.no_global_orients_matrixD (Sys := ko7System) M

/-- Unconditional tracked-primary componentwise pair barrier. -/
theorem no_global_step_orientation_matrix2
    (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.PairLt :=
  StepDuplicatingSchema.no_global_orients_matrix2 (Sys := ko7System) M

/-- Lexicographic pair barrier: one positive first component replaces the pump. -/
theorem no_global_step_orientation_matrix2_lex_of_fst_pos
    (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema)
    (hpos : ∃ t : Trace, 1 ≤ (M.eval t).1) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.PairLexLt :=
  StepDuplicatingSchema.no_global_orients_matrix2_lex_of_fst_pos (Sys := ko7System) M hpos

/-- Unconditional weighted scalar-projection barrier. -/
theorem no_global_step_orientation_matrixFunctional
    {d : Nat} (M : StepDuplicatingSchema.MatrixFunctionalMeasure ko7Schema d) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.VecLt :=
  StepDuplicatingSchema.no_global_orients_matrixFunctional (Sys := ko7System) M

/-- Unconditional balanced mixed-coordinate pair barrier. -/
theorem no_global_step_orientation_matrixMix2
    (M : StepDuplicatingSchema.MatrixMix2Measure ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.PairLt :=
  StepDuplicatingSchema.no_global_orients_matrixMix2 (Sys := ko7System) M

/-- Finite tracked-primary lexicographic vector barrier: one positive primary value. -/
theorem no_global_step_orientation_matrixLexD_of_primary_pos
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexMeasureD ko7Schema d)
    (hpos : ∃ t : Trace, 1 ≤ M.eval t (StepDuplicatingSchema.primaryIdx d)) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.VecLexLt :=
  StepDuplicatingSchema.no_global_orients_matrixLexD_of_primary_pos (Sys := ko7System) M hpos

/-- Permutation-priority lexicographic vector barrier: one positive primary value. -/
theorem no_global_step_orientation_matrixLexPermD_of_primary_pos
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexPermMeasureD ko7Schema d)
    (hpos : ∃ t : Trace,
      1 ≤ M.eval t (StepDuplicatingSchema.permPrimaryIdx M.priority)) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval
      (StepDuplicatingSchema.VecPermLexLt M.priority) :=
  StepDuplicatingSchema.no_global_orients_matrixLexPermD_of_primary_pos
    (Sys := ko7System) M hpos

/-- Scalar-dominance mixed-matrix barrier: one positive scalarized value replaces the pump. -/
theorem no_global_step_orientation_matrixArbitrary_of_scalar_dominance_of_pos
    {d : Nat} (M : StepDuplicatingSchema.MatrixArbitraryMeasure ko7Schema d)
    {R : StepDuplicatingSchema.MatrixVec d → StepDuplicatingSchema.MatrixVec d → Prop}
    (D : StepDuplicatingSchema.MatrixScalarDominance M.weight R)
    (hpos : ∃ t : Trace,
      1 ≤ StepDuplicatingSchema.matrixScalarize M.weight (M.eval t)) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval R :=
  StepDuplicatingSchema.no_global_orients_matrixArbitrary_of_scalar_dominance_of_pos
    (Sys := ko7System) M D hpos

/-! ## Explicit projection-coverage corollaries

The two rows of `Meta/MatrixProjectionCoverage.lean` restated without their pumps. The
fixed-row row takes the tracked coordinate explicitly, which is the reading the coverage
table uses. The row-sum row states its conclusion at `rowSumWeight`, so the weight equation
is consumed by the proof.
-/

/-- Explicit fixed-row coverage corollary, unconditional. -/
theorem no_global_step_orientation_matrix_fixed_row
    {d : Nat} (tracked : Fin d)
    (M : StepDuplicatingSchema.MatrixMeasureD ko7Schema d tracked) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.VecLt :=
  StepDuplicatingSchema.no_global_orients_matrixD (Sys := ko7System) M

/-- Row-sum coverage corollary, unconditional. The all-ones projection of a weighted
functional measure cannot strictly decrease along full KO7 `Step`. -/
theorem no_global_step_orientation_matrix_row_sum
    {d : Nat} (M : StepDuplicatingSchema.MatrixFunctionalMeasure ko7Schema d)
    (hweight : M.weight = StepDuplicatingSchema.rowSumWeight) :
    ¬ MetaConjectureBoundary.GlobalOrients
      (fun t => StepDuplicatingSchema.weightedSum StepDuplicatingSchema.rowSumWeight (M.eval t))
      (· < ·) := by
  intro h
  refine StepDuplicatingSchema.no_global_orients_affine
    (Sys := ko7System) M.projectedAffine ?_
  intro a b hab
  have hstep : Step a b := hab
  simpa [StepDuplicatingSchema.MatrixFunctionalMeasure.projectedAffine, hweight] using h hstep

end OperatorKO7.BarrierPumpDischarge
