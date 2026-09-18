import OperatorKO7.Meta.MatrixBarrierArbitrary_Instances
import OperatorKO7.Meta.MatrixBarrierArcticTropical_Instances
import OperatorKO7.Meta.MatrixResidualTaxonomy

/-!
# Matrix Tool Search Mapping

This module packages the first reviewer-facing matrix search fragments that are already
theorem-backed in the artifact.

Covered fragments:

- fixed-row / unit-weight scalarization for arbitrary mixed matrices;
- row-sum / all-ones scalarization for arbitrary mixed matrices;
- certificate-backed arctic fixed-row / row-sum scalarization;
- certificate-backed tropical fixed-row / row-sum scalarization.

Still open:

- unrestricted arbitrary mixed-matrix classes without a scalarization certificate;
- unrestricted arctic matrix classes;
- unrestricted tropical matrix classes.
-/

namespace OperatorKO7.MatrixToolSearchMapping

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.MatrixResidualTaxonomy

/-- Tool-facing fixed-row fragment for arbitrary mixed matrices. -/
structure FixedRowFragment (Sys : StepDuplicatingSystem) where
  d : Nat
  tracked : Fin d
  measure : MatrixArbitraryMeasure Sys.toStepDuplicatingSchema d
  weight_eq : measure.weight = unitWeight tracked
  unbounded : HasUnboundedScalarizedRange measure

/-- Tool-facing row-sum fragment for arbitrary mixed matrices. -/
structure RowSumFragment (Sys : StepDuplicatingSystem) where
  d : Nat
  measure : MatrixArbitraryMeasure Sys.toStepDuplicatingSchema d
  weight_eq : measure.weight = allOnesWeight
  unbounded : HasUnboundedScalarizedRange measure

/-- Tool-facing fixed-row fragment for the certificate-backed arctic continuation. -/
structure ArcticFixedRowFragment (Sys : StepDuplicatingSystem) where
  d : Nat
  tracked : Fin d
  measure : ArcticMatrixMeasure Sys.toStepDuplicatingSchema d
  weight_eq : measure.scalarMeasure.weight = unitWeight tracked
  scalarize_eq :
    ∀ t : Sys.toStepDuplicatingSchema.T,
      arcticFinitePart (measure.eval t) = measure.scalarMeasure.eval t
  unbounded : HasUnboundedScalarizedRange measure.scalarMeasure

/-- Tool-facing row-sum fragment for the certificate-backed arctic continuation. -/
structure ArcticRowSumFragment (Sys : StepDuplicatingSystem) where
  d : Nat
  measure : ArcticMatrixMeasure Sys.toStepDuplicatingSchema d
  weight_eq : measure.scalarMeasure.weight = allOnesWeight
  scalarize_eq :
    ∀ t : Sys.toStepDuplicatingSchema.T,
      arcticFinitePart (measure.eval t) = measure.scalarMeasure.eval t
  unbounded : HasUnboundedScalarizedRange measure.scalarMeasure

/-- Tool-facing fixed-row fragment for the certificate-backed tropical continuation. -/
structure TropicalFixedRowFragment (Sys : StepDuplicatingSystem) where
  d : Nat
  tracked : Fin d
  measure : TropicalMatrixMeasure Sys.toStepDuplicatingSchema d
  weight_eq : measure.scalarMeasure.weight = unitWeight tracked
  scalarize_eq :
    ∀ t : Sys.toStepDuplicatingSchema.T,
      tropicalFinitePart (measure.eval t) = measure.scalarMeasure.eval t
  unbounded : HasUnboundedScalarizedRange measure.scalarMeasure

/-- Tool-facing row-sum fragment for the certificate-backed tropical continuation. -/
structure TropicalRowSumFragment (Sys : StepDuplicatingSystem) where
  d : Nat
  measure : TropicalMatrixMeasure Sys.toStepDuplicatingSchema d
  weight_eq : measure.scalarMeasure.weight = allOnesWeight
  scalarize_eq :
    ∀ t : Sys.toStepDuplicatingSchema.T,
      tropicalFinitePart (measure.eval t) = measure.scalarMeasure.eval t
  unbounded : HasUnboundedScalarizedRange measure.scalarMeasure

/-- Fixed-row search fragments are blocked by the existing unit-weight scalarization theorem. -/
theorem fixedRow_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : FixedRowFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (VecLeLt F.tracked) := by
  intro h
  exact
    no_matrixArbitrary_orients_dup_step_of_unit_scalar_dominance_pump
      (S := Sys.toStepDuplicatingSchema)
      (tracked := F.tracked)
      F.measure
      F.weight_eq
      F.unbounded
      (fun b s n => h (Sys.dup_step b s n))

/-- Row-sum search fragments are blocked by the existing all-ones scalarization theorem. -/
theorem rowSum_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : RowSumFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval VecLt := by
  intro h
  exact
    no_matrixArbitrary_orients_dup_step_of_rowSum_scalar_dominance_pump
      (S := Sys.toStepDuplicatingSchema)
      F.measure
      F.weight_eq
      F.unbounded
      (fun b s n => h (Sys.dup_step b s n))

/-- Certificate-backed arctic fixed-row fragments are blocked by the unit-weight instance theorem. -/
theorem arcticFixedRow_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : ArcticFixedRowFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (ArcticMatrixUnitLt F.tracked) := by
  intro h
  exact
    no_arcticMatrix_orients_dup_step_of_unit_scalar_dominance_pump
      (S := Sys.toStepDuplicatingSchema)
      (tracked := F.tracked)
      F.measure
      F.weight_eq
      F.scalarize_eq
      F.unbounded
      (fun b s n => h (Sys.dup_step b s n))

/-- Certificate-backed arctic row-sum fragments are blocked by the all-ones instance theorem. -/
theorem arcticRowSum_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : ArcticRowSumFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval ArcticMatrixRowSumLt := by
  intro h
  exact
    no_arcticMatrix_orients_dup_step_of_rowSum_scalar_dominance_pump
      (S := Sys.toStepDuplicatingSchema)
      F.measure
      F.weight_eq
      F.scalarize_eq
      F.unbounded
      (fun b s n => h (Sys.dup_step b s n))

/-- Certificate-backed tropical fixed-row fragments are blocked by the unit-weight instance theorem. -/
theorem tropicalFixedRow_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : TropicalFixedRowFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (TropicalMatrixUnitLt F.tracked) := by
  intro h
  exact
    no_tropicalMatrix_orients_dup_step_of_unit_scalar_dominance_pump
      (S := Sys.toStepDuplicatingSchema)
      (tracked := F.tracked)
      F.measure
      F.weight_eq
      F.scalarize_eq
      F.unbounded
      (fun b s n => h (Sys.dup_step b s n))

/-- Certificate-backed tropical row-sum fragments are blocked by the all-ones instance theorem. -/
theorem tropicalRowSum_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : TropicalRowSumFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval TropicalMatrixRowSumLt := by
  intro h
  exact
    no_tropicalMatrix_orients_dup_step_of_rowSum_scalar_dominance_pump
      (S := Sys.toStepDuplicatingSchema)
      F.measure
      F.weight_eq
      F.scalarize_eq
      F.unbounded
      (fun b s n => h (Sys.dup_step b s n))

/-- The currently theorem-backed matrix projection layer refines the exact residual-matrix
status split at the scalarizable, arctic-full, and tropical-full rows. -/
abbrev MatrixProjectionResidualStatusHook : Prop :=
  matrixResidualClosureStatus .scalarizableWeight = .reducedToExistingTheorem ∧
  matrixResidualClosureStatus .arcticFull = .licensedEscape ∧
  matrixResidualClosureStatus .tropicalFull = .licensedEscape

/-- The exact residual-matrix status split visible from the current projection layer. -/
theorem matrix_projection_fragments_refine_exact_residual_statuses :
    MatrixProjectionResidualStatusHook := by
  decide

end OperatorKO7.MatrixToolSearchMapping
