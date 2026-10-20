import OperatorKO7.Meta.MatrixBarrierArcticTropical
import OperatorKO7.Meta.MatrixBarrierArbitrary_Instances

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Fixed-row / unit-weight arctic comparison induced by the finite-part scalarization. -/
def ArcticMatrixUnitLt {d : Nat} (tracked : Fin d) (u v : ArcticMatrixVec d) : Prop :=
  VecLeLt tracked (arcticFinitePart u) (arcticFinitePart v)

/-- Row-sum / all-ones arctic comparison induced by the finite-part scalarization. -/
def ArcticMatrixRowSumLt {d : Nat} (u v : ArcticMatrixVec d) : Prop :=
  VecLt (arcticFinitePart u) (arcticFinitePart v)

/-- Fixed-row / unit-weight tropical comparison on the finite-vector carrier. -/
def TropicalMatrixUnitLt {d : Nat} (tracked : Fin d) (u v : TropicalMatrixVec d) : Prop :=
  VecLeLt tracked u v

/-- Row-sum / all-ones tropical comparison on the finite-vector carrier. -/
def TropicalMatrixRowSumLt {d : Nat} (u v : TropicalMatrixVec d) : Prop :=
  VecLt u v

namespace ArcticMatrixCertificate

/-- Reusable fixed-row / unit-weight arctic certificate. -/
def of_unitScalarDominance {d : Nat} (tracked : Fin d) : ArcticMatrixCertificate d where
  weight := unitWeight tracked
  scalarize := arcticFinitePart
  lt := ArcticMatrixUnitLt tracked
  nonstrict := by
    intro u v h
    simpa [ArcticMatrixUnitLt] using
      (MatrixScalarDominance.of_pointwise_le_lt (weight := unitWeight tracked) tracked).nonstrict h

/-- Reusable row-sum / all-ones arctic certificate. -/
def of_rowSumScalarDominance {d : Nat} : ArcticMatrixCertificate d where
  weight := allOnesWeight
  scalarize := arcticFinitePart
  lt := ArcticMatrixRowSumLt
  nonstrict := by
    intro u v h
    simpa [ArcticMatrixRowSumLt] using
      (MatrixScalarDominance.of_pointwise_lt (weight := allOnesWeight)).nonstrict h

end ArcticMatrixCertificate

namespace TropicalMatrixCertificate

/-- Reusable fixed-row / unit-weight tropical certificate. -/
def of_unitScalarDominance {d : Nat} (tracked : Fin d) : TropicalMatrixCertificate d where
  weight := unitWeight tracked
  scalarize := tropicalFinitePart
  lt := TropicalMatrixUnitLt tracked
  nonstrict := by
    intro u v h
    simpa [TropicalMatrixUnitLt, tropicalFinitePart] using
      (MatrixScalarDominance.of_pointwise_le_lt (weight := unitWeight tracked) tracked).nonstrict h

/-- Reusable row-sum / all-ones tropical certificate. -/
def of_rowSumScalarDominance {d : Nat} : TropicalMatrixCertificate d where
  weight := allOnesWeight
  scalarize := tropicalFinitePart
  lt := TropicalMatrixRowSumLt
  nonstrict := by
    intro u v h
    simpa [TropicalMatrixRowSumLt, tropicalFinitePart] using
      (MatrixScalarDominance.of_pointwise_lt (weight := allOnesWeight)).nonstrict h

end TropicalMatrixCertificate

/-- Fixed-row / unit-weight arctic instance of the certificate-backed matrix barrier. -/
theorem no_arcticMatrix_orients_dup_step_of_unit_scalar_dominance_pump
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : ArcticMatrixMeasure S d)
    (hweight : M.scalarMeasure.weight = unitWeight tracked)
    (hscalarize : ∀ t : S.T, arcticFinitePart (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ (∀ (b s n : S.T),
      ArcticMatrixUnitLt tracked
        (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  exact
    no_arcticMatrix_orients_dup_step_of_scalar_dominance_pump
      M
      (ArcticMatrixCertificate.of_unitScalarDominance tracked)
      (by simpa using hweight.symm)
      hscalarize
      hunbounded

/-- Row-sum / all-ones arctic instance of the certificate-backed matrix barrier. -/
theorem no_arcticMatrix_orients_dup_step_of_rowSum_scalar_dominance_pump
    {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticMatrixMeasure S d)
    (hweight : M.scalarMeasure.weight = allOnesWeight)
    (hscalarize : ∀ t : S.T, arcticFinitePart (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ (∀ (b s n : S.T),
      ArcticMatrixRowSumLt
        (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  exact
    no_arcticMatrix_orients_dup_step_of_scalar_dominance_pump
      M
      ArcticMatrixCertificate.of_rowSumScalarDominance
      (by simpa using hweight.symm)
      hscalarize
      hunbounded

/-- Fixed-row / unit-weight tropical instance of the certificate-backed matrix barrier. -/
theorem no_tropicalMatrix_orients_dup_step_of_unit_scalar_dominance_pump
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : TropicalMatrixMeasure S d)
    (hweight : M.scalarMeasure.weight = unitWeight tracked)
    (hscalarize : ∀ t : S.T, tropicalFinitePart (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ (∀ (b s n : S.T),
      TropicalMatrixUnitLt tracked
        (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  exact
    no_tropicalMatrix_orients_dup_step_of_scalar_dominance_pump
      M
      (TropicalMatrixCertificate.of_unitScalarDominance tracked)
      (by simpa using hweight.symm)
      hscalarize
      hunbounded

/-- Row-sum / all-ones tropical instance of the certificate-backed matrix barrier. -/
theorem no_tropicalMatrix_orients_dup_step_of_rowSum_scalar_dominance_pump
    {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalMatrixMeasure S d)
    (hweight : M.scalarMeasure.weight = allOnesWeight)
    (hscalarize : ∀ t : S.T, tropicalFinitePart (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ (∀ (b s n : S.T),
      TropicalMatrixRowSumLt
        (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  exact
    no_tropicalMatrix_orients_dup_step_of_scalar_dominance_pump
      M
      TropicalMatrixCertificate.of_rowSumScalarDominance
      (by simpa using hweight.symm)
      hscalarize
      hunbounded

end StepDuplicatingSchema

namespace MatrixBarrierArcticTropical

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 fixed-row / unit-weight arctic wrapper. -/
theorem no_global_step_orientation_arcticMatrix_unit_of_scalar_dominance_pump
    {d : Nat} {tracked : Fin d}
    (M : StepDuplicatingSchema.ArcticMatrixMeasure ko7Schema d)
    (hweight : M.scalarMeasure.weight = StepDuplicatingSchema.unitWeight tracked)
    (hscalarize : ∀ t : Trace,
      StepDuplicatingSchema.arcticFinitePart (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ StepDuplicatingSchema.GlobalOrients
        ko7System M.eval (StepDuplicatingSchema.ArcticMatrixUnitLt tracked) := by
  intro h
  exact
    StepDuplicatingSchema.no_arcticMatrix_orients_dup_step_of_unit_scalar_dominance_pump
      (S := ko7Schema) M hweight hscalarize hunbounded
      (fun b s n => h (ko7System.dup_step b s n))

/-- KO7 row-sum / all-ones arctic wrapper. -/
theorem no_global_step_orientation_arcticMatrix_rowSum_of_scalar_dominance_pump
    {d : Nat}
    (M : StepDuplicatingSchema.ArcticMatrixMeasure ko7Schema d)
    (hweight : M.scalarMeasure.weight = StepDuplicatingSchema.allOnesWeight)
    (hscalarize : ∀ t : Trace,
      StepDuplicatingSchema.arcticFinitePart (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ StepDuplicatingSchema.GlobalOrients
        ko7System M.eval StepDuplicatingSchema.ArcticMatrixRowSumLt := by
  intro h
  exact
    StepDuplicatingSchema.no_arcticMatrix_orients_dup_step_of_rowSum_scalar_dominance_pump
      (S := ko7Schema) M hweight hscalarize hunbounded
      (fun b s n => h (ko7System.dup_step b s n))

/-- KO7 fixed-row / unit-weight tropical wrapper. -/
theorem no_global_step_orientation_tropicalMatrix_unit_of_scalar_dominance_pump
    {d : Nat} {tracked : Fin d}
    (M : StepDuplicatingSchema.TropicalMatrixMeasure ko7Schema d)
    (hweight : M.scalarMeasure.weight = StepDuplicatingSchema.unitWeight tracked)
    (hscalarize : ∀ t : Trace,
      StepDuplicatingSchema.tropicalFinitePart (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ StepDuplicatingSchema.GlobalOrients
        ko7System M.eval (StepDuplicatingSchema.TropicalMatrixUnitLt tracked) := by
  intro h
  exact
    StepDuplicatingSchema.no_tropicalMatrix_orients_dup_step_of_unit_scalar_dominance_pump
      (S := ko7Schema) M hweight hscalarize hunbounded
      (fun b s n => h (ko7System.dup_step b s n))

/-- KO7 row-sum / all-ones tropical wrapper. -/
theorem no_global_step_orientation_tropicalMatrix_rowSum_of_scalar_dominance_pump
    {d : Nat}
    (M : StepDuplicatingSchema.TropicalMatrixMeasure ko7Schema d)
    (hweight : M.scalarMeasure.weight = StepDuplicatingSchema.allOnesWeight)
    (hscalarize : ∀ t : Trace,
      StepDuplicatingSchema.tropicalFinitePart (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ StepDuplicatingSchema.GlobalOrients
        ko7System M.eval StepDuplicatingSchema.TropicalMatrixRowSumLt := by
  intro h
  exact
    StepDuplicatingSchema.no_tropicalMatrix_orients_dup_step_of_rowSum_scalar_dominance_pump
      (S := ko7Schema) M hweight hscalarize hunbounded
      (fun b s n => h (ko7System.dup_step b s n))

end MatrixBarrierArcticTropical

end OperatorKO7.StepDuplicating
