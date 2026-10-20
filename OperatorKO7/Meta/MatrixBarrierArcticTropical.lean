import OperatorKO7.Meta.MatrixBarrierArcticTropical_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.MatrixBarrierArcticTropical

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the certificate-backed arctic matrix barrier. -/
theorem no_global_step_orientation_arcticMatrix_of_scalar_dominance_pump
    {d : Nat}
    (M : StepDuplicatingSchema.ArcticMatrixMeasure ko7Schema d)
    (C : StepDuplicatingSchema.ArcticMatrixCertificate d)
    (hweight : C.weight = M.scalarMeasure.weight)
    (hscalarize : ∀ t : Trace, C.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval C.lt := by
  intro h
  exact
    StepDuplicatingSchema.no_arcticMatrix_orients_dup_step_of_scalar_dominance_pump
      (S := ko7Schema) M C hweight hscalarize hunbounded
      (fun b s n => h (ko7System.dup_step b s n))

/-- KO7 specialization of the certificate-backed tropical matrix barrier. -/
theorem no_global_step_orientation_tropicalMatrix_of_scalar_dominance_pump
    {d : Nat}
    (M : StepDuplicatingSchema.TropicalMatrixMeasure ko7Schema d)
    (C : StepDuplicatingSchema.TropicalMatrixCertificate d)
    (hweight : C.weight = M.scalarMeasure.weight)
    (hscalarize : ∀ t : Trace, C.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval C.lt := by
  intro h
  exact
    StepDuplicatingSchema.no_tropicalMatrix_orients_dup_step_of_scalar_dominance_pump
      (S := ko7Schema) M C hweight hscalarize hunbounded
      (fun b s n => h (ko7System.dup_step b s n))

end OperatorKO7.MatrixBarrierArcticTropical
