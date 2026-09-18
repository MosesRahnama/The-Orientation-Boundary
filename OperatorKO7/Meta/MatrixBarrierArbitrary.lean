import OperatorKO7.Meta.MatrixBarrierArbitrary_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.MatrixBarrierArbitrary

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the arbitrary mixed-matrix scalar-dominance barrier. -/
theorem no_global_step_orientation_matrixArbitrary_of_scalar_dominance_pump
    {d : Nat}
    (M : StepDuplicatingSchema.MatrixArbitraryMeasure ko7Schema d)
    {R : StepDuplicatingSchema.MatrixVec d → StepDuplicatingSchema.MatrixVec d → Prop}
    (D : StepDuplicatingSchema.MatrixScalarDominance M.weight R)
    (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval R := by
  exact
    StepDuplicatingSchema.no_global_orients_matrixArbitrary_of_scalar_dominance_pump
      (Sys := ko7System) M D hunbounded

end OperatorKO7.MatrixBarrierArbitrary
