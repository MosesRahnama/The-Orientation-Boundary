import OperatorKO7.Meta.DistinctionBoundary.FiniteGluingObstruction
import OperatorKO7.Meta.SafeStep.BranchTransaction

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.StrictTransform

open OperatorKO7 Trace
open MetaSN_KO7

structure DiagonalBlowupChart where
  rawSource : Trace
  retainedBranch : Trace
  refusedBranch : Trace
  retainedLicensed : SafeStep rawSource retainedBranch
  refusedRaw : Step rawSource refusedBranch
  refusedLicensed : ¬ SafeStep rawSource refusedBranch

def ko7_diagonal_chart : DiagonalBlowupChart where
  rawSource := eqW void void
  retainedBranch := void
  refusedBranch := integrate (merge void void)
  retainedLicensed := OperatorKO7.Meta.SafeStep.BranchTransaction.diagonal_selected_licensed
  refusedRaw := Step.R_eq_diff void void
  refusedLicensed := OperatorKO7.Meta.SafeStep.BranchTransaction.diagonal_diff_branch_unsafe

theorem ko7_chart_retains_void :
    SafeStep ko7_diagonal_chart.rawSource ko7_diagonal_chart.retainedBranch :=
  ko7_diagonal_chart.retainedLicensed

theorem ko7_chart_refuses_diagonal_difference :
    Step ko7_diagonal_chart.rawSource ko7_diagonal_chart.refusedBranch ∧
      ¬ SafeStep ko7_diagonal_chart.rawSource ko7_diagonal_chart.refusedBranch :=
  ⟨ko7_diagonal_chart.refusedRaw, ko7_diagonal_chart.refusedLicensed⟩

#print axioms ko7_chart_retains_void
#print axioms ko7_chart_refuses_diagonal_difference

end OperatorKO7.Meta.DistinctionBoundary.StrictTransform
