import OperatorKO7.Meta.DistinctionBoundary.CostDual
import OperatorKO7.Meta.SafeStep.BranchTransaction

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.TransactionGalois

structure ProjectionLicense where
  droppedDimension : Nat
  retainedVerdict : Prop

structure BranchLicense where
  refusedBranchCount : Nat
  retainedVerdict : Prop

def ProjectionLe (A B : ProjectionLicense) : Prop :=
  A.droppedDimension ≤ B.droppedDimension ∧
    (A.retainedVerdict -> B.retainedVerdict)

def BranchLe (A B : BranchLicense) : Prop :=
  A.refusedBranchCount ≤ B.refusedBranchCount ∧
    (A.retainedVerdict -> B.retainedVerdict)

def projectionToBranch (P : ProjectionLicense) : BranchLicense where
  refusedBranchCount := P.droppedDimension
  retainedVerdict := P.retainedVerdict

def branchToProjection (B : BranchLicense) : ProjectionLicense where
  droppedDimension := B.refusedBranchCount
  retainedVerdict := B.retainedVerdict

theorem finite_transaction_galois (P : ProjectionLicense) (B : BranchLicense) :
    BranchLe (projectionToBranch P) B ↔
      ProjectionLe P (branchToProjection B) := by
  rfl

theorem transaction_unit_cost_matches_refusal (N : Nat) :
    CostDual.totalCharge CostDual.distinctionChargeLaw (List.replicate N ()) = N :=
  CostDual.distinction_totalCharge_eq_N N

#print axioms finite_transaction_galois
#print axioms transaction_unit_cost_matches_refusal

end OperatorKO7.Meta.DistinctionBoundary.TransactionGalois
