import OperatorKO7.Meta.SafeStep.BranchTransaction
import OperatorKO7.Meta.SafeStep.RefusalLoad
import OperatorKO7.Meta.SafeStep.BranchEntropyGeneral

set_option autoImplicit false

namespace OperatorKO7.Meta.SafeStep.EntropySink

open OperatorKO7 Trace
open MetaSN_KO7

structure EntropySinkLedger where
  rawBranches : Nat
  licensedBranches : Nat
  refusedBranches : Nat
  balance : rawBranches = licensedBranches + refusedBranches

def ko7_diagonal_entropySink : EntropySinkLedger where
  rawBranches := 2
  licensedBranches := 1
  refusedBranches := 1
  balance := rfl

theorem ko7_entropySink_balance :
    ko7_diagonal_entropySink.rawBranches =
      ko7_diagonal_entropySink.licensedBranches +
        ko7_diagonal_entropySink.refusedBranches :=
  ko7_diagonal_entropySink.balance

theorem ko7_entropySink_refusal_witness :
    BranchTransaction.ForbiddenBranch Step SafeStep
      (eqW void void) (integrate (merge void void)) :=
  BranchTransaction.diagonal_forbiddenBranch

theorem ko7_entropySink_refusal_load :
    RefusalLoad.refLoad RefusalLoad.diagonalForbidden = 1 :=
  RefusalLoad.refLoad_diagonal_eq_one

#print axioms ko7_entropySink_balance
#print axioms ko7_entropySink_refusal_witness
#print axioms ko7_entropySink_refusal_load

end OperatorKO7.Meta.SafeStep.EntropySink
