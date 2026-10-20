import OperatorKO7.Meta.SafeStep.BranchEntropyGeneral
import OperatorKO7.Meta.SafeStep.BranchTransaction

set_option autoImplicit false

namespace OperatorKO7.Meta.SafeStep.BranchCodeFloor

def finiteBranchCodeBits : Nat -> Nat
  | 0 => 0
  | 1 => 0
  | _ + 2 => 1

theorem raw_diagonal_two_branch_code :
    finiteBranchCodeBits 2 = 1 := rfl

theorem guarded_diagonal_one_branch_code :
    finiteBranchCodeBits 1 = 0 := rfl

theorem diagonal_branch_code_drops_one :
    finiteBranchCodeBits 2 - finiteBranchCodeBits 1 = 1 := rfl

theorem branch_code_matches_entropy_binary :
    finiteBranchCodeBits 1 =
        OperatorKO7.Meta.SafeStep.BranchEntropy.verdictBits 1
      ∧ finiteBranchCodeBits 2 =
        OperatorKO7.Meta.SafeStep.BranchEntropy.verdictBits 2 := by
  simp [finiteBranchCodeBits]

#print axioms raw_diagonal_two_branch_code
#print axioms guarded_diagonal_one_branch_code
#print axioms diagonal_branch_code_drops_one
#print axioms branch_code_matches_entropy_binary

end OperatorKO7.Meta.SafeStep.BranchCodeFloor
