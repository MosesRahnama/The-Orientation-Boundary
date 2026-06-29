import OperatorKO7.Meta.SafeStep.RefusalLoad
import OperatorKO7.Meta.SafeStep.BranchEntropyGeneral

set_option autoImplicit false

namespace OperatorKO7.Meta.SafeStep.RefusalLoadMinimum

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.RefusalLoad
open OperatorKO7.Meta.SafeStep.BranchEntropyGeneral

/-- A per-query refusal certificate scheme for one forbidden diagonal branch. -/
structure OneBranchCertificateScheme where
  perQueryCost : Nat
  coversForbiddenBranch : 1 <= perQueryCost

/-- One bit is the real-valued branch entropy of the refused diagonal branch. -/
theorem refused_branch_entropy_one_bit :
    branchEntropy 2 - branchEntropy 1 = 1 :=
  branchEntropy_collapse_one_bit_real

/-- Any certificate scheme covering one forbidden diagonal branch costs at least one unit. -/
theorem diagonal_refusal_load_minimum (S : OneBranchCertificateScheme) :
    1 <= S.perQueryCost :=
  S.coversForbiddenBranch

/-- The KO7 singleton refusal scheme attains the one-unit lower bound. -/
def ko7SingletonCertificateScheme : OneBranchCertificateScheme where
  perQueryCost := refLoad diagonalForbidden
  coversForbiddenBranch := by
    rw [refLoad_diagonal_eq_one]

/-- Exact optimality: the compiled KO7 diagonal scheme has cost one and no valid scheme costs zero. -/
theorem ko7_refusal_load_is_minimum :
    ko7SingletonCertificateScheme.perQueryCost = 1
      ∧ ∀ S : OneBranchCertificateScheme, 1 <= S.perQueryCost :=
  ⟨refLoad_diagonal_eq_one, diagonal_refusal_load_minimum⟩

/-- The existing batch theorem is the linear accumulation law in minimum-cost form. -/
theorem ko7_minimum_refusal_load_batch (srcs : List Trace) :
    (srcs.map (fun a => refLoad (batchForbidden a))).sum = srcs.length :=
  refLoad_batch_eq_N srcs

#print axioms refused_branch_entropy_one_bit
#print axioms ko7_refusal_load_is_minimum
#print axioms ko7_minimum_refusal_load_batch

end OperatorKO7.Meta.SafeStep.RefusalLoadMinimum

