import OperatorKO7.Meta.SafeStep.BranchCodeFloor
import OperatorKO7.Meta.SafeStep.BranchEntropy
import OperatorKO7.Meta.DistinctionBoundary.CostDual

/-!
# Finite prefix-code certificate for branch transactions

The file formalizes the finite, conditional branch-description statement used in
the Distinction Boundary paper. It does not claim universal-machine Kolmogorov
complexity, which is outside the available Mathlib substrate.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.KolmogorovBranchCertificate

/-- Four branch certificates visible at the raw/guarded diagonal boundary. -/
inductive BranchCertificate
  | rawVoid
  | rawDifference
  | guardedVoid
  | refusedDiagonal
  deriving DecidableEq, Repr

/-- Finite prefix-code length assigned to the branch certificates. -/
def prefixCodeLength : BranchCertificate -> Nat
  | .rawVoid => 1
  | .rawDifference => 1
  | .guardedVoid => 0
  | .refusedDiagonal => 0

theorem raw_diagonal_choice_slot_one_bit :
    prefixCodeLength BranchCertificate.rawDifference = 1 := rfl

theorem guarded_diagonal_choice_slot_zero :
    prefixCodeLength BranchCertificate.refusedDiagonal = 0 := rfl

theorem branch_certificate_prefix_model_nonvacuous :
    prefixCodeLength BranchCertificate.rawDifference
        - prefixCodeLength BranchCertificate.refusedDiagonal = 1
      ∧ OperatorKO7.Meta.SafeStep.BranchCodeFloor.finiteBranchCodeBits 2
          - OperatorKO7.Meta.SafeStep.BranchCodeFloor.finiteBranchCodeBits 1 = 1 := by
  exact ⟨rfl, OperatorKO7.Meta.SafeStep.BranchCodeFloor.diagonal_branch_code_drops_one⟩

/-- Conditional Kolmogorov data over the finite branch-certificate surface. The
`invariance` field is the named hypothesis replacing any unformalized universal
prefix machine. -/
structure KolmogorovBranchData where
  K : BranchCertificate -> Nat
  invariance :
    K BranchCertificate.refusedDiagonal ≤ K BranchCertificate.rawDifference
  rawSlot :
    K BranchCertificate.rawDifference = prefixCodeLength BranchCertificate.rawDifference
  guardedSlot :
    K BranchCertificate.refusedDiagonal =
      prefixCodeLength BranchCertificate.refusedDiagonal

/-- The finite model with structural prefix lengths. -/
def finiteBranchKolmogorovData : KolmogorovBranchData where
  K := prefixCodeLength
  invariance := by decide
  rawSlot := rfl
  guardedSlot := rfl

/-- Under the explicit invariance interface, the guarded/refused certificate has
no larger description length than the raw difference certificate. -/
theorem guarded_branch_kolmogorov_drop_conditional
    (D : KolmogorovBranchData) :
    D.K BranchCertificate.refusedDiagonal ≤
      D.K BranchCertificate.rawDifference :=
  D.invariance

/-- In the concrete finite prefix-code model, the drop is exactly one bit. -/
theorem finite_guarded_branch_kolmogorov_drop_exact :
    finiteBranchKolmogorovData.K BranchCertificate.rawDifference
        - finiteBranchKolmogorovData.K BranchCertificate.refusedDiagonal = 1 := by
  rfl

#print axioms raw_diagonal_choice_slot_one_bit
#print axioms guarded_diagonal_choice_slot_zero
#print axioms branch_certificate_prefix_model_nonvacuous
#print axioms guarded_branch_kolmogorov_drop_conditional
#print axioms finite_guarded_branch_kolmogorov_drop_exact

end OperatorKO7.Meta.DistinctionBoundary.KolmogorovBranchCertificate
