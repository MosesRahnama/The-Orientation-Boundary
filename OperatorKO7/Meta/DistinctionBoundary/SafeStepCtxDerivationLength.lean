import OperatorKO7.Meta.ContextualCopyBudget
import OperatorKO7.Meta.ReverseMath.GuardedNewmanExactCalibration

/-!
# SafeStepCtx derivation-length surface

This file re-exports the existing context-closed derivation-length theorem under
the Distinction Boundary paper's stable name.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.SafeStepCtxDerivationLength

open OperatorKO7 Trace
open MetaSN_KO7
open Ordinal

/-- Any exact-length context-closed SafeStep chain has single-exponential length
in the structural term size of its source. -/
theorem safeStepCtx_derivation_length_single_exponential
    (t u : Trace) (n : Nat) (h : SafeStepCtxPow n t u) :
    n + 1 ≤ 2 ^ (2 * termSize t) :=
  safeStepCtx_length_le_two_pow_double_termSize t u n h

/-- The same length theorem is paired with the guarded-Newman `ω^ω * 2` order
descriptor. -/
theorem safeStepCtx_derivation_length_and_order_descriptor
    (t u : Trace) (n : Nat) (h : SafeStepCtxPow n t u) :
    n + 1 ≤ 2 ^ (2 * termSize t) ∧
      OperatorKO7.MetaDM.lex3cToOrd (OperatorKO7.MetaCM.mu3c t) <
        ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) :=
  ⟨safeStepCtx_derivation_length_single_exponential t u n h,
    _root_.OperatorKO7.Meta.ReverseMath.GuardedNewmanExactCalibration.safeStepCtx_order_descriptor_omegaOmega
      t⟩

#print axioms safeStepCtx_derivation_length_single_exponential
#print axioms safeStepCtx_derivation_length_and_order_descriptor

end OperatorKO7.Meta.DistinctionBoundary.SafeStepCtxDerivationLength
