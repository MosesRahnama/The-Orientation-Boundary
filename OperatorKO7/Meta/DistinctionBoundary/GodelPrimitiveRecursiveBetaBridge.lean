import OperatorKO7.Meta.DistinctionBoundary.GodelPrimitiveRecursiveProofTreeChecker
import OperatorKO7.Meta.DistinctionBoundary.GodelProofRelationSemantics

set_option autoImplicit false

/-!
# Primitive-recursive Boolean checker for the beta proof relation

The object-language `proofRel` consumes beta-packed Hilbert certificates.  The
existing semantics module proves that every accepted recursive proof-tree code
has a canonical beta recoding (`proofRecoding`) and that acceptance is
semantically equivalent to `proofRel` on that recoding.  The numeric checker
constructed in `GodelPrimitiveRecursiveProofTreeChecker.lean` removes the
recursive decoder from the executable side.  This module joins those results:
`proofRelCheckB` is primitive recursive and, on canonical proof/formula codes,
its truth value is equivalent to the beta-sequence relation after canonical
recoding.

The theorem is deliberately scoped to canonical proof-tree input codes.  It
states the executable representability interface actually consumed by the live
Gödel construction and does not identify arbitrary malformed numeric strings
with proof trees.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- Executable Boolean checker corresponding to the beta proof relation through
the canonical proof-tree-to-beta recoding bridge. -/
def proofRelCheckB (proofCode formulaCode : Nat) : Bool :=
  isProofCodeB proofCode formulaCode

/-- The Boolean beta-relation checker is primitive recursive. -/
theorem proofRelCheck_primrec : Primrec₂ proofRelCheckB := by
  exact isProofCodeB_primrec

/-- On canonical proof and formula codes the executable checker agrees with the
live syntactic checker. -/
theorem proofRelCheckB_encode_iff_check (p : ProofTree) (φ : Formula) :
    proofRelCheckB (encodeProof p) (encodeFormula φ) = true ↔
      check p = some φ := by
  exact isProofCodeB_encode_iff p φ

/-- Canonical executable acceptance is equivalent to the beta-packed
object-language proof relation on the canonical recoding. -/
theorem proofRelCheckB_encode_iff_betaRel (p : ProofTree) (φ : Formula) :
    proofRelCheckB (encodeProof p) (encodeFormula φ) = true ↔
      evalForm env0
        (proofRel (numeral (proofRecoding (encodeProof p)))
          (numeral (encodeFormula φ))) := by
  rw [proofRelCheckB_encode_iff_check]
  rw [← isProofCode_iff p φ]
  exact isProofCode_iff_proofRel_recoded_formula (encodeProof p) φ

/-- Primitive-recursive closure package for every arithmetic operation used by
the canonical proof relation and its beta bridge. -/
structure PrimitiveRecursiveBetaClosure : Prop where
  numbering : AcceptableNumberingPrecondition
  betaCheckerPR : Primrec₂ proofRelCheckB
  canonicalAgreement : ∀ p φ,
    proofRelCheckB (encodeProof p) (encodeFormula φ) = true ↔
      evalForm env0
        (proofRel (numeral (proofRecoding (encodeProof p)))
          (numeral (encodeFormula φ)))

/-- The recursive coding, substitution, checker, and canonical beta bridge are
all closed in Mathlib's primitive-recursive class. -/
theorem primitiveRecursiveBetaClosure : PrimitiveRecursiveBetaClosure where
  numbering := acceptable_numbering_precondition
  betaCheckerPR := proofRelCheck_primrec
  canonicalAgreement := proofRelCheckB_encode_iff_betaRel

#check @proofRelCheckB
#check @proofRelCheck_primrec
#check @proofRelCheckB_encode_iff_check
#check @proofRelCheckB_encode_iff_betaRel
#check @PrimitiveRecursiveBetaClosure
#check @primitiveRecursiveBetaClosure
#print axioms proofRelCheck_primrec
#print axioms proofRelCheckB_encode_iff_check
#print axioms proofRelCheckB_encode_iff_betaRel
#print axioms primitiveRecursiveBetaClosure

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
