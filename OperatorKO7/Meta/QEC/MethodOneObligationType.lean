import OperatorKO7.Meta.Physics.QECSyndromeAsStage2

/-!
This module defines a QEC obligation carrier, a structural well-formedness predicate, and an
abstention predicate. Its theorem projects an imported syndrome bookkeeping result. Dispatch
behavior requires a separate function and correctness theorem.



-/

namespace OperatorKO7.Meta.QEC.MethodOneObligationType

open OperatorKO7.Meta.Physics.QECSyndromeAsStage2
open OperatorKO7.Meta.Physics.RecordFormation

/-- Data record whose requirements are the fields displayed below. -/
structure QECMethodOneObligation where
  syndromeRound : QECSyndromeRound
  codeLabel : String
  codeDistance : Nat
  decodingPolicy : String
  abstentionTrigger : QECSyndromeRound → Prop

/-- Definition with formal content given by the displayed type and body. -/
def WellFormedQECMethodOneObligation (obligation : QECMethodOneObligation) : Prop :=
  0 < obligation.syndromeRound.syndromeBitCount ∧
  obligation.codeLabel ≠ "" ∧
  0 < obligation.codeDistance ∧
  obligation.decodingPolicy ≠ "" ∧
  obligation.syndromeRound.redundancyThreshold ≤ obligation.syndromeRound.redundancyCount

/-- Definition with formal content given by the displayed type and body.
-/
def qecMethodOneAbstains (obligation : QECMethodOneObligation) : Prop :=
  obligation.abstentionTrigger obligation.syndromeRound

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem qec_method_one_obligation_anchor
    (obligation : QECMethodOneObligation) :
    C6_HonestBitBookkeeping
      (qecSyndromeAsRecordFormation obligation.syndromeRound) :=
  qecSyndromeAsRecordFormation_honestBitBookkeeping obligation.syndromeRound

end OperatorKO7.Meta.QEC.MethodOneObligationType
