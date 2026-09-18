import OperatorKO7.Meta.LicensedBoundaryCalculus.Execution.BoundaryGate

/-!
This module defines the event vocabulary emitted by one BoundaryDecision and proves list
membership by finite case analysis. The scope is the local decisionTrace definition.












-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

/-- Definition with formal content given by the displayed type and body. -/
def EventSemantics : BoundaryDecision → BoundaryEventKind → Prop
  | _, .domainCheck => True
  | .refuseState, .stateRefusal => True
  | .refuseEdge, .edgeCheck => True
  | .refuseEdge, .edgeRefusal => True
  | .commit, .edgeCheck => True
  | .commit, .replayStep => True
  | _, _ => False

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem mem_decisionTrace_iff_eventSemantics
    (decision : BoundaryDecision) (event : BoundaryEvent) :
    event ∈ decisionTrace decision ↔ EventSemantics decision event.kind := by
  rcases event with ⟨kind⟩
  cases decision <;> cases kind <;>
    simp [decisionTrace, EventSemantics]

/-- The displayed proposition follows from the stated hypotheses. -/
theorem certificateBit_not_generic_event
    (decision : BoundaryDecision) :
    ¬ EventSemantics decision .certificateBit := by
  cases decision <;> simp [EventSemantics]

/-- The displayed proposition follows from the stated hypotheses. -/
theorem reliableRecordBit_not_generic_event
    (decision : BoundaryDecision) :
    ¬ EventSemantics decision .reliableRecordBit := by
  cases decision <;> simp [EventSemantics]

#check mem_decisionTrace_iff_eventSemantics
#check certificateBit_not_generic_event
#check reliableRecordBit_not_generic_event
#print axioms mem_decisionTrace_iff_eventSemantics
#print axioms certificateBit_not_generic_event
#print axioms reliableRecordBit_not_generic_event

end OperatorKO7.Meta.LicensedBoundaryCalculus
