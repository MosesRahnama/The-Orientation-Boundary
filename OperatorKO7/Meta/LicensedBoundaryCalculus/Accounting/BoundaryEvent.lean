import Mathlib

/-!
# Boundary events

This file declares the finite event vocabulary used by the LBC accounting
records. Repeated occurrences can be represented by repeated trace entries in
downstream ledgers. The declarations here do not prove that the vocabulary is
complete for every application domain.

## Formal scope

Relation: none; event classification only.
Closure: none.
Trust: kernel-only finite inductive data.
Scope: the closed inductive catalog declared below.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

/-- Event kinds available to the LBC accounting records. -/
inductive BoundaryEventKind
  | domainCheck
  | stateRefusal
  | edgeCheck
  | edgeRefusal
  | stateIdentification
  | terminalAlternative
  | repairAction
  | witnessGradeUse
  | certificateBit
  | reliableRecordBit
  | comparison
  | replayStep
  | oracleQuery
  | externalAssumptionUse
  deriving DecidableEq, Fintype, Repr

/-- One audited occurrence in an execution trace. -/
structure BoundaryEvent where
  kind : BoundaryEventKind
  deriving DecidableEq, Repr

/-- A concrete refusal event proves that the event type is inhabited. -/
def edgeRefusal_event_fixture : BoundaryEvent := ⟨.edgeRefusal⟩

theorem edgeRefusal_event_fixture_kind :
    edgeRefusal_event_fixture.kind = .edgeRefusal :=
  rfl

#check edgeRefusal_event_fixture
#check edgeRefusal_event_fixture_kind
#print axioms edgeRefusal_event_fixture_kind

end OperatorKO7.Meta.LicensedBoundaryCalculus
