import OperatorKO7.Meta.LicensedBoundaryCalculus.Accounting.BoundaryEvent

/-!
# Event traces

Sequential accounting is represented by ordinary list concatenation.  Its unit
and associativity laws are therefore constructor laws rather than supplied
ledger equations.

## Audit slots

Relation: sequential order of semantic events.
Closure: finite list concatenation.
Trust: kernel-only.
Scope: finite execution traces.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

abbrev EventTrace := List BoundaryEvent

/-- Sequential trace composition. -/
def EventTrace.comp (first second : EventTrace) : EventTrace := first ++ second

theorem EventTrace.empty_comp (trace : EventTrace) :
    EventTrace.comp [] trace = trace :=
  rfl

theorem EventTrace.comp_empty (trace : EventTrace) :
    EventTrace.comp trace [] = trace := by
  simp [EventTrace.comp]

theorem EventTrace.comp_assoc (first second third : EventTrace) :
    EventTrace.comp (EventTrace.comp first second) third =
      EventTrace.comp first (EventTrace.comp second third) := by
  simp [EventTrace.comp, List.append_assoc]

/-- Two-event trace fixture. -/
def refusalCertificate_trace_fixture : EventTrace :=
  [⟨.edgeRefusal⟩, ⟨.certificateBit⟩]

theorem refusalCertificate_trace_fixture_length :
    refusalCertificate_trace_fixture.length = 2 :=
  rfl

#check EventTrace.comp_assoc
#check refusalCertificate_trace_fixture_length
#print axioms EventTrace.empty_comp
#print axioms EventTrace.comp_empty
#print axioms EventTrace.comp_assoc
#print axioms refusalCertificate_trace_fixture_length

end OperatorKO7.Meta.LicensedBoundaryCalculus
