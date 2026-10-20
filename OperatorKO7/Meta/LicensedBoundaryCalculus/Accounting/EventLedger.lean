import OperatorKO7.Meta.LicensedBoundaryCalculus.Accounting.EventTrace

/-!
# Finitely supported event ledger

`countEvents` recursively converts a finite event trace to finitely supported counts by event kind.
The append theorem proves that counting a concatenated trace equals addition of the two ledgers. The
fixture evaluates a trace containing one refusal and one certificate-bit event.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

/-- Finitely supported event counts indexed by event kind. -/
abbrev EventLedger := BoundaryEventKind →₀ Nat

noncomputable section

/-- The one-event ledger. -/
def singletonEventLedger (event : BoundaryEvent) : EventLedger :=
  Finsupp.single event.kind 1

/-- Count every event in a finite trace. -/
def countEvents : EventTrace -> EventLedger
  | [] => 0
  | event :: rest => singletonEventLedger event + countEvents rest

@[simp] theorem countEvents_nil : countEvents [] = 0 :=
  rfl

@[simp] theorem countEvents_cons (event : BoundaryEvent) (rest : EventTrace) :
    countEvents (event :: rest) = singletonEventLedger event + countEvents rest :=
  rfl

/-- Event counting converts list append into ledger addition. -/
theorem countEvents_append (first second : EventTrace) :
    countEvents (first ++ second) = countEvents first + countEvents second := by
  induction first with
  | nil => simp
  | cons event rest ih =>
      simp [ih, add_assoc]

theorem countEvents_comp (first second : EventTrace) :
    countEvents (EventTrace.comp first second) =
      countEvents first + countEvents second := by
  exact countEvents_append first second

/-- The concrete two-event trace has one refusal and one certificate bit. -/
theorem refusalCertificate_ledger_fixture :
    countEvents refusalCertificate_trace_fixture =
      Finsupp.single .edgeRefusal 1 + Finsupp.single .certificateBit 1 := by
  simp [refusalCertificate_trace_fixture, countEvents, singletonEventLedger]

theorem refusalCertificate_edgeRefusal_count_fixture :
    countEvents refusalCertificate_trace_fixture .edgeRefusal = 1 := by
  rw [refusalCertificate_ledger_fixture]
  simp

#check countEvents_append
#check countEvents_comp
#check refusalCertificate_ledger_fixture
#print axioms countEvents_append
#print axioms countEvents_comp
#print axioms refusalCertificate_ledger_fixture
#print axioms refusalCertificate_edgeRefusal_count_fixture

end
end OperatorKO7.Meta.LicensedBoundaryCalculus
