import OperatorKO7.Meta.LicensedBoundaryCalculus.Accounting.ResourceVector

/-!
# Additive event-to-resource valuations

A valuation is an explicit typed exchange table from semantic events to
resource vectors.  Evaluation is finite and additive; the universal calculus
does not choose a scalar exchange rate.

## Audit slots

Relation: event kinds mapped to typed resource dimensions.
Closure: finite sums and ledger addition.
Trust: kernel-only.
Scope: additive vector valuations, before scalarization.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

/-- Explicit resource vector contributed by one occurrence of each event. -/
structure AdditiveValuation where
  weight : BoundaryEventKind -> ResourceVector

noncomputable section

/-- Evaluate a finite event ledger in a typed resource vector. -/
def AdditiveValuation.evaluate
    (valuation : AdditiveValuation) (ledger : EventLedger) : ResourceVector :=
  ∑ kind : BoundaryEventKind, ledger kind • valuation.weight kind

/-- Universal unconditional additivity of every explicit vector valuation. -/
theorem AdditiveValuation.evaluate_add
    (valuation : AdditiveValuation) (left right : EventLedger) :
    valuation.evaluate (left + right) =
      valuation.evaluate left + valuation.evaluate right := by
  ext resource
  simp [AdditiveValuation.evaluate, add_nsmul, Finset.sum_add_distrib]

/-- Evaluation of a singleton ledger is exactly the selected event weight. -/
theorem AdditiveValuation.evaluate_single
    (valuation : AdditiveValuation) (kind : BoundaryEventKind) (count : Nat) :
    valuation.evaluate (Finsupp.single kind count) =
      count • valuation.weight kind := by
  unfold AdditiveValuation.evaluate
  rw [Finset.sum_eq_single kind]
  · simp
  · intro other _ hne
    simp [Ne.symm hne]
  · simp

/-- Trace concatenation therefore gives vector addition for every valuation. -/
theorem AdditiveValuation.evaluate_countEvents_append
    (valuation : AdditiveValuation) (first second : EventTrace) :
    valuation.evaluate (countEvents (first ++ second)) =
      valuation.evaluate (countEvents first) +
        valuation.evaluate (countEvents second) := by
  rw [countEvents_append, valuation.evaluate_add]

/-- A unit valuation for dimensions whose event/resource interpretation is
definitionally direct.  Other event kinds remain zero until a domain supplies
an explicit valuation. -/
def directUnitValuation : AdditiveValuation where
  weight
    | .certificateBit => Finsupp.single .bit 1
    | .reliableRecordBit => Finsupp.single .bit 1
    | .comparison => Finsupp.single .comparison 1
    | .replayStep => Finsupp.single .replayStep 1
    | .oracleQuery => Finsupp.single .oracleCall 1
    | .externalAssumptionUse => Finsupp.single .externalAssumption 1
    | _ => 0

theorem directUnitValuation_refusalCertificate_fixture :
    directUnitValuation.evaluate
      (countEvents refusalCertificate_trace_fixture) .bit = 1 := by
  rw [refusalCertificate_ledger_fixture]
  rw [AdditiveValuation.evaluate_add]
  rw [AdditiveValuation.evaluate_single, AdditiveValuation.evaluate_single]
  simp [directUnitValuation]

#check AdditiveValuation.evaluate_add
#check AdditiveValuation.evaluate_single
#check AdditiveValuation.evaluate_countEvents_append
#check directUnitValuation_refusalCertificate_fixture
#print axioms AdditiveValuation.evaluate_add
#print axioms AdditiveValuation.evaluate_single
#print axioms AdditiveValuation.evaluate_countEvents_append
#print axioms directUnitValuation_refusalCertificate_fixture

end
end OperatorKO7.Meta.LicensedBoundaryCalculus
