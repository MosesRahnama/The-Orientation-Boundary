import OperatorKO7.Meta.ResidualMethodLedger

namespace ResidualMethodLedgerReach

open OperatorKO7.ResidualMethodLedger

#check ResidualCoverageStatus
#check matrixClosureStatus_to_wsf
#check rmccStatus_to_wsf
#check ResidualLedgerFamily
#check residualLedgerStatus
#check residualLedgerRows
#check residualLedgerRows_length
#check residualLedgerRows_nodup
#check ResidualLedgerConsistent
#check residual_method_ledger_consistent
#check residual_method_ledger_has_closed
#check residual_method_ledger_has_open
#check residual_method_ledger_has_adapter_only
#check residual_method_ledger_has_conditional

-- R.1 headline: ledger has all four status values
example : ∃ f : ResidualLedgerFamily, residualLedgerStatus f = .closed :=
  ⟨.matrixRow .paretoProduct, rfl⟩

example : ∃ f : ResidualLedgerFamily, residualLedgerStatus f = .open_status :=
  ⟨.matrixRow .unconstrainedRelation, rfl⟩

example : ∃ f : ResidualLedgerFamily, residualLedgerStatus f = .adapter_only :=
  ⟨.matrixRow .arcticFull, rfl⟩

example : ∃ f : ResidualLedgerFamily, residualLedgerStatus f = .conditional :=
  ⟨.rmccRow .matrixComponentwiseWeakStrictReduction, rfl⟩

-- Canonical status for specific families (decidable via rfl)
example : residualLedgerStatus (.matrixRow .paretoProduct) = .closed := rfl

example : residualLedgerStatus (.matrixRow .arcticFull) = .adapter_only := rfl

example : residualLedgerStatus (.matrixRow .unconstrainedRelation) = .open_status := rfl

example : residualLedgerStatus (.rmccRow .fbiAdequacyBoundaryClosed) = .closed := rfl

-- Ledger has 35 rows (10 matrix + 25 RMCC)
example : residualLedgerRows.length = 35 := residualLedgerRows_length


/-! Axiom closure of every pinned declaration (LASOT gate Q24). -/

#print axioms ResidualCoverageStatus
#print axioms matrixClosureStatus_to_wsf
#print axioms rmccStatus_to_wsf
#print axioms ResidualLedgerFamily
#print axioms residualLedgerStatus
#print axioms residualLedgerRows
#print axioms residualLedgerRows_length
#print axioms residualLedgerRows_nodup
#print axioms ResidualLedgerConsistent
#print axioms residual_method_ledger_consistent
#print axioms residual_method_ledger_has_closed
#print axioms residual_method_ledger_has_open
#print axioms residual_method_ledger_has_adapter_only
#print axioms residual_method_ledger_has_conditional

end ResidualMethodLedgerReach
