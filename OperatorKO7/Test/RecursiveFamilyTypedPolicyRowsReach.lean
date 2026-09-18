import OperatorKO7.Meta.RecursiveFamilyTypedPolicyRows

/-!
# Reach test: Phase E' typed and policy rows

Confirms every public name added in
`Meta/RecursiveFamilyTypedPolicyRows.lean` is reachable and type-checks.
The reach test imports nothing beyond the module under test (which
transitively pulls every substrate module the catalog projects onto).
-/

namespace OperatorKO7.StepDuplicating

open RecursiveFamilyTypedPolicyRows

#check @RecursiveFamilyTypedPolicyRow
#check @RecursiveFamilyTypedPolicyRow.typedTransport
#check @RecursiveFamilyTypedPolicyRow.manySortedTransport
#check @RecursiveFamilyTypedPolicyRow.higherOrderPolicyAudit
#check @RecursiveFamilyTypedPolicyRow.higherOrderClosure
#check @RecursiveFamilyTypedPolicyRow.noSharingBoundary
#check @RecursiveFamilyTypedPolicyRow.fullCaptureBoundary
#check @RecursiveFamilyTypedPolicyRow.strategyAndConstraintTrivialization

#check @recursiveFamilyTypedPolicyRows
#check @typed_policy_rows_complete_exact
#check @typed_policy_rows_project_existing_surfaces
#check @typed_policy_rows_project_existing_surfaces_holds
#check @phaseEprime_typed_policy_rows_closed

/-! ## Concrete reach examples

Each row of the Phase E' catalog projects onto an existing substrate
theorem. The examples below replay every projection in turn. -/

example :
    typed_policy_rows_project_existing_surfaces .typedTransport :=
  typed_policy_rows_project_existing_surfaces_holds .typedTransport

example :
    typed_policy_rows_project_existing_surfaces .manySortedTransport :=
  typed_policy_rows_project_existing_surfaces_holds .manySortedTransport

example :
    typed_policy_rows_project_existing_surfaces .higherOrderPolicyAudit :=
  typed_policy_rows_project_existing_surfaces_holds .higherOrderPolicyAudit

example :
    typed_policy_rows_project_existing_surfaces .higherOrderClosure :=
  typed_policy_rows_project_existing_surfaces_holds .higherOrderClosure

example :
    typed_policy_rows_project_existing_surfaces .noSharingBoundary :=
  typed_policy_rows_project_existing_surfaces_holds .noSharingBoundary

example :
    typed_policy_rows_project_existing_surfaces .fullCaptureBoundary :=
  typed_policy_rows_project_existing_surfaces_holds .fullCaptureBoundary

example :
    typed_policy_rows_project_existing_surfaces
        .strategyAndConstraintTrivialization :=
  typed_policy_rows_project_existing_surfaces_holds
    .strategyAndConstraintTrivialization

/-- The Phase E' closeout marker is reachable as a single named
proposition combining the complete-exact certificate and the
per-row projection map. -/
example :
    (recursiveFamilyTypedPolicyRows.length = 7 ∧
        recursiveFamilyTypedPolicyRows.Nodup ∧
        (∀ row : RecursiveFamilyTypedPolicyRow,
          row ∈ recursiveFamilyTypedPolicyRows)) ∧
      (∀ row : RecursiveFamilyTypedPolicyRow,
        typed_policy_rows_project_existing_surfaces row) :=
  phaseEprime_typed_policy_rows_closed

end OperatorKO7.StepDuplicating
