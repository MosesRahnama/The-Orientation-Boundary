import OperatorKO7.Meta.LicensedBoundaryCalculus.Accounting.EventLedger

/-!
# Typed resource vectors

`ResourceKind` defines eight distinct coordinate labels, and `ResourceVector` is a finitely supported
natural-valued function on those labels. The fixture records one bit and two joules; the theorems
evaluate those coordinates and prove that the two labels are distinct.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

inductive ResourceKind
  | bit
  | byte
  | joule
  | second
  | comparison
  | replayStep
  | oracleCall
  | externalAssumption
  deriving DecidableEq, Fintype, Repr

/-- Finitely supported, dimension-typed resource quantities. -/
abbrev ResourceVector := ResourceKind →₀ Nat

noncomputable section

/-- A mixed vector used to test the scalar-policy firewall. -/
def bitJoule_resource_fixture : ResourceVector :=
  Finsupp.single .bit 1 + Finsupp.single .joule 2

theorem bitJoule_resource_fixture_bit :
    bitJoule_resource_fixture .bit = 1 := by
  simp [bitJoule_resource_fixture]

theorem bitJoule_resource_fixture_joule :
    bitJoule_resource_fixture .joule = 2 := by
  simp [bitJoule_resource_fixture]

theorem bit_and_joule_are_distinct :
    ResourceKind.bit ≠ ResourceKind.joule := by
  decide

#check bitJoule_resource_fixture
#check bit_and_joule_are_distinct
#print axioms bitJoule_resource_fixture_bit
#print axioms bitJoule_resource_fixture_joule
#print axioms bit_and_joule_are_distinct

end
end OperatorKO7.Meta.LicensedBoundaryCalculus
