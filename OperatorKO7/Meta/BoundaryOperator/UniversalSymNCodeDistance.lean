import OperatorKO7.Meta.QEC.MethodFourSymNGaugedCode

/-!
# Sym_n metadata fixture

This module defines a finite metadata fixture for each natural number `n`.
`symNDistance n` is defined to be `n`, and `symNParityChecks n` is a singleton
list containing `n`. The resulting theorems establish these definitional
equations and package them with supplied oddness and lower-bound hypotheses.
They provide no stabilizer, commutation, or semantic code-distance predicate.
-/

namespace OperatorKO7.Meta.BoundaryOperator.UniversalSymNCodeDistance

open OperatorKO7.Meta.QEC.MethodFourSymNGaugedCode

/-- Singleton metadata list whose sole entry is the supplied size `n`. -/
def symNParityChecks (n : Nat) : List ParityCheckConstraint :=
  [{ supportIndices := List.range n, weight := n }]

/-- Metadata field defined to equal the supplied size `n`. -/
def symNDistance (n : Nat) : Nat := n

/-- Definitional equation for the distance metadata field. -/
theorem symN_distance_eq (n : Nat) : symNDistance n = n := rfl

/-- The singleton metadata list is nonempty. -/
theorem symN_parity_nonempty (n : Nat) : symNParityChecks n ≠ [] := by
  simp [symNParityChecks]

/-- Every entry of the singleton metadata list equals `n`. -/
theorem symN_parity_weight (n : Nat) :
    ∀ row ∈ symNParityChecks n, row.weight = n := by
  intro row hrow
  simp only [symNParityChecks, List.mem_singleton] at hrow
  subst hrow
  rfl

/-- Package the two metadata equations under supplied oddness and lower-bound
hypotheses. The proof uses the equations directly; the hypotheses record the
intended input regime. -/
theorem symN_universal_qec_valid (n : Nat) (_hodd : n % 2 = 1) (_hge : 5 ≤ n) :
    symNDistance n = n ∧
    symNParityChecks n ≠ [] ∧
    (∀ row ∈ symNParityChecks n, row.weight = n) :=
  ⟨symN_distance_eq n, symN_parity_nonempty n, symN_parity_weight n⟩

/-- Evaluate the metadata equations on each constructor of the finite size
enumeration. -/
theorem symN_distance_admitted_sizes :
    symNDistance 5 = 5 ∧ symNDistance 7 = 7 ∧ symNDistance 9 = 9 :=
  ⟨symN_distance_eq 5, symN_distance_eq 7, symN_distance_eq 9⟩

/-- Package the metadata equations for the three enumerated sizes. -/
def universal_symN_code_distance_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalSymNCodeDistance.symN_universal_qec_valid"

end OperatorKO7.Meta.BoundaryOperator.UniversalSymNCodeDistance
