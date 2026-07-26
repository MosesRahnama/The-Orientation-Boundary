/-!
This module defines three size tags and a metadata record whose distance field equals size.value
by construction. Parity rows are replicated all-index records. Theorems prove list size,
nonemptiness, and stored weight equality; stabilizer semantics and code-distance validity
require additional formalization.















-/

namespace OperatorKO7.Meta.QEC.MethodFourSymNGaugedCode

/-- Carrier with the constructors displayed below. -/
inductive SymNSize
  | n5
  | n7
  | n9
  deriving DecidableEq, Repr

/-- Definition with formal content given by the displayed type and body. -/
def SymNSize.value : SymNSize → Nat
  | .n5 => 5
  | .n7 => 7
  | .n9 => 9

@[simp] theorem SymNSize.value_n5 : SymNSize.value .n5 = 5 := rfl
@[simp] theorem SymNSize.value_n7 : SymNSize.value .n7 = 7 := rfl
@[simp] theorem SymNSize.value_n9 : SymNSize.value .n9 = 9 := rfl

/-- Data record whose requirements are the fields displayed below.








-/
structure ParityCheckConstraint where
  supportIndices : List Nat
  weight : Nat
  deriving Repr

/-- Data record whose requirements are the fields displayed below.





-/
structure SymNGaugedCode where
  size : SymNSize
  distance : Nat
  parityChecks : List ParityCheckConstraint
  deriving Repr

/-- Definition with formal content given by the displayed type and body.
-/
def allIndicesUpTo (n : Nat) : List Nat :=
  List.range n

/-- Definition with formal content given by the displayed type and body.
-/
def allIndicesParityCheck (n : Nat) : ParityCheckConstraint where
  supportIndices := allIndicesUpTo n
  weight := n

/-- Definition with formal content given by the displayed type and body.



-/
def canonicalParityChecks (n : Nat) : List ParityCheckConstraint :=
  List.replicate n (allIndicesParityCheck n)

/-- Definition with formal content given by the displayed type and body. -/
def canonicalSymNGaugedCode (s : SymNSize) : SymNGaugedCode where
  size := s
  distance := s.value
  parityChecks := canonicalParityChecks s.value

/-! Declarations for the section below.


-/

/-- The displayed proposition follows from the stated hypotheses.

-/
theorem sym_n_distance_eq_size (s : SymNSize) :
    (canonicalSymNGaugedCode s).distance = s.value := by
  cases s <;> rfl

/-- The displayed proposition follows from the stated hypotheses.


-/
theorem sym_n_parity_checks_nonempty (s : SymNSize) :
    (canonicalSymNGaugedCode s).parityChecks ≠ [] := by
  cases s <;> simp [canonicalSymNGaugedCode, canonicalParityChecks]

/-- The displayed proposition follows from the stated hypotheses.

-/
theorem sym_n_distance_in_set (s : SymNSize) :
    (canonicalSymNGaugedCode s).distance ∈ [5, 7, 9] := by
  cases s <;> simp [canonicalSymNGaugedCode, SymNSize.value]

/-! Declarations for the section below.



-/

theorem canonical_n5_length :
    (canonicalSymNGaugedCode SymNSize.n5).parityChecks.length = 5 := by
  simp [canonicalSymNGaugedCode, canonicalParityChecks, SymNSize.value]

theorem canonical_n7_length :
    (canonicalSymNGaugedCode SymNSize.n7).parityChecks.length = 7 := by
  simp [canonicalSymNGaugedCode, canonicalParityChecks, SymNSize.value]

theorem canonical_n9_length :
    (canonicalSymNGaugedCode SymNSize.n9).parityChecks.length = 9 := by
  simp [canonicalSymNGaugedCode, canonicalParityChecks, SymNSize.value]

theorem canonical_row_weight_eq_size (s : SymNSize)
    (row : ParityCheckConstraint)
    (hRow : row ∈ (canonicalSymNGaugedCode s).parityChecks) :
    row.weight = s.value := by
  have hRep : row ∈ List.replicate s.value (allIndicesParityCheck s.value) := by
    simpa [canonicalSymNGaugedCode, canonicalParityChecks] using hRow
  have hEq : row = allIndicesParityCheck s.value :=
    (List.eq_of_mem_replicate hRep)
  rw [hEq]
  rfl

/-! Declarations for the section below.




-/

/-- Definition with formal content given by the displayed type and body.
-/
def qec_method_four_symn_anchor : String :=
  "OperatorKO7.Meta.QEC.MethodFourSymNGaugedCode.sym_n_distance_eq_size"

/-- Definition with formal content given by the displayed type and body.
-/
def qec_method_four_obligation_anchor : String :=
  "OperatorKO7.Meta.QEC.MethodFourSymNGaugedCode.SymNGaugedCode"

end OperatorKO7.Meta.QEC.MethodFourSymNGaugedCode
