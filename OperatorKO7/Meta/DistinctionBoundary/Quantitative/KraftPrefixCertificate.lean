import Mathlib

set_option autoImplicit false

/-!
# Rational mass-budget certificate

This module records a symbol-count label and two rational mass values.
`PrefixBudgetValid` checks only the inequalities
`0 <= usedKraftMass <= maxKraftMass <= 1`. It does not define codewords,
codeword lengths, prefix-freeness, or a relation between `symbolCount` and the
mass fields.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- A record containing a symbol-count label and rational used and maximum masses. -/
structure PrefixBudget where
  symbolCount : Nat
  maxKraftMass : ℚ
  usedKraftMass : ℚ
  deriving DecidableEq, Repr

def PrefixBudgetValid (P : PrefixBudget) : Prop :=
  0 <= P.usedKraftMass ∧ P.usedKraftMass <= P.maxKraftMass ∧ P.maxKraftMass <= 1

theorem PrefixBudgetValid.used_le_one
    (P : PrefixBudget) (h : PrefixBudgetValid P) :
    P.usedKraftMass <= 1 := by
  linarith [h.2.1, h.2.2]

def twoSymbolUnitPrefixBudget : PrefixBudget where
  symbolCount := 2
  maxKraftMass := 1
  usedKraftMass := 1

theorem twoSymbolUnitPrefixBudget_valid :
    PrefixBudgetValid twoSymbolUnitPrefixBudget := by
  norm_num [PrefixBudgetValid, twoSymbolUnitPrefixBudget]

#print axioms PrefixBudgetValid.used_le_one
#print axioms twoSymbolUnitPrefixBudget_valid

end OperatorKO7.Meta.DistinctionBoundary.Quantitative
