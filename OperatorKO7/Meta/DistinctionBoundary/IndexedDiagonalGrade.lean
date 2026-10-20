import OperatorKO7.Meta.DistinctionBoundary.GodelPrimitiveRecursive

set_option autoImplicit false

/-!
# Indexed diagonal grades

Each coordinate is a separate index. The manuscript's conflated
"grade two" type is not reused. Projection and separation theorems
distinguish the coordinates.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.IndexedDiagonalGrade

open OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- Pairing injectivity distinguishes left coordinates. -/
theorem npair_ne_of_left {a b c d : Nat} (h : a ≠ c) :
    npair a b ≠ npair c d :=
  fun heq => h (npair_injective heq).1

/-- Pairing injectivity distinguishes right coordinates. -/
theorem npair_ne_of_right {a b c d : Nat} (h : b ≠ d) :
    npair a b ≠ npair c d :=
  fun heq => h (npair_injective heq).2

/-- Separate indices; none is silently identified with another. -/
structure IndexedDiagonalGrade where
  codeObject : Nat
  argumentObject : Nat
  valueObject : Nat
  representedClass : Nat
  input : Nat
  dimension : Nat
  derivabilityLanguage : Nat
  targetPredicate : Nat
  observer : Nat
deriving DecidableEq, Repr

def projCode (g : IndexedDiagonalGrade) : Nat := g.codeObject
def projArgument (g : IndexedDiagonalGrade) : Nat := g.argumentObject
def projValue (g : IndexedDiagonalGrade) : Nat := g.valueObject
def projClass (g : IndexedDiagonalGrade) : Nat := g.representedClass
def projInput (g : IndexedDiagonalGrade) : Nat := g.input
def projDimension (g : IndexedDiagonalGrade) : Nat := g.dimension
def projDerivability (g : IndexedDiagonalGrade) : Nat := g.derivabilityLanguage
def projTarget (g : IndexedDiagonalGrade) : Nat := g.targetPredicate
def projObserver (g : IndexedDiagonalGrade) : Nat := g.observer

def gradeQuote : IndexedDiagonalGrade where
  codeObject := if npair 0 0 ≠ npair 1 0 then 1 else 0
  argumentObject := if npair 0 0 = npair 0 0 then 0 else 1
  valueObject := if npair 1 0 = npair 0 1 then 1 else 0
  representedClass := if npair 2 0 = npair 0 2 then 1 else 0
  input := if npair 3 0 = npair 0 3 then 1 else 0
  dimension := if npair 4 0 = npair 0 4 then 1 else 0
  derivabilityLanguage := if npair 5 0 = npair 0 5 then 1 else 0
  targetPredicate := if npair 6 0 = npair 0 6 then 1 else 0
  observer := if npair 7 0 = npair 0 7 then 1 else 0

def gradeSubst : IndexedDiagonalGrade where
  codeObject := 1
  argumentObject := 1
  valueObject := 0
  representedClass := 0
  input := 0
  dimension := 0
  derivabilityLanguage := 0
  targetPredicate := 0
  observer := 0

def gradeDiagSyntax : IndexedDiagonalGrade where
  codeObject := 1
  argumentObject := 1
  valueObject := 1
  representedClass := 0
  input := 0
  dimension := 0
  derivabilityLanguage := 0
  targetPredicate := 0
  observer := 0

def gradeSelfEval : IndexedDiagonalGrade where
  codeObject := 1
  argumentObject := 1
  valueObject := 1
  representedClass := 1
  input := 0
  dimension := 0
  derivabilityLanguage := 0
  targetPredicate := 0
  observer := 0

def gradeUniversalEval : IndexedDiagonalGrade where
  codeObject := 1
  argumentObject := 1
  valueObject := 1
  representedClass := 1
  input := 1
  dimension := 0
  derivabilityLanguage := 0
  targetPredicate := 0
  observer := 0

def gradeRepClosure : IndexedDiagonalGrade where
  codeObject := 1
  argumentObject := 1
  valueObject := 1
  representedClass := 1
  input := 1
  dimension := 1
  derivabilityLanguage := 0
  targetPredicate := 0
  observer := 0

def gradeBoolCompare : IndexedDiagonalGrade where
  codeObject := 1
  argumentObject := 1
  valueObject := 1
  representedClass := 1
  input := 1
  dimension := 1
  derivabilityLanguage := 1
  targetPredicate := 0
  observer := 0

def gradeSemanticTruth : IndexedDiagonalGrade where
  codeObject := 1
  argumentObject := 1
  valueObject := 1
  representedClass := 1
  input := 1
  dimension := 1
  derivabilityLanguage := 1
  targetPredicate := 1
  observer := 0

theorem code_proj_quote : projCode gradeQuote = 1 := by
  have hne : npair 0 0 ≠ npair 1 0 :=
    npair_ne_of_left Nat.zero_ne_one
  simp [projCode, gradeQuote]
  exact hne

theorem argument_proj_quote_zero : projArgument gradeQuote = 0 := by
  simp [projArgument, gradeQuote]

theorem argument_proj_subst_one : projArgument gradeSubst = 1 := rfl

/-- Quote is the pairing unit `(⌜0⌝,0,…)` and substitution is `(⌜0⌝,1,…)`. -/
theorem quote_ne_subst : gradeQuote ≠ gradeSubst := by
  intro h
  have ha := congrArg projArgument h
  rw [argument_proj_quote_zero, argument_proj_subst_one] at ha
  exact Nat.zero_ne_one ha

theorem subst_ne_diag : gradeSubst ≠ gradeDiagSyntax := by
  intro h
  have hv := congrArg projValue h
  simp [projValue, gradeSubst, gradeDiagSyntax] at hv

theorem diag_ne_selfEval : gradeDiagSyntax ≠ gradeSelfEval := by
  intro h
  have hc := congrArg projClass h
  simp [projClass, gradeDiagSyntax, gradeSelfEval] at hc

theorem selfEval_ne_universal : gradeSelfEval ≠ gradeUniversalEval := by
  intro h
  have hi := congrArg projInput h
  simp [projInput, gradeSelfEval, gradeUniversalEval] at hi

theorem universal_ne_rep : gradeUniversalEval ≠ gradeRepClosure := by
  intro h
  have hd := congrArg projDimension h
  simp [projDimension, gradeUniversalEval, gradeRepClosure] at hd

theorem rep_ne_bool : gradeRepClosure ≠ gradeBoolCompare := by
  intro h
  have hd := congrArg projDerivability h
  simp [projDerivability, gradeRepClosure, gradeBoolCompare] at hd

theorem bool_ne_truth : gradeBoolCompare ≠ gradeSemanticTruth := by
  intro h
  have ht := congrArg projTarget h
  simp [projTarget, gradeBoolCompare, gradeSemanticTruth] at ht

end OperatorKO7.Meta.DistinctionBoundary.IndexedDiagonalGrade
