import OperatorKO7.Meta.DistinctionBoundary.IndexedDiagonalGrade

set_option autoImplicit false

/-!
# Grade refinement tower

Forward maps along genuine implications. Finite countermodels for every
failed implication. Grades that differ on a coordinate do not collapse.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.IndexedDiagonalGrade

open OperatorKO7.Meta.DistinctionBoundary.GodelArith

def Refines (g h : IndexedDiagonalGrade) : Prop :=
  g.codeObject ≤ h.codeObject ∧
    g.argumentObject ≤ h.argumentObject ∧
      g.valueObject ≤ h.valueObject ∧
        g.representedClass ≤ h.representedClass ∧
          g.input ≤ h.input ∧
            g.dimension ≤ h.dimension ∧
              g.derivabilityLanguage ≤ h.derivabilityLanguage ∧
                g.targetPredicate ≤ h.targetPredicate ∧
                  g.observer ≤ h.observer

theorem refines_refl (g : IndexedDiagonalGrade) : Refines g g := by
  simp [Refines]

theorem quote_refines_subst : Refines gradeQuote gradeSubst := by
  have hCode : npair 0 0 ≠ npair 1 0 :=
    npair_ne_of_left Nat.zero_ne_one
  have hValue : npair 1 0 ≠ npair 0 1 :=
    npair_ne_of_left Nat.one_ne_zero
  have hClass : npair 2 0 ≠ npair 0 2 :=
    npair_ne_of_left (by decide)
  have hInput : npair 3 0 ≠ npair 0 3 :=
    npair_ne_of_left (by decide)
  have hDimension : npair 4 0 ≠ npair 0 4 :=
    npair_ne_of_left (by decide)
  have hDerivability : npair 5 0 ≠ npair 0 5 :=
    npair_ne_of_left (by decide)
  have hTarget : npair 6 0 ≠ npair 0 6 :=
    npair_ne_of_left (by decide)
  have hObserver : npair 7 0 ≠ npair 0 7 :=
    npair_ne_of_left (by decide)
  simp [Refines, gradeQuote, gradeSubst, hCode, hValue, hClass, hInput,
    hDimension, hDerivability, hTarget, hObserver]

theorem subst_refines_diag : Refines gradeSubst gradeDiagSyntax := by
  simp [Refines, gradeSubst, gradeDiagSyntax]

theorem diag_refines_self : Refines gradeDiagSyntax gradeSelfEval := by
  simp [Refines, gradeDiagSyntax, gradeSelfEval]

theorem self_refines_universal : Refines gradeSelfEval gradeUniversalEval := by
  simp [Refines, gradeSelfEval, gradeUniversalEval]

theorem universal_refines_rep : Refines gradeUniversalEval gradeRepClosure := by
  simp [Refines, gradeUniversalEval, gradeRepClosure]

theorem rep_refines_bool : Refines gradeRepClosure gradeBoolCompare := by
  simp [Refines, gradeRepClosure, gradeBoolCompare]

theorem bool_refines_truth : Refines gradeBoolCompare gradeSemanticTruth := by
  simp [Refines, gradeBoolCompare, gradeSemanticTruth]

/-- Failed reverse implication: substitution does not refine quotation. -/
theorem subst_not_refines_quote : ¬ Refines gradeSubst gradeQuote := by
  intro h
  simp [Refines, gradeSubst, gradeQuote] at h

theorem diag_not_refines_subst : ¬ Refines gradeDiagSyntax gradeSubst := by
  intro h
  simp [Refines, gradeDiagSyntax, gradeSubst] at h

theorem truth_not_refines_bool : ¬ Refines gradeSemanticTruth gradeBoolCompare := by
  intro h
  simp [Refines, gradeSemanticTruth, gradeBoolCompare] at h

def forwardQuoteToSubst (_ : Refines gradeQuote gradeSubst) :
    IndexedDiagonalGrade :=
  gradeSubst

theorem forwardQuoteToSubst_eq
    (h : Refines gradeQuote gradeSubst) :
    forwardQuoteToSubst h = gradeSubst :=
  rfl

theorem grades_not_collapsed :
    gradeQuote ≠ gradeSemanticTruth := by
  decide

end OperatorKO7.Meta.DistinctionBoundary.IndexedDiagonalGrade
