import OperatorKO7.Meta.DistinctionBoundary.Quantitative.RepairCover

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover

inductive CanonicalDefect | diagonal
deriving DecidableEq, Fintype

inductive RepairAction | guardDiff | deleteDiff | quotientPeaks | priorityRefl
deriving DecidableEq, Fintype, Repr

def bad : Finset CanonicalDefect := Finset.univ

def closes : RepairAction -> Finset CanonicalDefect
  | .guardDiff | .deleteDiff | .quotientPeaks | .priorityRefl => Finset.univ

theorem coverable : IsRepairCover bad closes Finset.univ := by
  intro b hb
  simp only [Finset.mem_biUnion]
  exact ⟨.guardDiff, Finset.mem_univ _, by simp [closes]⟩

theorem canonical_breaker_repairCoverNumber_eq_one :
    repairCoverNumber bad closes coverable = 1 := by
  apply le_antisymm
  · apply repairCoverNumber_le_card coverable (chosen := {.guardDiff})
    intro b hb
    simp [closes]
  · have h := repairCoverNumber_lower_bound coverable (M := 1) (by decide)
        (fun j => by cases j <;> decide)
    simpa [bad] using h

/-- A tabulated cost assignment on the four `RepairAction` constructors. No action semantics or
semantic-preservation relation is defined in this module. -/
def actionCost : RepairAction -> Nat
  | .guardDiff => 1
  | .deleteDiff => 3
  | .quotientPeaks => 4
  | .priorityRefl => 2

theorem guard_is_unique_minimum_cost_action (a : RepairAction) :
    actionCost .guardDiff <= actionCost a /\
      (actionCost a = actionCost .guardDiff -> a = .guardDiff) := by
  cases a <;> decide

#print axioms canonical_breaker_repairCoverNumber_eq_one
#print axioms guard_is_unique_minimum_cost_action

end OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover
