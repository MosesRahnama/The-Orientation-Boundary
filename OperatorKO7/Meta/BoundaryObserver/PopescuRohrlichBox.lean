import OperatorKO7.Meta.BoundaryObserver.FourTestTables

set_option autoImplicit false

/-!
# The Popescu-Rohrlich table

The four disagreement rates define a table with score four and without an observer.
The explicit joint laws realize those rates, with uniform marginals at both parties.

Proof graph: boundary-theorem math completion, node N9.
-/

namespace OperatorKO7.Meta.BoundaryObserver.PopescuRohrlichBox

/-- The four-setting table has disagreement zero except at the pair of true settings. -/
def prBox : FourTestTables.Table := fun x y => if x && y then 1 else 0

/-- The table attains the algebraic score four. -/
theorem prBox_score : FourTestTables.score prBox = 4 := by
  norm_num [FourTestTables.score, FourTestTables.corr, prBox]

/-- The score-four table admits no single joint observer. -/
theorem prBox_no_observer : ¬ FourTestTables.HasObserver prBox := by
  intro h
  have hb := FourTestTables.observer_abs_score_le_two h
  rw [prBox_score] at hb
  norm_num at hb

/-- The final-setting cycle inequality fails for the score-four table. -/
theorem prBox_cycle_fails : ¬ FourTestTables.CycleIneq prBox 1 := by
  intro h
  have h11 := (h true true).1
  norm_num [prBox] at h11

/-- Each setting pair assigns probability one half to each report pair whose sign product
agrees with the product of the settings, and probability zero to the other report pairs. -/
noncomputable def prJoint (x y α β : Bool) : ℝ := by
  classical
  exact (1 / 2 : ℝ) *
    (if FourTestTables.boolSign α * FourTestTables.boolSign β =
        (-1 : ℝ) ^ (x.toNat * y.toNat) then 1 else 0)

/-- Every joint-report probability is nonnegative. -/
theorem prJoint_nonneg (x y α β : Bool) : 0 ≤ prJoint x y α β := by
  unfold prJoint
  split_ifs <;> norm_num

/-- Every setting pair has joint total probability one. -/
theorem prJoint_normalized (x y : Bool) :
    (∑ α : Bool, ∑ β : Bool, prJoint x y α β) = 1 := by
  cases x <;> cases y <;>
    norm_num [prJoint, FourTestTables.boolSign, Fintype.sum_bool]

/-- The probability that the reports disagree equals the corresponding table entry. -/
theorem prJoint_realizes (x y : Bool) :
    (∑ α : Bool, ∑ β : Bool,
      prJoint x y α β * FourTestTables.disagree α β) = prBox x y := by
  cases x <;> cases y <;>
    norm_num [prJoint, FourTestTables.boolSign, FourTestTables.disagree,
      Fintype.sum_bool, prBox]

/-- Each party has probability one half of either report, for both settings of the other
party and both of its own settings. -/
theorem prJoint_marginals_uniform :
    (∀ x y α : Bool, (∑ β : Bool, prJoint x y α β) = (1 / 2 : ℝ)) ∧
    (∀ x y β : Bool, (∑ α : Bool, prJoint x y α β) = (1 / 2 : ℝ)) := by
  constructor
  · intro x y α
    cases x <;> cases y <;> cases α <;>
      norm_num [prJoint, FourTestTables.boolSign, Fintype.sum_bool]
  · intro x y β
    cases x <;> cases y <;> cases β <;>
      norm_num [prJoint, FourTestTables.boolSign, Fintype.sum_bool]

end OperatorKO7.Meta.BoundaryObserver.PopescuRohrlichBox

namespace OperatorKO7.Meta.BoundaryObserver.FourTestTables

/-- The PR table with three zero disagreement rates and one unit rate has score four. -/
theorem pr_box_score_eq_four : score PopescuRohrlichBox.prBox = 4 :=
  PopescuRohrlichBox.prBox_score

/-- The score-four PR table cannot be the rates of a shared joint observer. -/
theorem pr_box_no_observer : ¬ HasObserver PopescuRohrlichBox.prBox :=
  PopescuRohrlichBox.prBox_no_observer

/-- The half-weight parity joint laws are nonnegative, normalized, realize the PR table,
and give both parties uniform report marginals for every setting of the other party. -/
theorem pr_box_uniform_marginals :
    (∀ x y α β : Bool, 0 ≤ PopescuRohrlichBox.prJoint x y α β) ∧
    (∀ x y : Bool,
      (∑ α : Bool, ∑ β : Bool, PopescuRohrlichBox.prJoint x y α β) = 1) ∧
    (∀ x y : Bool,
      (∑ α : Bool, ∑ β : Bool,
        PopescuRohrlichBox.prJoint x y α β * disagree α β) =
        PopescuRohrlichBox.prBox x y) ∧
    (∀ x y α : Bool,
      (∑ β : Bool, PopescuRohrlichBox.prJoint x y α β) = (1 / 2 : ℝ)) ∧
    (∀ x y β : Bool,
      (∑ α : Bool, PopescuRohrlichBox.prJoint x y α β) = (1 / 2 : ℝ)) := by
  exact ⟨PopescuRohrlichBox.prJoint_nonneg,
    PopescuRohrlichBox.prJoint_normalized,
    PopescuRohrlichBox.prJoint_realizes,
    PopescuRohrlichBox.prJoint_marginals_uniform.1,
    PopescuRohrlichBox.prJoint_marginals_uniform.2⟩

end OperatorKO7.Meta.BoundaryObserver.FourTestTables




