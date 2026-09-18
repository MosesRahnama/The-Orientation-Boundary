import OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery

/-!
# Budgeted finite noisy recovery

The exhaustive finite side-encoder search can be restricted by any computable natural-number cost.
The returned encoder is feasible and has minimum Bayes risk among all encoders within the budget.
The algorithm makes no efficiency claim.

Property: finite constrained Bayes optimization.
Trust: kernel-only with the same classical baseline as the imported Bayes layer.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.BudgetedNoisyRecovery

open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery

universe u v w z

variable {X : Type u} {O : Type v} {V : Type w} {C : Type z}
variable [Fintype X] [Fintype O] [Fintype V] [Fintype C]
variable [DecidableEq X] [DecidableEq O] [DecidableEq V] [DecidableEq C]

/-- All deterministic side encoders whose declared natural-number cost is within the budget. -/
def budgetedSideEncoderCandidates
    (EX : Enumeration X) (EC : Enumeration C)
    (cost : (X → C) → Nat) (budget : Nat) : List (X → C) :=
  (sideEncoderCandidates EX EC).filter fun s => cost s ≤ budget

omit [Fintype X] [Fintype C] in
/-- Membership is equivalent to being an encoder in the exhaustive function table and satisfying
its budget. -/
theorem mem_budgetedSideEncoderCandidates_iff
    (EX : Enumeration X) (EC : Enumeration C)
    (cost : (X → C) → Nat) (budget : Nat) (s : X → C) :
    s ∈ budgetedSideEncoderCandidates EX EC cost budget ↔ cost s ≤ budget := by
  simp [budgetedSideEncoderCandidates, sideEncoderCandidates_complete EX EC s]

/-- Minimum-risk feasible encoder, computed by filtering the exhaustive encoder table and then
running the existing finite argmin. -/
def bestBudgetedSideEncoder?
    (EX : Enumeration X) (EC : Enumeration C) (EV : Enumeration V)
    (M : RationalObservationModel X O) (P : X → V)
    (cost : (X → C) → Nat) (budget : Nat) : Option (X → C) :=
  argminBy? (sideRisk EV M P) (budgetedSideEncoderCandidates EX EC cost budget)

omit [Fintype V] [DecidableEq O] in
/-- Every returned encoder satisfies the declared budget. -/
theorem bestBudgetedSideEncoder?_feasible
    (EX : Enumeration X) (EC : Enumeration C) (EV : Enumeration V)
    (M : RationalObservationModel X O) (P : X → V)
    (cost : (X → C) → Nat) (budget : Nat) {best : X → C}
    (hbest : bestBudgetedSideEncoder? EX EC EV M P cost budget = some best) :
    cost best ≤ budget := by
  have hmem := (argminBy?_minimal (sideRisk EV M P) hbest).1
  exact (mem_budgetedSideEncoderCandidates_iff EX EC cost budget best).1 hmem

omit [Fintype V] [DecidableEq O] in
/-- The returned feasible encoder has minimum Bayes risk among every deterministic encoder with
cost at most the budget. -/
theorem bestBudgetedSideEncoder?_minimal
    (EX : Enumeration X) (EC : Enumeration C) (EV : Enumeration V)
    (M : RationalObservationModel X O) (P : X → V)
    (cost : (X → C) → Nat) (budget : Nat) {best : X → C}
    (hbest : bestBudgetedSideEncoder? EX EC EV M P cost budget = some best) :
    ∀ s : X → C, cost s ≤ budget → sideRisk EV M P best ≤ sideRisk EV M P s := by
  have hmin := (argminBy?_minimal (sideRisk EV M P) hbest).2
  intro s hs
  exact hmin s ((mem_budgetedSideEncoderCandidates_iff EX EC cost budget s).2 hs)

omit [Fintype V] [DecidableEq O] in
/-- The constrained search is empty exactly when every deterministic encoder exceeds the budget. -/
theorem bestBudgetedSideEncoder?_eq_none_iff
    (EX : Enumeration X) (EC : Enumeration C) (EV : Enumeration V)
    (M : RationalObservationModel X O) (P : X → V)
    (cost : (X → C) → Nat) (budget : Nat) :
    bestBudgetedSideEncoder? EX EC EV M P cost budget = none ↔
      ¬ ∃ s : X → C, cost s ≤ budget := by
  rw [bestBudgetedSideEncoder?, argminBy?_eq_none_iff]
  constructor
  · intro hempty hexists
    rcases hexists with ⟨s, hs⟩
    have hmem : s ∈ budgetedSideEncoderCandidates EX EC cost budget :=
      (mem_budgetedSideEncoderCandidates_iff EX EC cost budget s).2 hs
    rw [hempty] at hmem
    simp at hmem
  · intro hnone
    apply List.eq_nil_iff_forall_not_mem.2
    intro s hmem
    exact hnone ⟨s,
      (mem_budgetedSideEncoderCandidates_iff EX EC cost budget s).1 hmem⟩

omit [Fintype X] [Fintype C] in
/-- Increasing the budget only adds feasible encoder candidates. -/
theorem budgetedSideEncoderCandidates_mono
    (EX : Enumeration X) (EC : Enumeration C)
    (cost : (X → C) → Nat) {b₁ b₂ : Nat} (hbudget : b₁ ≤ b₂) :
    ∀ s, s ∈ budgetedSideEncoderCandidates EX EC cost b₁ →
      s ∈ budgetedSideEncoderCandidates EX EC cost b₂ := by
  intro s hs
  rw [mem_budgetedSideEncoderCandidates_iff] at hs ⊢
  exact le_trans hs hbudget

omit [Fintype V] [DecidableEq O] in
/-- If both budget levels return optima, the larger budget has Bayes risk at most that of the
smaller budget. -/
theorem bestBudgetedSideEncoder?_risk_antitone
    (EX : Enumeration X) (EC : Enumeration C) (EV : Enumeration V)
    (M : RationalObservationModel X O) (P : X → V)
    (cost : (X → C) → Nat) {b₁ b₂ : Nat} (hbudget : b₁ ≤ b₂)
    {best₁ best₂ : X → C}
    (h₁ : bestBudgetedSideEncoder? EX EC EV M P cost b₁ = some best₁)
    (h₂ : bestBudgetedSideEncoder? EX EC EV M P cost b₂ = some best₂) :
    sideRisk EV M P best₂ ≤ sideRisk EV M P best₁ := by
  apply bestBudgetedSideEncoder?_minimal EX EC EV M P cost b₂ h₂ best₁
  exact le_trans (bestBudgetedSideEncoder?_feasible EX EC EV M P cost b₁ h₁) hbudget

/-! ## Cost controls -/

/-- Constant-zero encoder cost makes every deterministic encoder feasible at every budget. -/
def zeroEncoderCost (_ : X → C) : Nat := 0

omit [Fintype X] [Fintype C] in
/-- Under zero encoder cost, constrained search is the unconstrained search on the same candidates. -/
theorem zeroEncoderCost_candidates
    (EX : Enumeration X) (EC : Enumeration C) (budget : Nat) :
    budgetedSideEncoderCandidates EX EC (zeroEncoderCost (X := X) (C := C)) budget =
      sideEncoderCandidates EX EC := by
  simp [budgetedSideEncoderCandidates, zeroEncoderCost]

/-- A uniform positive cost can make a nonempty encoder space infeasible under a zero budget. -/
def oneEncoderCost (_ : X → C) : Nat := 1

omit [Fintype X] [Fintype C] in
/-- At budget zero every positive-cost encoder is filtered out. -/
theorem oneEncoderCost_zero_candidates
    (EX : Enumeration X) (EC : Enumeration C) :
    budgetedSideEncoderCandidates EX EC (oneEncoderCost (X := X) (C := C)) 0 = [] := by
  simp [budgetedSideEncoderCandidates, oneEncoderCost]

end OperatorKO7.Meta.OperationalInexpressibility.BudgetedNoisyRecovery
