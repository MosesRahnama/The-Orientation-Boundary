import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite

/-!
# Query as informational confession (Informational Incompleteness, Theorem 3.3 / `thm:query-confession`)

`thm:query-confession`: if a query is non-vacuous (the posterior of the target
`X_q` given the meta-layer state is not a point mass), then (1) the conditional
entropy `H(X_q | I_M) > 0`, and (2) under answer-record soundness (receipt of the
answer drives the conditional entropy to zero), the mutual information
`MI = H(X_q | I_M) - H(X_q | I_M, A_q) > 0`.

The posterior is modeled as a finite sub-distribution `p` (`0 ≤ p`, `∑ p ≤ 1`);
non-vacuity is two distinct outcomes with positive mass (`def:nonvacuous-behaviour`).
Clause (1) is the analytic core: a not-point-mass sub-distribution has strictly
positive Shannon entropy. Clause (2) is then `MI = H p - 0 > 0`.

## Audit slots

```
Relation: not applicable (finite-alphabet information functional).
Closure:  not applicable.
Trust:    kernel-only; real-analysis surface only.
Scope:    finite posterior sub-distributions with two positive-mass outcomes.
```
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.InformationalIncompleteness.QueryInterface

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite

/--
Proves: clause (1) of `thm:query-confession`. For a finite posterior
  sub-distribution `p` (`0 ≤ p x`, `∑ p ≤ 1`) that is non-vacuous (two distinct
  outcomes `x₁ ≠ x₂` with positive mass), the conditional entropy is strictly
  positive: `0 < H p`. The `x₁` summand `negMulLog (p x₁)` is strictly positive
  (since `0 < p x₁ < 1`) and every summand is nonnegative.
Does not prove: the converse, or quantitative lower bounds on `H p`.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every finite `α`, sub-distribution `p`, and non-vacuity witness.
-/
theorem query_confession_condEntropy_pos {α : Type} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (h0 : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x ≤ 1)
    (x₁ x₂ : α) (hne : x₁ ≠ x₂) (hp1 : 0 < p x₁) (hp2 : 0 < p x₂) :
    0 < H p := by
  -- every mass is ≤ 1
  have hle1 : ∀ x, p x ≤ 1 := by
    intro x
    have hx : p x ≤ ∑ y, p y :=
      Finset.single_le_sum (fun y _ => h0 y) (Finset.mem_univ x)
    exact le_trans hx hsum
  -- the two positive masses sum to ≤ 1, so p x₁ < 1
  have hpair : p x₁ + p x₂ ≤ ∑ y, p y := by
    have hsub : ({x₁, x₂} : Finset α) ⊆ Finset.univ := Finset.subset_univ _
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun y _ _ => h0 y)
    rwa [Finset.sum_pair hne] at hh
  have hx1lt1 : p x₁ < 1 := by
    have : p x₁ + p x₂ ≤ 1 := le_trans hpair hsum
    linarith
  -- the x₁ summand is strictly positive
  have hterm_pos : 0 < Real.negMulLog (p x₁) := by
    have hlog : Real.log (p x₁) < 0 := Real.log_neg hp1 hx1lt1
    have heq : Real.negMulLog (p x₁) = p x₁ * (-(Real.log (p x₁))) := by
      unfold Real.negMulLog; ring
    rw [heq]
    exact mul_pos hp1 (neg_pos.2 hlog)
  -- H p ≥ that summand
  have hge : Real.negMulLog (p x₁) ≤ H p := by
    unfold H
    exact Finset.single_le_sum
      (fun x _ => Real.negMulLog_nonneg (h0 x) (hle1 x)) (Finset.mem_univ x₁)
  linarith

/--
Proves: clause (2) of `thm:query-confession`. Under answer-record soundness
  (the post-answer conditional entropy `Hpost` is zero), the mutual information
  `MI = H p - Hpost` of a non-vacuous query is strictly positive.
Does not prove: a model of the answer channel; `Hpost = 0` is the soundness
  hypothesis, exactly as the paper states it.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every non-vacuous query with answer-soundness `Hpost = 0`.
-/
theorem query_confession_mi_pos {α : Type} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (h0 : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x ≤ 1)
    (x₁ x₂ : α) (hne : x₁ ≠ x₂) (hp1 : 0 < p x₁) (hp2 : 0 < p x₂)
    (Hpost : ℝ) (hAnswer : Hpost = 0) :
    0 < H p - Hpost := by
  rw [hAnswer, sub_zero]
  exact query_confession_condEntropy_pos p h0 hsum x₁ x₂ hne hp1 hp2

/-- Audit anchor for the query-confession surface. -/
def query_interface_anchor : String :=
  "OperatorKO7.Meta.InformationalIncompleteness.QueryInterface.query_confession_condEntropy_pos"

end OperatorKO7.Meta.InformationalIncompleteness.QueryInterface
