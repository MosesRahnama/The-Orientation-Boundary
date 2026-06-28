import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
import Mathlib.Analysis.Convex.Jensen

/-!
# Finite conditional entropy and the conditioning inequality (Informational Incompleteness substrate)

Reusable finite conditional-entropy layer for the graded witness-channel deficit
(`prop:deficit-monotone`). Models `H(X | Y)` as the `Y`-weighted average of the
per-cell entropies, `condEntropy lam q = ∑ y, lam y * H (q y)`, and proves the
conditioning inequality `H(X | Y) ≤ H(X)`: conditioning on `Y` does not increase
entropy. The proof is concave Jensen (`ConcaveOn.le_map_sum`) applied pointwise
to `Real.negMulLog`, which is concave on `[0, ∞)`.

## Audit slots

```
Relation: not applicable (finite-alphabet information functional).
Closure:  not applicable.
Trust:    kernel-only; `noncomputable` real-analysis surface only.
Scope:    finite families of distributions with nonnegative weights summing to 1.
```
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite

/-- Finite conditional entropy `H(X | Y)`: the `Y`-weighted average of the
per-cell entropies, `∑ y, lam y * H (q y)`, where `lam y` is the weight of cell
`y` and `q y` is the conditional distribution of `X` given `Y = y`. -/
noncomputable def condEntropy {X Y : Type} [Fintype X] [Fintype Y]
    (lam : Y → ℝ) (q : Y → X → ℝ) : ℝ :=
  ∑ y, lam y * H (q y)

/-- The marginal mixture distribution of `X`, `mixture lam q x = ∑ y, lam y * q y x`. -/
noncomputable def mixture {X Y : Type} [Fintype Y]
    (lam : Y → ℝ) (q : Y → X → ℝ) : X → ℝ :=
  fun x => ∑ y, lam y * q y x

/--
Proves: the conditioning inequality (`prop:deficit-monotone` core, Cover-Thomas
  Thm 2.6.5): `H(X | Y) ≤ H(X)`. Conditioning on `Y` does not increase the
  entropy of `X`, where `H(X)` is the entropy of the marginal mixture. The proof
  applies concave Jensen for `negMulLog` pointwise in `x`, then swaps the order
  of summation.
Does not prove: equality conditions, or the chain rule.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (concavity of `negMulLog` + Jensen).
Scope: every finite `X`, `Y`, weights `lam ≥ 0` with `∑ lam = 1`, and
  nonnegative conditionals `q`.
-/
theorem condEntropy_le_H_mixture {X Y : Type} [Fintype X] [Fintype Y]
    (lam : Y → ℝ) (q : Y → X → ℝ)
    (hlam0 : ∀ y, 0 ≤ lam y) (hlam1 : ∑ y, lam y = 1)
    (hq0 : ∀ y x, 0 ≤ q y x) :
    condEntropy lam q ≤ H (mixture lam q) := by
  unfold condEntropy mixture H
  -- pointwise concave Jensen in x
  have hpt : ∀ x, (∑ y, lam y * Real.negMulLog (q y x))
      ≤ Real.negMulLog (∑ y, lam y * q y x) := by
    intro x
    have hjensen := Real.concaveOn_negMulLog.le_map_sum
      (t := Finset.univ) (w := lam) (p := fun y => q y x)
      (fun y _ => hlam0 y) hlam1 (fun y _ => Set.mem_Ici.2 (hq0 y x))
    simpa [smul_eq_mul] using hjensen
  calc ∑ y, lam y * (∑ x, Real.negMulLog (q y x))
      = ∑ y, ∑ x, lam y * Real.negMulLog (q y x) := by
        refine Finset.sum_congr rfl ?_
        intro y _
        rw [Finset.mul_sum]
    _ = ∑ x, ∑ y, lam y * Real.negMulLog (q y x) := Finset.sum_comm
    _ ≤ ∑ x, Real.negMulLog (∑ y, lam y * q y x) :=
        Finset.sum_le_sum (fun x _ => hpt x)

/-- Audit anchor for the conditional-entropy surface. -/
def conditional_entropy_anchor : String :=
  "OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy.condEntropy_le_H_mixture"

end OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy
