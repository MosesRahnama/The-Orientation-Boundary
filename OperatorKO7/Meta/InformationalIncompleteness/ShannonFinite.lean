import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Finite-alphabet Shannon entropy (Informational Incompleteness substrate)

Minimal finite-alphabet Shannon entropy `H p = ∑ x, negMulLog (p x)` over a
`Fintype` carrier, used by the diagonal-entropy lemma (`lem:diagonal`), the
query-confession theorem, and the graded-deficit propositions. Built on
`Real.negMulLog` so no measure-theoretic machinery is required.

## Audit slots

```
Relation: not applicable (real-valued information functional).
Closure:  not applicable.
Trust:    kernel-only; `noncomputable` (real analysis), depends on the standard
          analysis axiom surface only. No sorry/native_decide/user axiom.
Scope:    finite-alphabet distributions `p : α → ℝ` over a `Fintype α`.
```
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite

/--
Proves: the finite-alphabet Shannon entropy of `p : α → ℝ` over a `Fintype α`,
  `H p = ∑ x, negMulLog (p x)` where `negMulLog t = -t * log t`.
Does not prove: that `p` is a probability distribution; `H` is defined on any
  real-valued `p` and the distribution hypotheses are supplied per theorem.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`noncomputable` real functional).
Scope: every `Fintype α` and `p : α → ℝ`.
-/
noncomputable def H {α : Type} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ x, Real.negMulLog (p x)

/--
Proves: `H p` is nonnegative for a sub-distribution (`0 ≤ p x ≤ 1` pointwise),
  since each summand `negMulLog (p x)` is nonnegative on `[0, 1]`.
Does not prove: strict positivity (that is the non-point-mass statement).
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `Fintype α` and `p` with `0 ≤ p x ≤ 1` for all `x`.
-/
theorem H_nonneg {α : Type} [Fintype α] (p : α → ℝ)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1) : 0 ≤ H p := by
  unfold H
  apply Finset.sum_nonneg
  intro x _
  exact Real.negMulLog_nonneg (h0 x) (h1 x)

/--
Proves: entropy is invariant under relabeling the alphabet by an equivalence
  `e : α ≃ β`: `H (p ∘ e.symm) = H p`. This is the mechanized core of the
  diagonal-entropy lemma `lem:diagonal` (`H(Δ_m Y) = H(Y)`): the m-fold diagonal
  copy variable is supported on the diagonal of `α^m`, which is in bijection with
  `α`, so duplicating identical copies is a relabeling and adds no entropy.
Does not prove: the zero-padded pushforward form over the full `α^m` directly;
  the content (relabeling invariance) is identical, and off-diagonal mass carries
  `negMulLog 0 = 0`.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (reindexing by the equivalence).
Scope: every `Fintype α`, `Fintype β`, equivalence `e : α ≃ β`, and `p : α → ℝ`.
-/
theorem H_relabel_eq {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (p : α → ℝ) :
    H (fun b => p (e.symm b)) = H p := by
  unfold H
  rw [← Equiv.sum_comp e (fun b => Real.negMulLog (p (e.symm b)))]
  simp

/-- The point-mass (determinate) distribution at `x₀`: `1` at `x₀`, `0` elsewhere. -/
def pointMass {α : Type} [DecidableEq α] (x₀ : α) : α → ℝ :=
  fun x => if x = x₀ then 1 else 0

/--
Proves: a determinate (point-mass) distribution has zero Shannon entropy,
  `H (pointMass x₀) = 0`. Every summand is `negMulLog 1 = 0` (at `x₀`) or
  `negMulLog 0 = 0` (elsewhere).
Does not prove: the converse (zero entropy implies point mass), which needs the
  sub-distribution hypothesis.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `Fintype α` with `DecidableEq α` and every `x₀ : α`.
-/
theorem H_pointMass {α : Type} [Fintype α] [DecidableEq α] (x₀ : α) :
    H (pointMass x₀) = 0 := by
  unfold H pointMass
  apply Finset.sum_eq_zero
  intro x _
  by_cases h : x = x₀
  · simp [h, Real.negMulLog, Real.log_one]
  · simp [h, Real.negMulLog]

end OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
