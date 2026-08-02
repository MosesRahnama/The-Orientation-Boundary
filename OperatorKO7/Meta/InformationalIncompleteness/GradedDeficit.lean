import OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy

/-!
# Graded witness-channel deficit (Informational Incompleteness, Section 6)

`prop:deficit-monotone` and `prop:deficit-terminates`. The graded deficit
`InfInc_n(M, t) = H(C_t | I_{<=n})` is the conditional entropy of the
certificate-channel variable given the cumulative information state at order `n`.
Conditioning on more (the cumulative states nest as `n` grows) does not increase
the deficit (`prop:deficit-monotone`), and once the adequate witness order is
reached the channel is determined and the deficit is zero
(`prop:deficit-terminates`).

## Audit slots

```
Relation: not applicable (finite-alphabet information functional).
Closure:  not applicable.
Trust:    kernel-only.
Scope:    finite certificate-channel distributions and cumulative states.
```
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.InformationalIncompleteness.GradedDeficit

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy

/--
Proves: (`prop:deficit-monotone`) the graded witness-channel deficit is
  antitone under refinement of the cumulative information state. Conditioning the
  certificate channel `X` on the finer information `Y` (the cumulative state at a
  higher order) gives `H(X | Y) = condEntropy lam q`, which is at most the
  coarser deficit `H(X) = H(mixture lam q)`. So more committed witness orders
  never increase the deficit.
Does not prove: strict decrease, or a numeric decrement.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (conditioning inequality).
Scope: every finite channel `X`, refinement `Y`, weights `lam ≥ 0` with
  `∑ lam = 1`, and nonnegative conditionals `q`.
-/
theorem gradedDeficit_monotone {X Y : Type} [Fintype X] [Fintype Y]
    (lam : Y → ℝ) (q : Y → X → ℝ)
    (hlam0 : ∀ y, 0 ≤ lam y) (hlam1 : ∑ y, lam y = 1) (hq0 : ∀ y x, 0 ≤ q y x) :
    condEntropy lam q ≤ H (mixture lam q) :=
  condEntropy_le_H_mixture lam q hlam0 hlam1 hq0

/--
Proves: (`prop:deficit-terminates`) once the certificate channel is determined,
  modeled as the point mass at the adequate witness order `kStar`, the graded
  witness-channel deficit is zero. Combined with the orientation-boundary
  coordinate (`WitnessChannelBoundary`), the boundary is the first order at which
  this deficit drops to zero.
Does not prove: the value of the deficit strictly below `kStar`.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (point-mass entropy is zero).
Scope: every finite certificate-channel alphabet and adequate order `kStar`.
-/
theorem gradedDeficit_terminates {C : Type} [Fintype C] [DecidableEq C]
    (kStar : C) : H (pointMass kStar) = 0 :=
  H_pointMass kStar

/-- Audit anchor for the graded witness-channel deficit surface. -/
def graded_deficit_anchor : String :=
  "OperatorKO7.Meta.InformationalIncompleteness.GradedDeficit.gradedDeficit_monotone"

end OperatorKO7.Meta.InformationalIncompleteness.GradedDeficit
