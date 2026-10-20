import OperatorKO7.Meta.SafeStep.BranchEntropy
import OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden

/-!
# Axis-growth separation (T6): the two confession loads grow differently

The Distinction-Boundary and Orientation-Boundary developments both discharge to one typed confession,
but the magnitudes differ. This module promotes that prose remark to a proven separation.

* **Confluence axis (left).** Each diagonal query `eqW a a` collapses two unjoinable verdicts to one,
  a fixed one-bit branch-entropy collapse (`BranchEntropy.branchEntropy_collapse_one_bit`), and pays a
  constant-size refusal certificate `¬ (a ≠ a)`. Over a batch of `N` diagonal queries the load is `N`
  bits: linear, with a constant unit marginal.
* **Termination axis (right).** The raw carrier burden of the canonical trace
  (`CarrierBurden.carrierRaw`) adds `(K + 2) * L` units at depth `K`: the per-step marginal grows
  without bound.

`axis_growth_separation` packages the contrast: the confluence-axis marginal is the constant `1`, while
the termination-axis marginal is unbounded. The confession load on the left does not grow; the carrier
burden on the right does.

## Claim typing (binding)
* PROVEN: every theorem below (pure `Nat` arithmetic over the `verdictBits` collapse anchor and the
  `carrierRaw` closed form).
* ANALOGY (docstring only): the identification of the `Nat` counts with physical cost; the formal
  content is the marginal-growth comparison.

## Audit slots
- Relation: not applicable (pure `Nat` arithmetic; the `verdictBits` collapse anchor is re-used as a
  count, no `Step`/`SafeStep` reasoning here).
- Closure: no axioms (pure `Nat`); verified by `#print axioms` below.
- Trust: no `sorry`/`admit`/`axiom`/`opaque`/`partial`/`unsafe`/`native_decide`/`bv_decide`/`@[csimp]`.
- Non-vacuity (R5): `axis_growth_separation_witness` exhibits a concrete batch count and a concrete
  termination marginal.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.InformationalIncompleteness.AxisGrowthSeparation

open OperatorKO7.Meta.SafeStep.BranchEntropy
open OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden

/-- Total confluence-axis branch-entropy over `N` independent diagonal queries: each diagonal query is
the one-bit collapse `verdictBits 2 - verdictBits 1`, so the batch carries `N` such bits. -/
def batchBranchEntropy (N : Nat) : Nat := N * (verdictBits 2 - verdictBits 1)

/-- The batch branch-entropy is exactly `N`: the confluence-axis load is linear in the number of
diagonal queries, one bit each (via the one-bit collapse anchor). -/
theorem batchBranchEntropy_eq (N : Nat) : batchBranchEntropy N = N := by
  unfold batchBranchEntropy
  rw [branchEntropy_collapse_one_bit, Nat.mul_one]

/-- **Confluence-axis marginal is constant.** Each additional diagonal query adds exactly one bit; the
confluence-axis load does not grow with the batch. -/
theorem confluence_marginal_constant (N : Nat) :
    batchBranchEntropy (N + 1) - batchBranchEntropy N = 1 := by
  rw [batchBranchEntropy_eq, batchBranchEntropy_eq]
  omega

/-- **Termination-axis marginal at depth `K`.** Extending the canonical trace by one step adds
`(K + 2) * L` units of raw carrier mass: the new wrapper cell carries the duplicated payload. -/
theorem termination_marginal (L K : Nat) :
    carrierRaw L (K + 1) - carrierRaw L K = (K + 2) * L := by
  have h : carrierRaw L (K + 1) = carrierRaw L K + (K + 2) * L := rfl
  omega

/-- **Termination-axis marginal is unbounded.** For any positive payload `L ≥ 1`, the per-step carrier
cost `(K + 2) * L` exceeds every bound as the depth `K` grows: the termination-axis load keeps growing,
in contrast to the constant confluence-axis bit. -/
theorem termination_marginal_unbounded (L : Nat) (hL : 1 ≤ L) :
    ∀ M, ∃ K, M < carrierRaw L (K + 1) - carrierRaw L K := by
  intro M
  refine ⟨M + 1, ?_⟩
  rw [termination_marginal]
  calc M < M + 3 := by omega
    _ = (M + 1 + 2) * 1 := by ring
    _ ≤ (M + 1 + 2) * L := Nat.mul_le_mul le_rfl hL

/-- **Axis-growth separation.** The confluence-axis load has a constant unit marginal (one bit per
diagonal query) while the termination-axis load has an unbounded marginal: the confession load on the
left does not grow, the carrier burden on the right does. -/
theorem axis_growth_separation (L : Nat) (hL : 1 ≤ L) :
    (∀ N, batchBranchEntropy (N + 1) - batchBranchEntropy N = 1)
      ∧ (∀ M, ∃ K, M < carrierRaw L (K + 1) - carrierRaw L K) :=
  ⟨confluence_marginal_constant, termination_marginal_unbounded L hL⟩

/-- **Non-vacuity (R5).** A concrete batch count (`7` queries carry `7` bits) and a concrete termination
marginal (depth `1` to `2` adds `3` units at payload `L = 1`). -/
theorem axis_growth_separation_witness :
    batchBranchEntropy 7 = 7 ∧ carrierRaw 1 2 - carrierRaw 1 1 = 3 :=
  ⟨batchBranchEntropy_eq 7, by decide⟩

#print axioms batchBranchEntropy_eq
#print axioms confluence_marginal_constant
#print axioms termination_marginal
#print axioms termination_marginal_unbounded
#print axioms axis_growth_separation
#print axioms axis_growth_separation_witness

end OperatorKO7.Meta.InformationalIncompleteness.AxisGrowthSeparation
