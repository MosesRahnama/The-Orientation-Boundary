import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficitCore
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapDPExchange

/-!
# Fiber-capacity specializations

The generic capacity theorem is in `FiberDeficitCore.lean`. This file records the two-role and
Fork3 specializations used by the recursor and distinction examples.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit

open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

/-! ## The two-verdict fixture -/

/-- The value observer on the two-role carrier: both roles carry one value. -/
def valueObserver : Bool → Unit := fun _ => ()

/-- The role target: the role itself. -/
def roleTarget : Bool → Bool := id

/-- One value, two roles: the fiber multiplicity is two. -/
theorem two_verdict_multiplicity : fiberMultiplicity valueObserver roleTarget = 2 := by
  decide

/-- One value, two roles: the fiber deficit is one bit. -/
theorem two_verdict_deficit : fiberDeficit valueObserver roleTarget = 1 := by
  unfold fiberDeficit
  rw [two_verdict_multiplicity]
  exact Nat.clog_eq_one (le_refl 2) (le_refl 2)

/-- The role coordinate itself is an additional channel of exactly two values that closes
the deficit. -/
theorem role_channel_closes_two_verdict_deficit :
    FactorsThrough (fun x => (valueObserver x, roleTarget x)) roleTarget := by
  intro x y hxy
  simp only [Prod.mk.injEq] at hxy
  exact hxy.2

/-- The two-verdict fixture is a collision, hence unlicensed for a value-only reading. -/
theorem two_verdict_collision :
    OperationallyInexpressibleAt valueObserver roleTarget false true :=
  ⟨rfl, by decide⟩

open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- **Bridge to the overproduction gap.** On the canonical fixture the fiber deficit of the
value observer against the role target equals the zero-evidence overproduction gap of
`Fork3` under the value-blind channel: both are one bit. -/
theorem two_verdict_deficit_eq_fork3_zero_evidence_gap :
    (fiberDeficit valueObserver roleTarget : ℝ) =
      overproductionGap Fork3Step Fork3.source unitSurface roleWeights roleEcho := by
  rw [valueBlind_gap_one roleEcho (fun _ _ => (1 : ℝ) / 2) (fun _ _ => rfl),
    two_verdict_deficit]
  norm_num

end OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
