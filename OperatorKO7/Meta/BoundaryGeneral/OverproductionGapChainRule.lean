import OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

/-!
# Evidence chain rule for Omega

This module treats the operational relation/source as fixed and compares two
evidence channels.  The difference in Omega is exactly the negative difference
in licensed information gain.
-/
set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapChainRule

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

/-- Incremental licensed gain, measured in bits. -/
def incrementalGainBits (d0 d1 : Real) : Real := d1 - d0

/-- **W6 chain rule.** With the operational carrier fixed, upgrading the evidence
channel changes Omega by exactly the negative incremental information gain. -/
theorem overproductionGap_evidence_chain_rule
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X0 W0 C0 X1 W1 C1 : Type}
    [Fintype X0] [Fintype W0] [Fintype C0]
    [Fintype X1] [Fintype W1] [Fintype C1]
    (μ0 : W0 → Real) (ν0 : W0 → C0 → Real) (r0 : W0 → C0 → X0 → Real)
    (μ1 : W1 → Real) (ν1 : W1 → C1 → Real) (r1 : W1 → C1 → X1 → Real) :
    overproductionGap R source μ1 ν1 r1 =
      overproductionGap R source μ0 ν0 r0 -
        incrementalGainBits (deficitBits μ0 ν0 r0) (deficitBits μ1 ν1 r1) := by
  unfold overproductionGap incrementalGainBits
  ring

/-- Equivalent difference form: the Omega drop is exactly the licensed-gain
increase. -/
theorem omega_drop_eq_incremental_gain
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X0 W0 C0 X1 W1 C1 : Type}
    [Fintype X0] [Fintype W0] [Fintype C0]
    [Fintype X1] [Fintype W1] [Fintype C1]
    (μ0 : W0 → Real) (ν0 : W0 → C0 → Real) (r0 : W0 → C0 → X0 → Real)
    (μ1 : W1 → Real) (ν1 : W1 → C1 → Real) (r1 : W1 → C1 → X1 → Real) :
    overproductionGap R source μ0 ν0 r0 - overproductionGap R source μ1 ν1 r1 =
      deficitBits μ1 ν1 r1 - deficitBits μ0 ν0 r0 := by
  unfold overproductionGap
  ring

/-- More licensed information cannot increase Omega on a fixed operational
carrier. -/
theorem omega_antitone_in_licensed_gain
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X0 W0 C0 X1 W1 C1 : Type}
    [Fintype X0] [Fintype W0] [Fintype C0]
    [Fintype X1] [Fintype W1] [Fintype C1]
    (μ0 : W0 → Real) (ν0 : W0 → C0 → Real) (r0 : W0 → C0 → X0 → Real)
    (μ1 : W1 → Real) (ν1 : W1 → C1 → Real) (r1 : W1 → C1 → X1 → Real)
    (hgain : deficitBits μ0 ν0 r0 ≤ deficitBits μ1 ν1 r1) :
    overproductionGap R source μ1 ν1 r1 ≤ overproductionGap R source μ0 ν0 r0 := by
  unfold overproductionGap
  linarith

/-- If the second channel contributes strictly more licensed information, Omega
strictly decreases. -/
theorem omega_strictly_drops_with_strict_gain
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X0 W0 C0 X1 W1 C1 : Type}
    [Fintype X0] [Fintype W0] [Fintype C0]
    [Fintype X1] [Fintype W1] [Fintype C1]
    (μ0 : W0 → Real) (ν0 : W0 → C0 → Real) (r0 : W0 → C0 → X0 → Real)
    (μ1 : W1 → Real) (ν1 : W1 → C1 → Real) (r1 : W1 → C1 → X1 → Real)
    (hgain : deficitBits μ0 ν0 r0 < deficitBits μ1 ν1 r1) :
    overproductionGap R source μ1 ν1 r1 < overproductionGap R source μ0 ν0 r0 := by
  unfold overproductionGap
  linarith

/-- Echo-to-resolving evidence on Fork3 realizes an exact one-bit Omega drop. -/
theorem fork3_echo_to_resolving_chain_rule :
    overproductionGap OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3Step
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3.source
        unitSurface uniformChannelWeights echoChannel -
      overproductionGap OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3Step
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3.source
        unitSurface uniformChannelWeights resolvingChannel = 1 := by
  rw [fork3_raw_overproduction_eq_one,
    fork3_raw_gap_closed_by_resolving_channel]
  norm_num

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapChainRule
