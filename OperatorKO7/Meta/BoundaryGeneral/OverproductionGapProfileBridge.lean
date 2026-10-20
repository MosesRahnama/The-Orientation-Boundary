import OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
import OperatorKO7.Meta.BoundaryQuantitative.DistinctionInstance

/-!
# Omega and the branch-excess count

`ObstructionProfile.branchExcess` counts surplus terminals as a natural number; Omega measures terminal entropy in bits. The count equals the bit value for Fork3 but not for the four-terminal example. For a count-compatible profile with zero licensed gain, Omega equals the base-two logarithm of `branchExcess + 1`.
-/
set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapProfileBridge

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.BoundaryQuantitative
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- A profile's branch-excess count is operationally calibrated when `excess + 1`
is exactly the number of reachable terminal alternatives. -/
def BranchCountCompatible {T : Type} [Fintype T]
    (p : ObstructionProfile) (R : T → T → Prop) (source : T) : Prop :=
  p.branchExcess + 1 = terminalMultiplicity R source

/-- Convert a surplus-terminal count to bits. -/
noncomputable def branchExcessBits (p : ObstructionProfile) : Real :=
  Real.logb 2 (p.branchExcess + 1 : Real)

/-- For a count-compatible profile with zero licensed gain, Omega equals the base-two logarithm of `branchExcess + 1`. -/
theorem zeroEvidence_omega_eq_branchExcessBits_of_countCompatible
    {T : Type} [Fintype T] (p : ObstructionProfile)
    (R : T → T → Prop) (source : T)
    {X W C : Type} [Fintype X] [Fintype W] [Fintype C]
    (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real)
    (hcount : BranchCountCompatible p R source)
    (hzero : deficitBits μ ν r = 0) :
    overproductionGap R source μ ν r = branchExcessBits p := by
  unfold overproductionGap branchExcessBits terminalHartleyEntropy
  rw [hzero, sub_zero, ← hcount]
  norm_num

/-- Fork3's one surplus terminal matches its two-terminal multiplicity. -/
theorem fork3_branchCountCompatible :
    BranchCountCompatible (distinctionRawBadProfile 1 0) Fork3Step Fork3.source := by
  simp [BranchCountCompatible, distinctionRawBadProfile,
    fork3_raw_terminalMultiplicity_eq_two]

/-- For Fork3, the one-bit Omega value equals the branch-excess count. -/
theorem fork3_branchExcess_equals_omega :
    overproductionGap Fork3Step Fork3.source
      unitSurface uniformChannelWeights echoChannel =
      ((distinctionRawBadProfile 1 0).branchExcess : Real) := by
  rw [fork3_raw_overproduction_eq_one]
  norm_num [distinctionRawBadProfile]

/-- Four raw terminals correspond to three surplus terminals. -/
theorem fourFork_branchCountCompatible :
    BranchCountCompatible (distinctionRawBadProfile 3 0)
      FourForkStep FourForkNode.source := by
  simp [BranchCountCompatible, distinctionRawBadProfile,
    fourFork_terminalMultiplicity_eq_four]

/-- Four raw terminals have two bits of zero-evidence Omega. -/
theorem fourFork_echo_omega_eq_two :
    overproductionGap FourForkStep FourForkNode.source
      unitSurface uniformChannelWeights echoChannel = 2 := by
  unfold overproductionGap terminalHartleyEntropy
  rw [echoChannel_deficitBits_zero, sub_zero, fourFork_terminalMultiplicity_eq_four]
  change Real.log 4 / Real.log 2 = 2
  rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
  have hlog : Real.log (2 : Real) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog]

/-- For the four-terminal relation, the branch-excess count is three while Omega is two bits. -/
theorem branchExcess_not_equal_zeroEvidenceOmega_in_general :
    ((distinctionRawBadProfile 3 0).branchExcess : Real) ≠
      overproductionGap FourForkStep FourForkNode.source
        unitSurface uniformChannelWeights echoChannel := by
  rw [fourFork_echo_omega_eq_two]
  norm_num [distinctionRawBadProfile]

/-- The receipt gives the Fork3 equality, the four-terminal logarithmic value, and the count-to-bits mismatch. -/
theorem branchExcess_omega_bridge_resolved :
    BranchCountCompatible (distinctionRawBadProfile 1 0) Fork3Step Fork3.source ∧
    overproductionGap Fork3Step Fork3.source unitSurface uniformChannelWeights echoChannel = 1 ∧
    BranchCountCompatible (distinctionRawBadProfile 3 0) FourForkStep FourForkNode.source ∧
    overproductionGap FourForkStep FourForkNode.source unitSurface uniformChannelWeights echoChannel = 2 ∧
    ((distinctionRawBadProfile 3 0).branchExcess : Real) ≠
      overproductionGap FourForkStep FourForkNode.source
        unitSurface uniformChannelWeights echoChannel :=
  ⟨fork3_branchCountCompatible, fork3_raw_overproduction_eq_one,
    fourFork_branchCountCompatible, fourFork_echo_omega_eq_two,
    branchExcess_not_equal_zeroEvidenceOmega_in_general⟩

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapProfileBridge
