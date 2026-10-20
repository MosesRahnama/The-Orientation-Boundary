import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapOrder
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapProduct

/-!
# Over-evidence and negative Omega

Negative Omega means licensed information exceeds the operational terminal envelope. This module defines its magnitude and proves finite examples with one-bit and two-bit excess.
-/
set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.OmegaOverEvidence

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapOrder
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapProduct
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Over-evidence means strictly negative Omega. -/
def OverEvidence
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W C : Type} [Fintype X] [Fintype W] [Fintype C]
    (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real) : Prop :=
  overproductionGap R source μ ν r < 0

/-- Magnitude of wasted/over-supplied evidence in the negative regime. -/
def overEvidenceMagnitude (omega : Real) : Real := max 0 (-omega)

theorem overEvidence_iff_evidence_exceeds_envelope
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W C : Type} [Fintype X] [Fintype W] [Fintype C]
    (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real) :
    OverEvidence R source μ ν r ↔
      terminalHartleyEntropy R source < deficitBits μ ν r := by
  exact overproductionGap_neg_iff R source μ ν r

/-- In the negative regime the magnitude is exactly `-Omega`. -/
theorem overEvidenceMagnitude_eq_neg {omega : Real} (h : omega < 0) :
    overEvidenceMagnitude omega = -omega := by
  simp [overEvidenceMagnitude, le_of_lt (neg_pos.mpr h)]

/-- The one-bit chain example has negative Omega. -/
theorem one_bit_overEvidence :
    OverEvidence ChainStep ChainNode.source
      unitSurface uniformChannelWeights resolvingChannel := by
  unfold OverEvidence
  rw [chain_resolving_overproduction_eq_neg_one]
  norm_num

/-- The resolving channel is normalized for the independent-product calculation. -/
theorem resolvingChannel_normalized :
    NormalizedChannel unitSurface uniformChannelWeights resolvingChannel := by
  constructor
  · simp [unitSurface]
  · exact uniformChannelWeights_sum_one
  · intro w c
    fin_cases c <;> simp [resolvingChannel,
      OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite.pointMass]

/-- Two independent one-terminal systems can carry two bits of over-evidence. -/
theorem two_bit_overEvidence_value :
    overproductionGap
      (OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingProductQuotient.ProductStep
        ChainStep ChainStep)
      (ChainNode.source, ChainNode.source)
      (productMu unitSurface unitSurface)
      (productNu uniformChannelWeights uniformChannelWeights)
      (productConditional resolvingChannel resolvingChannel) = -2 := by
  rw [overproductionGap_independent_product
    (R := ChainStep) (S := ChainStep)
    (a := ChainNode.source) (b := ChainNode.source)
    chain_normalizingAt_source chain_normalizingAt_source
    resolvingChannel_normalized resolvingChannel_normalized]
  rw [chain_resolving_overproduction_eq_neg_one]
  norm_num

/-- The single-chain and two-chain resolving examples have Omega values `-1` and `-2`. -/
theorem overEvidence_regime_nontrivial :
    overproductionGap ChainStep ChainNode.source
        unitSurface uniformChannelWeights resolvingChannel = -1 ∧
    overproductionGap
      (OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingProductQuotient.ProductStep
        ChainStep ChainStep)
      (ChainNode.source, ChainNode.source)
      (productMu unitSurface unitSurface)
      (productNu uniformChannelWeights uniformChannelWeights)
      (productConditional resolvingChannel resolvingChannel) = -2 :=
  ⟨chain_resolving_overproduction_eq_neg_one, two_bit_overEvidence_value⟩

end OperatorKO7.Meta.BoundaryGeneral.OmegaOverEvidence
