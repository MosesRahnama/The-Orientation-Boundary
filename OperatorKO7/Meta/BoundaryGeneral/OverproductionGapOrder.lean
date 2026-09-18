import OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.TerminalMultiplicity

/-!
# Order theory and the sign of the overproduction gap

The word "gap" does not by itself imply nonnegativity.  Omega is the difference
between two separately supplied quantities: a structural Hartley envelope and a
licensed information gain.  This module makes the exact sign condition explicit.

* `overproductionGap_nonneg_iff` says nonnegativity is exactly the compatibility
  inequality `deficitBits <= terminalHartleyEntropy`.
* `boundaryEvent_iff` says a strict boundary event is exactly strict failure of
  the evidence channel to cover the structural branch envelope.
* A one-terminal chain paired with the canonical one-bit resolving channel has
  Omega = -1.  Therefore no theorem may advertise Omega as globally
  nonnegative without a coupling or capacity premise.

Trust: kernel checked; no proof holes or user axioms.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapOrder

open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

noncomputable section

/-- The evidence channel is compatible with the operational Hartley envelope
when its licensed information gain does not exceed that envelope. -/
def CapacityCompatible
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) : Prop :=
  deficitBits μ ν r ≤ terminalHartleyEntropy R source

/-- Omega is nonnegative exactly under the capacity-compatibility inequality. -/
theorem overproductionGap_nonneg_iff
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    0 ≤ overproductionGap R source μ ν r ↔
      CapacityCompatible R source μ ν r := by
  unfold overproductionGap CapacityCompatible
  constructor <;> intro h <;> linarith

/-- A positive boundary event is exactly strict under-supply relative to the
operational Hartley envelope. -/
theorem boundaryEvent_iff_deficitBits_lt_hartley
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    BoundaryEvent R source μ ν r ↔
      deficitBits μ ν r < terminalHartleyEntropy R source := by
  unfold BoundaryEvent overproductionGap
  constructor <;> intro h <;> linarith

/-- Exact zero gap means exact equality between supplied information and the
structural Hartley envelope. -/
theorem overproductionGap_eq_zero_iff
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    overproductionGap R source μ ν r = 0 ↔
      deficitBits μ ν r = terminalHartleyEntropy R source := by
  unfold overproductionGap
  constructor <;> intro h <;> linarith

/-- Negative Omega is exactly evidence gain larger than the branch envelope. -/
theorem overproductionGap_neg_iff
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    overproductionGap R source μ ν r < 0 ↔
      terminalHartleyEntropy R source < deficitBits μ ν r := by
  unfold overproductionGap
  constructor <;> intro h <;> linarith

/-- The canonical chain has zero terminal Hartley entropy. -/
theorem chain_terminalHartleyEntropy_eq_zero :
    terminalHartleyEntropy ChainStep .source = 0 := by
  rw [terminalHartleyEntropy_eq_zero_iff_confluentAt chain_normalizingAt_source]
  exact chain_confluentAt_source

/-- **Concrete negative witness.** A deterministic one-terminal operational
system paired with the one-bit resolving channel has Omega = -1. -/
theorem chain_resolving_overproduction_eq_neg_one :
    overproductionGap ChainStep .source
      unitSurface uniformChannelWeights resolvingChannel = -1 := by
  unfold overproductionGap
  rw [chain_terminalHartleyEntropy_eq_zero, resolvingChannel_deficitBits_eq_one]
  ring

/-- Hence Omega is not globally nonnegative over arbitrary independently supplied
relation/channel pairs. -/
theorem overproductionGap_not_globally_nonnegative :
    ∃ (T : Type) (_ : Fintype T) (R : T → T → Prop) (source : T),
      overproductionGap R source unitSurface uniformChannelWeights resolvingChannel < 0 :=
  ⟨ChainNode, inferInstance, ChainStep, .source, by
    rw [chain_resolving_overproduction_eq_neg_one]
    norm_num⟩

/-- The same operational relation can have distinct Omega values under two
licensed evidence channels; Omega is a coupled relation/channel object, not a
relation invariant. -/
theorem channel_choice_changes_overproduction :
    overproductionGap OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3Step
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3.source
        unitSurface uniformChannelWeights echoChannel ≠
      overproductionGap OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3Step
        OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Fork3.source
        unitSurface uniformChannelWeights resolvingChannel := by
  rw [OperatorKO7.Meta.BoundaryGeneral.OverproductionGap.fork3_raw_overproduction_eq_one,
    OperatorKO7.Meta.BoundaryGeneral.OverproductionGap.fork3_raw_gap_closed_by_resolving_channel]
  norm_num

/-- **Evidence monotonicity.** On a fixed operational relation, supplying at least
as much licensed information can only lower Omega. -/
theorem more_evidence_lowers_overproduction
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X₁ W₁ C₁ X₂ W₂ C₂ : Type}
    [Fintype X₁] [Fintype W₁] [Fintype C₁]
    [Fintype X₂] [Fintype W₂] [Fintype C₂]
    (μ₁ : W₁ → ℝ) (ν₁ : W₁ → C₁ → ℝ) (r₁ : W₁ → C₁ → X₁ → ℝ)
    (μ₂ : W₂ → ℝ) (ν₂ : W₂ → C₂ → ℝ) (r₂ : W₂ → C₂ → X₂ → ℝ)
    (hinfo : deficitBits μ₁ ν₁ r₁ ≤ deficitBits μ₂ ν₂ r₂) :
    overproductionGap R source μ₂ ν₂ r₂ ≤
      overproductionGap R source μ₁ ν₁ r₁ := by
  unfold overproductionGap
  linarith

/-- Boundary events are monotone toward weaker evidence: if the stronger
information channel still leaves positive Omega, then any channel with no more
licensed information also leaves a boundary event. -/
theorem boundaryEvent_of_weaker_evidence
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X₁ W₁ C₁ X₂ W₂ C₂ : Type}
    [Fintype X₁] [Fintype W₁] [Fintype C₁]
    [Fintype X₂] [Fintype W₂] [Fintype C₂]
    (μweak : W₁ → ℝ) (νweak : W₁ → C₁ → ℝ) (rweak : W₁ → C₁ → X₁ → ℝ)
    (μstrong : W₂ → ℝ) (νstrong : W₂ → C₂ → ℝ) (rstrong : W₂ → C₂ → X₂ → ℝ)
    (hinfo : deficitBits μweak νweak rweak ≤ deficitBits μstrong νstrong rstrong)
    (hstrong : BoundaryEvent R source μstrong νstrong rstrong) :
    BoundaryEvent R source μweak νweak rweak := by
  unfold BoundaryEvent at hstrong ⊢
  have hmono := more_evidence_lowers_overproduction R source
    μweak νweak rweak μstrong νstrong rstrong hinfo
  linarith

/-- Optional nonnegative reporting surface: the positive part of Omega.  This is
a derived reporting functional, not the primary mathematical object. -/
def overproductionPositivePart
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) : ℝ :=
  max 0 (overproductionGap R source μ ν r)

/-- The positive-part reporting surface is always nonnegative. -/
theorem overproductionPositivePart_nonneg
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    0 ≤ overproductionPositivePart R source μ ν r := by
  exact le_max_left _ _

/-- Under capacity compatibility, taking the positive part changes nothing. -/
theorem overproductionPositivePart_eq_of_compatible
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (h : CapacityCompatible R source μ ν r) :
    overproductionPositivePart R source μ ν r =
      overproductionGap R source μ ν r := by
  unfold overproductionPositivePart
  rw [max_eq_right]
  exact (overproductionGap_nonneg_iff R source μ ν r).2 h

/-- Order-theoretic Omega receipt. -/
theorem overproduction_order_law :
    (∀ {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
      {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
      (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ),
      0 ≤ overproductionGap R source μ ν r ↔
        CapacityCompatible R source μ ν r) ∧
    overproductionGap ChainStep .source
      unitSurface uniformChannelWeights resolvingChannel = -1 :=
  ⟨overproductionGap_nonneg_iff, chain_resolving_overproduction_eq_neg_one⟩

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapOrder
