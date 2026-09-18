import OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
import OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
import OperatorKO7.Meta.DistinctionBoundary.MinimalForkQuantitative

/-!
# Distributional overproduction and the Shannon-Hartley envelope

The Hartley overproduction gap uses the full reachable terminal support and is
therefore a worst-case structural envelope.  This module equips that support
with an explicit scheduler distribution and defines the distributional gap

`OmegaS = H₂(scheduler) - deficitBits`.

The scheduler is typed on the reachable-normal-form subtype itself, so it cannot
assign probability mass to a branch outside the audited terminal support.
`shannon_overproduction_le_hartley` proves the expected inequality, and the
uniform scheduler attains it.  The aligned-target theorem is a novelty fence:
whenever the scheduler entropy is exactly the target's direct conditional
entropy, `OmegaS` is simply residual conditional entropy in bits.

Scope: finite Type-0 carriers, matching the current finite Shannon substrate.
Trust: kernel checked, no proof holes or user axioms.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapShannon

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

noncomputable section

/-- Reachable normal forms below one audited source, as a finite type. -/
abbrev TerminalPoint {T : Type} [Fintype T]
    (R : T → T → Prop) (source : T) :=
  {x : T // x ∈ terminalSupport R source}

/-- A scheduler is a probability mass on the reachable terminal support. -/
structure TerminalScheduler {T : Type} [Fintype T]
    (R : T → T → Prop) (source : T) where
  mass : TerminalPoint R source → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  mass_sum_one : ∑ x, mass x = 1

/-- The terminal-point type has exactly the terminal multiplicity of the source. -/
theorem terminalPoint_card {T : Type} [Fintype T]
    (R : T → T → Prop) (source : T) :
    Fintype.card (TerminalPoint R source) = terminalMultiplicity R source := by
  simp [TerminalPoint, terminalMultiplicity, Fintype.card_coe]

/-- Local normalization makes the terminal-point type inhabited. -/
theorem terminalPoint_nonempty_of_normalizingAt
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (hnorm : NormalizingAt R source) : Nonempty (TerminalPoint R source) := by
  rcases terminalSupport_nonempty_of_normalizingAt hnorm with ⟨x, hx⟩
  exact ⟨⟨x, hx⟩⟩

/-- A scheduler only has states inside the reachable terminal support, by type. -/
theorem scheduler_cannot_assign_outside_terminalSupport
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (_σ : TerminalScheduler R source) (x : TerminalPoint R source) :
    x.1 ∈ terminalSupport R source :=
  x.2

/-- Shannon entropy of the scheduler, in bits. -/
def schedulerEntropyBits
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source) : ℝ :=
  HBits σ.mass

/-- The Shannon-side overproduction gap. -/
def shannonOverproductionGap
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    (σ : TerminalScheduler R source)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) : ℝ :=
  schedulerEntropyBits σ - deficitBits μ ν r

/-- **W2 headline.** Any scheduler distribution on the reachable normal forms
lies below the Hartley overproduction envelope. -/
theorem shannon_overproduction_le_hartley
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (hnorm : NormalizingAt R source)
    (σ : TerminalScheduler R source)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    shannonOverproductionGap R source σ μ ν r ≤
      overproductionGap R source μ ν r := by
  letI : Nonempty (TerminalPoint R source) :=
    terminalPoint_nonempty_of_normalizingAt hnorm
  have hH := HBits_le_logb_card σ.mass σ.mass_nonneg σ.mass_sum_one
  have hcard : Fintype.card (TerminalPoint R source) = terminalMultiplicity R source :=
    terminalPoint_card R source
  have hEnvelope : schedulerEntropyBits σ ≤ terminalHartleyEntropy R source := by
    unfold schedulerEntropyBits terminalHartleyEntropy
    simpa [hcard] using hH
  unfold shannonOverproductionGap overproductionGap
  exact sub_le_sub_right hEnvelope _

/-- The uniform scheduler on a locally normalizing source. -/
def uniformTerminalScheduler
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (hnorm : NormalizingAt R source) : TerminalScheduler R source := by
  letI : Nonempty (TerminalPoint R source) :=
    terminalPoint_nonempty_of_normalizingAt hnorm
  exact
    { mass := uniformMass (TerminalPoint R source)
      mass_nonneg := fun _ => le_of_lt (one_div_pos.mpr (card_cast_pos _))
      mass_sum_one := uniformMass_sum_one _ }

/-- The uniform scheduler attains the terminal Hartley envelope. -/
theorem uniform_scheduler_entropy_eq_hartley
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (hnorm : NormalizingAt R source) :
    schedulerEntropyBits (uniformTerminalScheduler hnorm) =
      terminalHartleyEntropy R source := by
  letI : Nonempty (TerminalPoint R source) :=
    terminalPoint_nonempty_of_normalizingAt hnorm
  unfold schedulerEntropyBits uniformTerminalScheduler terminalHartleyEntropy
  rw [HBits_uniformMass_eq_logb_card]
  rw [terminalPoint_card]

/-- **Sharpness.** The Hartley gap is exactly the Shannon gap of the uniform
scheduler on reachable terminals. -/
theorem uniform_shannonGap_eq_hartleyGap
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (hnorm : NormalizingAt R source)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    shannonOverproductionGap R source (uniformTerminalScheduler hnorm) μ ν r =
      overproductionGap R source μ ν r := by
  unfold shannonOverproductionGap overproductionGap
  rw [uniform_scheduler_entropy_eq_hartley hnorm]

/-- Residual licensed entropy expressed in bits. -/
def condEntropyLicensedBits
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) : ℝ :=
  condEntropyLicensed μ ν r / Real.log 2

/-- **Novelty fence / aligned collapse.** If the scheduler entropy is exactly
the target's direct conditional entropy, the Shannon overproduction gap is
ordinary residual conditional entropy (equivocation), expressed in bits. -/
theorem shannonGap_eq_condEntropyLicensedBits_of_entropy_alignment
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (halign : H σ.mass = condEntropyDirect μ ν r) :
    shannonOverproductionGap R source σ μ ν r =
      condEntropyLicensedBits μ ν r := by
  unfold shannonOverproductionGap schedulerEntropyBits HBits
    deficitBits deficit condEntropyLicensedBits
  rw [halign]
  ring

/-- A fully resolving aligned channel leaves no Shannon overproduction. -/
theorem shannonGap_eq_zero_of_aligned_zero_residual
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (halign : H σ.mass = condEntropyDirect μ ν r)
    (hres : condEntropyLicensed μ ν r = 0) :
    shannonOverproductionGap R source σ μ ν r = 0 := by
  rw [shannonGap_eq_condEntropyLicensedBits_of_entropy_alignment σ μ ν r halign]
  simp [condEntropyLicensedBits, hres]

/-- On canonical raw Fork3 the uniform Shannon gap reproduces the existing
one-bit Hartley result against the echo channel. -/
theorem fork3_uniform_shannon_gap_eq_one :
    shannonOverproductionGap Fork3Step Fork3.source
      (uniformTerminalScheduler fork3_raw_normalizingAt_source)
      unitSurface uniformChannelWeights echoChannel = 1 := by
  rw [uniform_shannonGap_eq_hartleyGap fork3_raw_normalizingAt_source]
  exact fork3_raw_overproduction_eq_one

/-- The same uniform scheduler and relation have zero gap under the resolving
channel, retaining the original sharpness fence. -/
theorem fork3_uniform_shannon_gap_resolving_eq_zero :
    shannonOverproductionGap Fork3Step Fork3.source
      (uniformTerminalScheduler fork3_raw_normalizingAt_source)
      unitSurface uniformChannelWeights resolvingChannel = 0 := by
  rw [uniform_shannonGap_eq_hartleyGap fork3_raw_normalizingAt_source]
  exact fork3_raw_gap_closed_by_resolving_channel

/-- W2 receipt: distributional gap, Hartley envelope, uniform attainment,
aligned conditional-entropy collapse, and the canonical one-bit/zero-bit pair. -/
theorem shannon_overproduction_law :
    (∀ {T : Type} [Fintype T] {R : T → T → Prop} {source : T},
      NormalizingAt R source → ∀ (σ : TerminalScheduler R source),
      ∀ {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
        (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ),
        shannonOverproductionGap R source σ μ ν r ≤
          overproductionGap R source μ ν r) ∧
    shannonOverproductionGap Fork3Step Fork3.source
      (uniformTerminalScheduler fork3_raw_normalizingAt_source)
      unitSurface uniformChannelWeights echoChannel = 1 ∧
    shannonOverproductionGap Fork3Step Fork3.source
      (uniformTerminalScheduler fork3_raw_normalizingAt_source)
      unitSurface uniformChannelWeights resolvingChannel = 0 :=
  by
    refine ⟨?_, fork3_uniform_shannon_gap_eq_one,
      fork3_uniform_shannon_gap_resolving_eq_zero⟩
    intro T instT R source hnorm σ X W Cn instX instW instCn μ ν r
    exact shannon_overproduction_le_hartley hnorm σ μ ν r

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapShannon
