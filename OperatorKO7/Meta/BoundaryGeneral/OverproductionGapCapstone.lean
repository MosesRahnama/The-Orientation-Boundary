import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapSchedulerChannel
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapProduct
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRelabel
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapOrder

/-!
# Omega research-program capstone

This file is the proof-carrying terminal surface for the Omega research program.
It contains no new primitive axiom.  Its receipt bundles the theorem families
that make Omega more than a definition:

* scheduler/Shannon refinement below the Hartley envelope;
* explicit echo and terminal-resolving scheduler channels;
* independent-product additivity and a sequential non-additivity countermodel;
* exact operational and evidence-alphabet transport invariance;
* forward-simulation and release-only transport counterexamples;
* exact sign classification, a negative Omega witness, and evidence monotonicity;
* the aligned Shannon collapse to ordinary residual conditional entropy.

The literature novelty gate is external evidence and therefore is not a Lean
field.  Its formal shadow is the aligned-collapse theorem: the aligned case is
mechanically ordinary equivocation, preventing an overclaim of novelty.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapCapstone

open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapShannon
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapSchedulerChannel
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapProduct
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapTransport
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRelabel
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapOrder
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingProductQuotient
open OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryObjectFunctor
open OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryDetermination

noncomputable section

/-- Proof-carrying receipt for the complete formal Omega program. -/
structure OmegaTheoryReceipt : Prop where
  schedulerEnvelope :
    ∀ {T : Type} [Fintype T] {R : T → T → Prop} {source : T},
      NormalizingAt R source → ∀ (σ : TerminalScheduler R source),
      ∀ {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
        (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ),
        shannonOverproductionGap R source σ μ ν r ≤
          overproductionGap R source μ ν r
  resolvingSchedulerZero :
    ∀ {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
      (σ : TerminalScheduler R source),
      shannonOverproductionGap R source σ schedulerUnitMass
        (schedulerResolvingWeight σ) schedulerResolvingConditional = 0
  independentProductAdditive :
    ∀ {A B : Type} [Fintype A] [Fintype B]
      {R : A → A → Prop} {S : B → B → Prop} {a : A} {b : B},
      NormalizingAt R a → NormalizingAt S b →
      ∀ {X₁ X₂ W₁ W₂ C₁ C₂ : Type}
        [Fintype X₁] [Fintype X₂] [Fintype W₁] [Fintype W₂]
        [Fintype C₁] [Fintype C₂]
        {μ₁ : W₁ → ℝ} {μ₂ : W₂ → ℝ}
        {ν₁ : W₁ → C₁ → ℝ} {ν₂ : W₂ → C₂ → ℝ}
        {r₁ : W₁ → C₁ → X₁ → ℝ} {r₂ : W₂ → C₂ → X₂ → ℝ},
        NormalizedChannel μ₁ ν₁ r₁ → NormalizedChannel μ₂ ν₂ r₂ →
        overproductionGap (ProductStep R S) (a, b)
            (productMu μ₁ μ₂) (productNu ν₁ ν₂) (productConditional r₁ r₂) =
          overproductionGap R a μ₁ ν₁ r₁ + overproductionGap S b μ₂ ν₂ r₂
  sequentialCounterexample :
    overproductionGap SequentialOverwriteStep .source
        unitSurface uniformChannelWeights echoChannel ≠
      overproductionGap Fork3Step Fork3.source unitSurface uniformChannelWeights echoChannel +
        overproductionGap Fork3Step Fork3.source unitSurface uniformChannelWeights echoChannel
  relationIsoInvariant :
    ∀ {A B : Type} [Fintype A] [Fintype B]
      {RA : A → A → Prop} {RB : B → B → Prop}
      (e : OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso RA RB) (source : A)
      {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
      (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ),
      overproductionGap RA source μ ν r =
        overproductionGap RB (e.toEquiv source) μ ν r
  fullRelabelInvariant :
    ∀ {A B : Type} [Fintype A] [Fintype B]
      {RA : A → A → Prop} {RB : B → B → Prop}
      (eR : OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso RA RB) (source : A)
      {W W' C C' X X' : Type}
      [Fintype W] [Fintype W'] [Fintype C] [Fintype C'] [Fintype X] [Fintype X']
      (eW : W ≃ W') (eC : C ≃ C') (eX : X ≃ X')
      (μ : W → ℝ) (ν : W → C → ℝ) (r : W → C → X → ℝ),
      overproductionGap RB (eR.toEquiv source)
          (relabelMu eW μ) (relabelNu eW eC ν) (relabelConditional eW eC eX r) =
        overproductionGap RA source μ ν r
  simulationCounterexample :
    ForwardSimulation fork3Collapse Fork3Step BoolForkStep ∧
      overproductionGap Fork3Step Fork3.source unitSurface uniformChannelWeights echoChannel ≠
        overproductionGap BoolForkStep (fork3Collapse Fork3.source)
          unitSurface uniformChannelWeights echoChannel
  releaseIsoInsufficient :
    Nonempty (ReleaseIso staticBoolBoundaryIso releaseDataA releaseDataA) ∧
      overproductionGap (restrictedDynamics staticBoolDatum) (boolBoundary false)
          unitSurface uniformChannelWeights echoChannel ≠
        overproductionGap (restrictedDynamics staticBoolDatum) (boolBoundary false)
          unitSurface uniformChannelWeights resolvingChannel
  signCharacterization :
    ∀ {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
      {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
      (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ),
      0 ≤ overproductionGap R source μ ν r ↔
        CapacityCompatible R source μ ν r
  negativeWitness :
    overproductionGap ChainStep .source
      unitSurface uniformChannelWeights resolvingChannel = -1
  evidenceMonotone :
    ∀ {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
      {X₁ W₁ C₁ X₂ W₂ C₂ : Type}
      [Fintype X₁] [Fintype W₁] [Fintype C₁]
      [Fintype X₂] [Fintype W₂] [Fintype C₂]
      (μ₁ : W₁ → ℝ) (ν₁ : W₁ → C₁ → ℝ) (r₁ : W₁ → C₁ → X₁ → ℝ)
      (μ₂ : W₂ → ℝ) (ν₂ : W₂ → C₂ → ℝ) (r₂ : W₂ → C₂ → X₂ → ℝ),
      deficitBits μ₁ ν₁ r₁ ≤ deficitBits μ₂ ν₂ r₂ →
        overproductionGap R source μ₂ ν₂ r₂ ≤
          overproductionGap R source μ₁ ν₁ r₁
  alignedCollapse :
    ∀ {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
      (σ : TerminalScheduler R source)
      {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
      (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ),
      OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite.H σ.mass =
          condEntropyDirect μ ν r →
        shannonOverproductionGap R source σ μ ν r =
          condEntropyLicensedBits μ ν r
  canonicalForkEvent :
    overproductionGap Fork3Step Fork3.source
      unitSurface uniformChannelWeights echoChannel = 1
  canonicalForkResolved :
    overproductionGap Fork3Step Fork3.source
      unitSurface uniformChannelWeights resolvingChannel = 0

/-- The complete formal Omega program is inhabited.

Every field is discharged by referencing its theorem directly. An explicit
lambda cannot be used here: each field interleaves implicit type binders and
`Fintype` instance binders between its explicit arguments, so Lean's implicit
lambda feature binds the written names to the type variables instead of to the
mass, weight, and conditional functions. -/
theorem omegaTheoryReceipt : OmegaTheoryReceipt where
  schedulerEnvelope := shannon_overproduction_le_hartley
  resolvingSchedulerZero := schedulerResolving_shannonGap_eq_zero
  independentProductAdditive := overproductionGap_independent_product
  sequentialCounterexample := sequential_composition_not_additive
  relationIsoInvariant := relIso_overproductionGap_eq
  fullRelabelInvariant := overproductionGap_full_relabel
  simulationCounterexample := forwardSimulation_does_not_preserve_overproduction
  releaseIsoInsufficient := releaseIso_alone_does_not_determine_overproduction
  signCharacterization := overproductionGap_nonneg_iff
  negativeWitness := chain_resolving_overproduction_eq_neg_one
  -- Referenced directly: an explicit lambda cannot bind these fields, whose
  -- instance binders sit between the explicit ones, so the lambda arguments
  -- would line up against the `Fintype` instances instead of the mass functions.
  evidenceMonotone := more_evidence_lowers_overproduction
  alignedCollapse := shannonGap_eq_condEntropyLicensedBits_of_entropy_alignment
  canonicalForkEvent := fork3_raw_overproduction_eq_one
  canonicalForkResolved := fork3_raw_gap_closed_by_resolving_channel

/-- The old one-bit Fork3 theorem remains an exact projection of the capstone. -/
theorem omegaCapstone_recovers_original_fork3 :
    overproductionGap Fork3Step Fork3.source
      unitSurface uniformChannelWeights echoChannel = 1 :=
  omegaTheoryReceipt.canonicalForkEvent

/-- The capstone also carries the exact resolving-channel falsifier. -/
theorem omegaCapstone_recovers_resolving_falsifier :
    overproductionGap Fork3Step Fork3.source
      unitSurface uniformChannelWeights resolvingChannel = 0 :=
  omegaTheoryReceipt.canonicalForkResolved

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapCapstone
