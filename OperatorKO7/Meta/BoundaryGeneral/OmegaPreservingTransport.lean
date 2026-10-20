import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRelabel
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapInvariantLimits

/-!
# Omega-preserving transports

An operational relation isomorphism and equivalences of the finite evidence alphabets preserve Omega when the evidence data are pulled back through those equivalences. The converse does not hold: two finite chains can have equal Omega while different carrier cardinalities rule out a relation isomorphism.
-/
set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.OmegaPreservingTransport

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRelabel

/-- Constructs the identity relation isomorphism. -/
noncomputable def relIsoRefl {A : Type} (R : A → A → Prop) :
    OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso R R where
  toEquiv := Equiv.refl A
  map_rel_iff := Iff.rfl

/-- A relation isomorphism and equivalences of all finite evidence alphabets preserve Omega. -/
theorem coupled_relabel_preserves_omega
    {A B W W' C C' X X' : Type}
    [Fintype A] [Fintype B] [Fintype W] [Fintype W']
    [Fintype C] [Fintype C'] [Fintype X] [Fintype X']
    {RA : A → A → Prop} {RB : B → B → Prop}
    (eR : OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso RA RB)
    (eW : W ≃ W') (eC : C ≃ C') (eX : X ≃ X')
    (source : A)
    (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real) :
    overproductionGap RB (eR.toEquiv source)
        (relabelMu eW μ) (relabelNu eW eC ν) (relabelConditional eW eC eX r) =
      overproductionGap RA source μ ν r :=
  overproductionGap_full_relabel eR source eW eC eX μ ν r

/-- Identity transport is included in the preservation class. -/
theorem identity_transport_preserves_omega
    {A W C X : Type} [Fintype A] [Fintype W] [Fintype C] [Fintype X]
    (R : A → A → Prop) (source : A)
    (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real) :
    overproductionGap R source μ ν r = overproductionGap R source μ ν r := rfl

/-- Equal Omega values do not imply a coupled relation/evidence transport: the two chains have equal Omega but different cardinalities, so no relation isomorphism exists. -/
theorem omega_equality_does_not_imply_relation_isomorphism :
    overproductionGap
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.ChainStep
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.ChainNode.source
        unitSurface uniformChannelWeights echoChannel =
      overproductionGap
        OperatorKO7.Meta.BoundaryGeneral.OverproductionGapInvariantLimits.LongChainStep
        OperatorKO7.Meta.BoundaryGeneral.OverproductionGapInvariantLimits.LongChainNode.source
        unitSurface uniformChannelWeights echoChannel ∧
    ¬ Nonempty
      (OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso
        OperatorKO7.Meta.DistinctionBoundary.Quantitative.ChainStep
        OperatorKO7.Meta.BoundaryGeneral.OverproductionGapInvariantLimits.LongChainStep) := by
  exact ⟨(OperatorKO7.Meta.BoundaryGeneral.OverproductionGapInvariantLimits.omega_and_terminalMultiplicity_not_complete_invariant).1,
    OperatorKO7.Meta.BoundaryGeneral.OverproductionGapInvariantLimits.no_relIso_shortChain_longChain⟩

/-- Coupled relabeling is sufficient for Omega preservation; equality of Omega alone is insufficient by the chain example. -/
theorem omega_preserving_transport_sufficient_law :
    ∀ {A B W W' C C' X X' : Type}
      [Fintype A] [Fintype B] [Fintype W] [Fintype W']
      [Fintype C] [Fintype C'] [Fintype X] [Fintype X']
      {RA : A → A → Prop} {RB : B → B → Prop}
      (eR : OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso RA RB)
      (eW : W ≃ W') (eC : C ≃ C') (eX : X ≃ X')
      (source : A) (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real),
      overproductionGap RB (eR.toEquiv source)
          (relabelMu eW μ) (relabelNu eW eC ν) (relabelConditional eW eC eX r) =
        overproductionGap RA source μ ν r :=
  coupled_relabel_preserves_omega

/-- Coupled relation and evidence relabeling is a sufficient preservation class, but Omega equality alone does not characterize that class. -/
theorem omega_preserving_transport_characterization_resolved :
    (∀ {A B W W' C C' X X' : Type}
      [Fintype A] [Fintype B] [Fintype W] [Fintype W']
      [Fintype C] [Fintype C'] [Fintype X] [Fintype X']
      {RA : A → A → Prop} {RB : B → B → Prop}
      (eR : OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso RA RB)
      (eW : W ≃ W') (eC : C ≃ C') (eX : X ≃ X')
      (source : A) (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real),
      overproductionGap RB (eR.toEquiv source)
          (relabelMu eW μ) (relabelNu eW eC ν) (relabelConditional eW eC eX r) =
        overproductionGap RA source μ ν r) ∧
    (∃ (A B : Type) (_ : Fintype A) (_ : Fintype B)
      (RA : A → A → Prop) (RB : B → B → Prop)
      (a : A) (b : B),
      overproductionGap RA a unitSurface uniformChannelWeights echoChannel =
        overproductionGap RB b unitSurface uniformChannelWeights echoChannel ∧
      ¬ Nonempty (OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso RA RB)) := by
  constructor
  · exact omega_preserving_transport_sufficient_law
  · exact ⟨
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.ChainNode,
      OperatorKO7.Meta.BoundaryGeneral.OverproductionGapInvariantLimits.LongChainNode,
      inferInstance, inferInstance,
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.ChainStep,
      OperatorKO7.Meta.BoundaryGeneral.OverproductionGapInvariantLimits.LongChainStep,
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.ChainNode.source,
      OperatorKO7.Meta.BoundaryGeneral.OverproductionGapInvariantLimits.LongChainNode.source,
      omega_equality_does_not_imply_relation_isomorphism⟩

end OperatorKO7.Meta.BoundaryGeneral.OmegaPreservingTransport
