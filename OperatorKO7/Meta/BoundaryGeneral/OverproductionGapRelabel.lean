import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapTransport
import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite

/-!
# Evidence-channel relabeling and full Omega invariance

An exact operational isomorphism is only half of the transport story.  The
licensed evidence surface may itself be renamed.  This module proves that finite
conditional entropy, licensed deficit, and Omega are invariant under arbitrary
equivalences of the direct-surface, channel, and target alphabets when the
probability data are transported by pullback along those equivalences.

Together with `relIso_overproductionGap_eq`, this gives a simultaneous transport
theorem for both the operational relation and the evidence channel.

Trust: kernel checked; no proof holes or user axioms.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRelabel

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapTransport

noncomputable section

/-- Relabel the direct-surface mass by pullback. -/
def relabelMu {W W' : Type} (eW : W ≃ W') (μ : W → ℝ) : W' → ℝ :=
  fun w' => μ (eW.symm w')

/-- Relabel the licensed-channel mass by pullback in both indices. -/
def relabelNu {W W' C C' : Type}
    (eW : W ≃ W') (eC : C ≃ C') (ν : W → C → ℝ) : W' → C' → ℝ :=
  fun w' c' => ν (eW.symm w') (eC.symm c')

/-- Relabel target conditionals by pullback in all three indices. -/
def relabelConditional {W W' C C' X X' : Type}
    (eW : W ≃ W') (eC : C ≃ C') (eX : X ≃ X')
    (r : W → C → X → ℝ) : W' → C' → X' → ℝ :=
  fun w' c' x' => r (eW.symm w') (eC.symm c') (eX.symm x')

/-- The target mixture commutes with channel/target relabeling. -/
theorem mixture_relabel
    {C C' X X' : Type} [Fintype C] [Fintype C'] [Fintype X] [Fintype X']
    (eC : C ≃ C') (eX : X ≃ X')
    (ν : C → ℝ) (r : C → X → ℝ) :
    mixture (fun c' => ν (eC.symm c'))
        (fun c' x' => r (eC.symm c') (eX.symm x')) =
      fun x' => mixture ν r (eX.symm x') := by
  funext x'
  unfold mixture
  exact Equiv.sum_comp eC.symm
    (fun c => ν c * r c (eX.symm x'))

/-- Entropy of the mixture is invariant under channel/target relabeling. -/
theorem H_mixture_relabel
    {C C' X X' : Type} [Fintype C] [Fintype C'] [Fintype X] [Fintype X']
    (eC : C ≃ C') (eX : X ≃ X')
    (ν : C → ℝ) (r : C → X → ℝ) :
    H (mixture (fun c' => ν (eC.symm c'))
        (fun c' x' => r (eC.symm c') (eX.symm x'))) =
      H (mixture ν r) := by
  rw [mixture_relabel]
  exact H_relabel_eq eX (mixture ν r)

/-- Direct conditional entropy is invariant under a simultaneous finite
relabeling of all its alphabets. -/
theorem condEntropyDirect_relabel
    {W W' C C' X X' : Type}
    [Fintype W] [Fintype W'] [Fintype C] [Fintype C'] [Fintype X] [Fintype X']
    (eW : W ≃ W') (eC : C ≃ C') (eX : X ≃ X')
    (μ : W → ℝ) (ν : W → C → ℝ) (r : W → C → X → ℝ) :
    condEntropyDirect (relabelMu eW μ) (relabelNu eW eC ν)
        (relabelConditional eW eC eX r) =
      condEntropyDirect μ ν r := by
  unfold condEntropyDirect relabelMu relabelNu relabelConditional
  have hcell : ∀ w' : W',
      H (fun x' : X' => ∑ c' : C',
          ν (eW.symm w') (eC.symm c') *
            r (eW.symm w') (eC.symm c') (eX.symm x')) =
        H (fun x : X => ∑ c : C,
          ν (eW.symm w') c * r (eW.symm w') c x) := by
    intro w'
    change H (mixture (fun c' => ν (eW.symm w') (eC.symm c'))
        (fun c' x' => r (eW.symm w') (eC.symm c') (eX.symm x'))) =
      H (mixture (ν (eW.symm w')) (r (eW.symm w')))
    exact H_mixture_relabel eC eX (ν (eW.symm w')) (r (eW.symm w'))
  simp_rw [hcell]
  exact Equiv.sum_comp eW.symm
    (fun w => μ w * H (mixture (ν w) (r w)))

/-- Licensed conditional entropy is invariant under the same relabeling. -/
theorem condEntropyLicensed_relabel
    {W W' C C' X X' : Type}
    [Fintype W] [Fintype W'] [Fintype C] [Fintype C'] [Fintype X] [Fintype X']
    (eW : W ≃ W') (eC : C ≃ C') (eX : X ≃ X')
    (μ : W → ℝ) (ν : W → C → ℝ) (r : W → C → X → ℝ) :
    condEntropyLicensed (relabelMu eW μ) (relabelNu eW eC ν)
        (relabelConditional eW eC eX r) =
      condEntropyLicensed μ ν r := by
  unfold condEntropyLicensed relabelMu relabelNu relabelConditional
  have htarget : ∀ (w' : W') (c' : C'),
      H (fun x' => r (eW.symm w') (eC.symm c') (eX.symm x')) =
        H (r (eW.symm w') (eC.symm c')) := by
    intro w' c'
    exact H_relabel_eq eX (r (eW.symm w') (eC.symm c'))
  simp_rw [htarget]
  have hinner : ∀ w' : W',
      (∑ c' : C', ν (eW.symm w') (eC.symm c') *
        H (r (eW.symm w') (eC.symm c'))) =
      ∑ c : C, ν (eW.symm w') c * H (r (eW.symm w') c) := by
    intro w'
    exact Equiv.sum_comp eC.symm
      (fun c => ν (eW.symm w') c * H (r (eW.symm w') c))
  simp_rw [hinner]
  exact Equiv.sum_comp eW.symm
    (fun w => μ w * ∑ c, ν w c * H (r w c))

/-- Licensed-channel deficit is invariant under relabeling. -/
theorem deficit_relabel
    {W W' C C' X X' : Type}
    [Fintype W] [Fintype W'] [Fintype C] [Fintype C'] [Fintype X] [Fintype X']
    (eW : W ≃ W') (eC : C ≃ C') (eX : X ≃ X')
    (μ : W → ℝ) (ν : W → C → ℝ) (r : W → C → X → ℝ) :
    deficit (relabelMu eW μ) (relabelNu eW eC ν)
        (relabelConditional eW eC eX r) = deficit μ ν r := by
  unfold deficit
  rw [condEntropyDirect_relabel, condEntropyLicensed_relabel]

/-- The deficit in bits is invariant under relabeling. -/
theorem deficitBits_relabel
    {W W' C C' X X' : Type}
    [Fintype W] [Fintype W'] [Fintype C] [Fintype C'] [Fintype X] [Fintype X']
    (eW : W ≃ W') (eC : C ≃ C') (eX : X ≃ X')
    (μ : W → ℝ) (ν : W → C → ℝ) (r : W → C → X → ℝ) :
    deficitBits (relabelMu eW μ) (relabelNu eW eC ν)
        (relabelConditional eW eC eX r) = deficitBits μ ν r := by
  unfold deficitBits
  rw [deficit_relabel]

/-- **Full W4 transport theorem.** Simultaneously relabeling the operational
carrier by a relation isomorphism and the three evidence alphabets by
equivalences leaves Omega unchanged. -/
theorem overproductionGap_full_relabel
    {A B : Type} [Fintype A] [Fintype B]
    {RA : A → A → Prop} {RB : B → B → Prop}
    (eR : OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso RA RB)
    (source : A)
    {W W' C C' X X' : Type}
    [Fintype W] [Fintype W'] [Fintype C] [Fintype C'] [Fintype X] [Fintype X']
    (eW : W ≃ W') (eC : C ≃ C') (eX : X ≃ X')
    (μ : W → ℝ) (ν : W → C → ℝ) (r : W → C → X → ℝ) :
    overproductionGap RB (eR.toEquiv source)
        (relabelMu eW μ) (relabelNu eW eC ν) (relabelConditional eW eC eX r) =
      overproductionGap RA source μ ν r := by
  unfold overproductionGap
  rw [deficitBits_relabel]
  rw [← relIso_terminalHartleyEntropy_eq eR source]

/-- Relabeling is a pure representation change on the evidence side. -/
theorem evidence_relabel_is_lossless :
    ∀ {W W' C C' X X' : Type}
      [Fintype W] [Fintype W'] [Fintype C] [Fintype C'] [Fintype X] [Fintype X']
      (eW : W ≃ W') (eC : C ≃ C') (eX : X ≃ X')
      (μ : W → ℝ) (ν : W → C → ℝ) (r : W → C → X → ℝ),
      deficitBits (relabelMu eW μ) (relabelNu eW eC ν)
        (relabelConditional eW eC eX r) = deficitBits μ ν r :=
  deficitBits_relabel

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRelabel
