import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapOrder

/-!
# Omega under resource changes

A resource state records an operational Hartley envelope and licensed evidence in bits. A free move does not increase the envelope and does not decrease licensed evidence. Since Omega is envelope minus evidence, it does not increase under a free move.
-/
set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapResource

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

structure OmegaResourceState where
  envelopeBits : Real
  evidenceBits : Real

def OmegaResourceState.omega (S : OmegaResourceState) : Real :=
  S.envelopeBits - S.evidenceBits

def FreeMove (A B : OmegaResourceState) : Prop :=
  B.envelopeBits ≤ A.envelopeBits ∧ A.evidenceBits ≤ B.evidenceBits

theorem freeMove_refl (A : OmegaResourceState) : FreeMove A A :=
  ⟨le_rfl, le_rfl⟩

theorem freeMove_trans {A B C : OmegaResourceState}
    (hAB : FreeMove A B) (hBC : FreeMove B C) : FreeMove A C :=
  ⟨le_trans hBC.1 hAB.1, le_trans hAB.2 hBC.2⟩

theorem omega_monotone_freeMove {A B : OmegaResourceState}
    (h : FreeMove A B) : B.omega ≤ A.omega := by
  rcases h with ⟨hH, hD⟩
  dsimp [OmegaResourceState.omega]
  linarith

theorem evidenceUpgrade_free (h0 d0 d1 : Real) (h : d0 ≤ d1) :
    FreeMove ⟨h0, d0⟩ ⟨h0, d1⟩ :=
  ⟨le_rfl, h⟩

theorem abstraction_free (h0 h1 d : Real) (h : h1 ≤ h0) :
    FreeMove ⟨h0, d⟩ ⟨h1, d⟩ :=
  ⟨h, le_rfl⟩

noncomputable def resourceStateOf
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W C : Type} [Fintype X] [Fintype W] [Fintype C]
    (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real) :
    OmegaResourceState :=
  ⟨terminalHartleyEntropy R source, deficitBits μ ν r⟩

theorem resourceStateOf_omega
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T)
    {X W C : Type} [Fintype X] [Fintype W] [Fintype C]
    (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real) :
    (resourceStateOf R source μ ν r).omega = overproductionGap R source μ ν r := by
  rfl

def FullyWarranted (S : OmegaResourceState) : Prop :=
  S.envelopeBits ≤ S.evidenceBits

theorem fullyWarranted_iff_omega_nonpos (S : OmegaResourceState) :
    FullyWarranted S ↔ S.omega ≤ 0 := by
  constructor
  · intro h
    dsimp [OmegaResourceState.omega]
    exact sub_nonpos.mpr h
  · intro h
    dsimp [OmegaResourceState.omega] at h
    exact sub_nonpos.mp h

theorem fullyWarranted_not_positiveOmega (S : OmegaResourceState)
    (h : FullyWarranted S) : ¬ 0 < S.omega := by
  have hz := (fullyWarranted_iff_omega_nonpos S).mp h
  linarith

theorem fullyWarranted_preserved_by_freeMove {A B : OmegaResourceState}
    (hfree : FreeMove A B) (hA : FullyWarranted A) : FullyWarranted B := by
  rcases hfree with ⟨hH, hD⟩
  dsimp [FullyWarranted] at hA ⊢
  linarith

theorem omega_resource_theory_law :
    (∀ A : OmegaResourceState, FreeMove A A) ∧
    (∀ {A B C : OmegaResourceState}, FreeMove A B → FreeMove B C → FreeMove A C) ∧
    (∀ {A B : OmegaResourceState}, FreeMove A B → B.omega ≤ A.omega) ∧
    (∀ S : OmegaResourceState, FullyWarranted S → ¬ 0 < S.omega) :=
  ⟨freeMove_refl, freeMove_trans, omega_monotone_freeMove,
    fullyWarranted_not_positiveOmega⟩

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapResource

