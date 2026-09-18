import OperatorKO7.Meta.OperationalInexpressibility.LicenseGalois
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# Observer-relative license stabilizers

The stabilizer of an observer consists of the permutations of its source that
preserve every observer value. Its orbits are exactly the observer fibers.
Consequently, a target is licensed exactly when it is invariant under the
stabilizer, observer refinement is subgroup inclusion, equal observer kernels
are equal stabilizers, and the stabilizer is trivial exactly for injective
observers. All statements hold for arbitrary source and observation types.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

universe u v w u'

/-- Permutations that preserve the observer value pointwise. -/
def licenseStabilizer {X : Type u} {Q : Type v} (q : X → Q) :
    Subgroup (Equiv.Perm X) where
  carrier := {σ | ∀ x, q (σ x) = q x}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro σ τ hσ hτ x
    change q (σ (τ x)) = q x
    exact (hσ (τ x)).trans (hτ x)
  inv_mem' := by
    intro σ hσ x
    have h := hσ (σ⁻¹ x)
    simpa using h.symm

@[simp] theorem mem_licenseStabilizer_iff {X : Type u} {Q : Type v}
    (q : X → Q) (σ : Equiv.Perm X) :
    σ ∈ licenseStabilizer q ↔ ∀ x, q (σ x) = q x :=
  Iff.rfl

/-- The transposition of two source points, defined without adding decidable
equality to the public observer theorems. -/
noncomputable def observerSwap {X : Type u} (x y : X) : Equiv.Perm X := by
  classical
  exact Equiv.swap x y

/-- A transposition inside one observer fiber belongs to the stabilizer. -/
theorem swap_mem_licenseStabilizer_of_eq {X : Type u} {Q : Type v}
    (q : X → Q) {x y : X} (hxy : q x = q y) :
    observerSwap x y ∈ licenseStabilizer q := by
  classical
  intro z
  by_cases hzx : z = x
  · subst z
    simpa [observerSwap] using hxy.symm
  by_cases hzy : z = y
  · subst z
    simpa [observerSwap] using hxy
  rw [observerSwap, Equiv.swap_apply_of_ne_of_ne hzx hzy]

/-- Licensed targets are exactly the functions invariant under every
observer-preserving permutation. -/
theorem licensed_iff_stabilizer_invariant
    {X : Type u} {Q : Type v} {V : Type w} (q : X → Q) (P : X → V) :
    Licensed q P ↔
      ∀ σ : licenseStabilizer q, ∀ x, P (σ.1 x) = P x := by
  classical
  constructor
  · intro h σ x
    exact h (σ.1 x) x (σ.2 x)
  · intro h x y hxy
    let σ : licenseStabilizer q :=
      ⟨observerSwap x y, swap_mem_licenseStabilizer_of_eq q hxy⟩
    have hσ := h σ x
    have hyx : P y = P x := by
      simpa [σ, observerSwap] using hσ
    exact hyx.symm

/-- The stabilizer orbit relation is exactly equality of observer values. -/
theorem same_fiber_iff_stabilizer_orbit
    {X : Type u} {Q : Type v} (q : X → Q) (x y : X) :
    q x = q y ↔ ∃ σ : licenseStabilizer q, σ.1 x = y := by
  classical
  constructor
  · intro hxy
    refine ⟨⟨observerSwap x y, swap_mem_licenseStabilizer_of_eq q hxy⟩, ?_⟩
    simp [observerSwap]
  · rintro ⟨σ, hσ⟩
    have hpres := σ.2 x
    rw [hσ] at hpres
    exact hpres.symm

/-- Observer refinement is inclusion of observer-relative stabilizers in the
same direction: a finer observer has a smaller stabilizer. -/
theorem observerRefines_iff_licenseStabilizer_le
    {X : Type u} {QFine : Type v} {QCoarse : Type u'}
    (qFine : X → QFine) (qCoarse : X → QCoarse) :
    ObserverRefines qFine qCoarse ↔
      licenseStabilizer qFine ≤ licenseStabilizer qCoarse := by
  classical
  constructor
  · intro href σ hσ x
    exact href (hσ x)
  · intro hsub x y hxy
    have hswapFine : observerSwap x y ∈ licenseStabilizer qFine :=
      swap_mem_licenseStabilizer_of_eq qFine hxy
    have hswapCoarse := hsub hswapFine
    have hyx := hswapCoarse x
    have : qCoarse y = qCoarse x := by
      simpa [observerSwap] using hyx
    exact this.symm

/-- Two observers have the same kernel exactly when they have the same
observer-relative stabilizer. -/
theorem same_kernel_iff_licenseStabilizer_eq
    {X : Type u} {Q₁ : Type v} {Q₂ : Type u'}
    (q₁ : X → Q₁) (q₂ : X → Q₂) :
    (∀ x y, q₁ x = q₁ y ↔ q₂ x = q₂ y) ↔
      licenseStabilizer q₁ = licenseStabilizer q₂ := by
  rw [← mutual_refinement_iff_same_kernel]
  constructor
  · rintro ⟨h12, h21⟩
    apply le_antisymm
    · exact (observerRefines_iff_licenseStabilizer_le q₁ q₂).mp h12
    · exact (observerRefines_iff_licenseStabilizer_le q₂ q₁).mp h21
  · intro h
    constructor
    · apply (observerRefines_iff_licenseStabilizer_le q₁ q₂).mpr
      exact le_of_eq h
    · apply (observerRefines_iff_licenseStabilizer_le q₂ q₁).mpr
      exact le_of_eq h.symm

/-- The observer stabilizer is trivial exactly when the observer is injective. -/
theorem licenseStabilizer_eq_bot_iff_injective
    {X : Type u} {Q : Type v} (q : X → Q) :
    licenseStabilizer q = ⊥ ↔ Function.Injective q := by
  classical
  constructor
  · intro hbot x y hxy
    have hswap : observerSwap x y ∈ licenseStabilizer q :=
      swap_mem_licenseStabilizer_of_eq q hxy
    have hmemBot : observerSwap x y ∈ (⊥ : Subgroup (Equiv.Perm X)) := by
      rw [← hbot]
      exact hswap
    have hperm : observerSwap x y = 1 := Subgroup.mem_bot.mp hmemBot
    have happ := congrArg (fun σ : Equiv.Perm X => σ x) hperm
    simpa [observerSwap] using happ.symm
  · intro hinj
    apply le_antisymm
    · intro σ hσ
      apply Subgroup.mem_bot.mpr
      ext x
      apply hinj
      simpa using hσ x
    · exact bot_le

/-- Strict observer refinement is strict stabilizer inclusion. -/
theorem observerRefines_strict_iff_licenseStabilizer_lt
    {X : Type u} {QFine : Type v} {QCoarse : Type u'}
    (qFine : X → QFine) (qCoarse : X → QCoarse) :
    (ObserverRefines qFine qCoarse ∧ ¬ ObserverRefines qCoarse qFine) ↔
      licenseStabilizer qFine < licenseStabilizer qCoarse := by
  rw [lt_iff_le_not_ge]
  constructor
  · rintro ⟨hFine, hNotCoarse⟩
    exact ⟨(observerRefines_iff_licenseStabilizer_le qFine qCoarse).mp hFine,
      fun hrev => hNotCoarse
        ((observerRefines_iff_licenseStabilizer_le qCoarse qFine).mpr hrev)⟩
  · rintro ⟨hle, hnle⟩
    exact ⟨(observerRefines_iff_licenseStabilizer_le qFine qCoarse).mpr hle,
      fun href => hnle
        ((observerRefines_iff_licenseStabilizer_le qCoarse qFine).mp href)⟩

/-! ## Exact fiber-product structure -/

/-- The ordinary fiber of an observer over an attained value. -/
abbrev ObserverFiber {X : Type u} {Q : Type v} (q : X → Q)
    (y : Set.range q) : Type u :=
  {x : X // q x = y.1}

/-- The fiber of the range-valued observer is the ordinary fiber over the
underlying attained value. -/
def rangeFiberEquiv {X : Type u} {Q : Type v} (q : X → Q)
    (y : Set.range q) :
    {x : X // Set.rangeFactorization q x = y} ≃ ObserverFiber q y where
  toFun x := ⟨x.1, congrArg Subtype.val x.2⟩
  invFun x := ⟨x.1, Subtype.ext x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The ordinary observer stabilizer is the double-opposite form of the
domain-action stabilizer used by Mathlib's fiber decomposition. -/
def licenseStabilizerDomEquiv {X : Type u} {Q : Type v} (q : X → Q) :
    licenseStabilizer q ≃*
      (MulAction.stabilizer (Equiv.Perm X)ᵈᵐᵃ
        (Set.rangeFactorization q))ᵐᵒᵖ where
  toFun σ := MulOpposite.op ⟨DomMulAct.mk σ.1, by
    apply DomMulAct.mem_stabilizer_iff.mpr
    funext x
    apply Subtype.ext
    exact σ.2 x⟩
  invFun τ := ⟨DomMulAct.mk.symm τ.unop.1, by
    intro x
    have hcomp := DomMulAct.mem_stabilizer_iff.mp τ.unop.2
    exact congrArg Subtype.val (congrFun hcomp x)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Exact group decomposition: an observer-preserving permutation is one
independent permutation of each attained observer fiber. -/
def licenseStabilizerFiberMulEquiv
    {X : Type u} {Q : Type v} (q : X → Q) :
    licenseStabilizer q ≃*
      (∀ y : Set.range q, Equiv.Perm (ObserverFiber q y)) :=
  (licenseStabilizerDomEquiv q).trans
    ((DomMulAct.stabilizerMulEquiv (Set.rangeFactorization q)).trans
      (MulEquiv.piCongrRight fun y =>
        Equiv.Perm.permCongrHom (rangeFiberEquiv q y)))

/-- For a finite source, the stabilizer order is the product of the factorials
of the attained fiber sizes. No finite ambient observation type is required. -/
theorem natCard_licenseStabilizer_eq_prod_factorial
    {X : Type u} {Q : Type v} [Finite X] (q : X → Q) :
    Nat.card (licenseStabilizer q) =
      (letI : Fintype (Set.range q) := Fintype.ofFinite (Set.range q)
       ∏ y : Set.range q, Nat.factorial (Nat.card (ObserverFiber q y))) := by
  classical
  letI : Fintype (Set.range q) := Fintype.ofFinite (Set.range q)
  change Nat.card (licenseStabilizer q) =
    ∏ y : Set.range q, Nat.factorial (Nat.card (ObserverFiber q y))
  rw [Nat.card_congr (licenseStabilizerFiberMulEquiv q).toEquiv, Nat.card_pi]
  apply Finset.prod_congr rfl
  intro y _
  exact Nat.card_perm

/-! ## Observer stabilizers are not primitive-language automorphism groups -/

/-- A two-element carrier with a named primitive constant. -/
inductive PointedBit where
  | named
  | other
  deriving DecidableEq

/-- Automorphisms of the carrier that preserve its named constant. -/
def pointedAutomorphismGroup : Subgroup (Equiv.Perm PointedBit) where
  carrier := {σ | σ .named = .named}
  one_mem' := rfl
  mul_mem' := by
    intro σ τ hσ hτ
    change σ (τ .named) = .named
    rw [hτ, hσ]
  inv_mem' := by
    intro σ hσ
    apply σ.injective
    simpa using hσ.symm

/-- The constant observer forgets the primitive constant. -/
def pointedBitConstantObserver : PointedBit → Unit := fun _ => ()

theorem pointedAutomorphisms_le_observerStabilizer :
    pointedAutomorphismGroup ≤
      licenseStabilizer pointedBitConstantObserver := by
  intro σ _ x
  rfl

/-- Swapping the named and unnamed points preserves the constant observer. -/
theorem pointedBitSwap_mem_observerStabilizer :
    observerSwap PointedBit.named PointedBit.other ∈
      licenseStabilizer pointedBitConstantObserver := by
  apply swap_mem_licenseStabilizer_of_eq
  rfl

/-- The same swap is not an automorphism of the language with the named
constant. -/
theorem pointedBitSwap_not_mem_pointedAutomorphismGroup :
    observerSwap PointedBit.named PointedBit.other ∉
      pointedAutomorphismGroup := by
  intro h
  have hfix := h
  simp [pointedAutomorphismGroup, observerSwap] at hfix

/-- Observer-preserving symmetry can strictly exceed primitive-language
symmetry, even on two points. -/
theorem pointedAutomorphismGroup_lt_observerStabilizer :
    pointedAutomorphismGroup <
      licenseStabilizer pointedBitConstantObserver := by
  rw [lt_iff_le_not_ge]
  refine ⟨pointedAutomorphisms_le_observerStabilizer, ?_⟩
  intro hreverse
  exact pointedBitSwap_not_mem_pointedAutomorphismGroup
    (hreverse pointedBitSwap_mem_observerStabilizer)

/-- The stabilizer representation is exact: invariants, orbits, refinement,
kernel equality, and injectivity are all recovered without finiteness. -/
theorem license_stabilizer_complete
    {X : Type u} {Q : Type v} (q : X → Q) :
    (∀ {V : Type w} (P : X → V),
      Licensed q P ↔ ∀ σ : licenseStabilizer q, ∀ x, P (σ.1 x) = P x)
      ∧ (∀ x y, q x = q y ↔ ∃ σ : licenseStabilizer q, σ.1 x = y)
      ∧ (licenseStabilizer q = ⊥ ↔ Function.Injective q)
      ∧ Nonempty
        (licenseStabilizer q ≃*
          (∀ y : Set.range q, Equiv.Perm (ObserverFiber q y))) := by
  exact ⟨fun P => licensed_iff_stabilizer_invariant q P,
    fun x y => same_fiber_iff_stabilizer_orbit q x y,
    licenseStabilizer_eq_bot_iff_injective q,
    ⟨licenseStabilizerFiberMulEquiv q⟩⟩

end OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
