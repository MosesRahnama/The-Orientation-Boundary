import OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
import OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
import OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingProductQuotient
import OperatorKO7.Meta.DistinctionBoundary.MinimalForkQuantitative

/-!
# Independent-product additivity and sequential non-additivity of Omega

This module proves the two composition results demanded by the Omega research
program.

For asynchronous independent products, exact reachability and normality factor,
so reachable terminal multiplicity multiplies and terminal Hartley entropy
adds.  For independent normalized evidence channels, the direct and licensed
conditional entropies add by product Shannon entropy and weighted-product
averaging.  Hence the licensed deficit and Omega add exactly.

The sequential law is false in general.  A five-state overwrite system has two
binary stages, but the second stage erases the first choice from the terminal
state.  Each standalone Fork3 component has one bit of echo overproduction,
while the sequential composite still has only one bit, not two.

Trust: kernel checked; no proof holes or user axioms.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapProduct

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingProductQuotient
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

noncomputable section

universe u v

/-! ## Exact reachability and operational product -/

/-- Exact-length reachability is equivalent to Mathlib's reflexive-transitive
closure. -/
theorem reach_iff_reflTransGen {T : Type u} {R : T → T → Prop} {x y : T} :
    Reach R x y ↔ Relation.ReflTransGen R x y := by
  constructor
  · rintro ⟨n, h⟩
    induction h with
    | zero => exact Relation.ReflTransGen.refl
    | succ hxy hyz ih =>
        exact (Relation.ReflTransGen.single hxy).trans ih
  · intro h
    induction h with
    | refl => exact reach_refl _
    | tail hab hbc ih => exact reach_trans ih (reach_step hbc)

/-- Exact `Reach` on the asynchronous product is componentwise. -/
theorem productReach_iff
    {A : Type u} {B : Type v} {R : A → A → Prop} {S : B → B → Prop}
    {a a' : A} {b b' : B} :
    Reach (ProductStep R S) (a, b) (a', b') ↔
      Reach R a a' ∧ Reach S b b' := by
  rw [reach_iff_reflTransGen, reach_iff_reflTransGen, reach_iff_reflTransGen]
  exact productStep_star_iff

/-- A product state is normal exactly when both components are normal. -/
theorem productNormalForm_iff
    {A : Type u} {B : Type v} {R : A → A → Prop} {S : B → B → Prop}
    (a : A) (b : B) :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm
        (ProductStep R S) (a, b) ↔
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm R a ∧
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm S b := by
  constructor
  · intro h
    constructor
    · intro a' ha'
      exact h (a', b) (ProductStep.left ha')
    · intro b' hb'
      exact h (a, b') (ProductStep.right hb')
  · rintro ⟨ha, hb⟩ y hy
    cases hy with
    | left hleft => exact ha _ hleft
    | right hright => exact hb _ hright

/-- Product terminal-support membership is componentwise. -/
theorem mem_terminalSupport_product_iff
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {R : A → A → Prop} {S : B → B → Prop}
    {a a' : A} {b b' : B} :
    (a', b') ∈ terminalSupport (ProductStep R S) (a, b) ↔
      a' ∈ terminalSupport R a ∧ b' ∈ terminalSupport S b := by
  constructor
  · intro h
    rcases mem_terminalSupport.mp h with ⟨hr, hn⟩
    rcases productReach_iff.mp hr with ⟨hra, hrb⟩
    rcases productNormalForm_iff a' b' |>.mp hn with ⟨hna, hnb⟩
    exact ⟨mem_terminalSupport.mpr ⟨hra, hna⟩,
      mem_terminalSupport.mpr ⟨hrb, hnb⟩⟩
  · rintro ⟨ha, hb⟩
    rcases mem_terminalSupport.mp ha with ⟨hra, hna⟩
    rcases mem_terminalSupport.mp hb with ⟨hrb, hnb⟩
    exact mem_terminalSupport.mpr
      ⟨productReach_iff.mpr ⟨hra, hrb⟩,
        (productNormalForm_iff a' b').mpr ⟨hna, hnb⟩⟩

/-- The product terminal support is exactly the Cartesian product of the factor
supports. -/
theorem terminalSupport_product_eq
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (R : A → A → Prop) (S : B → B → Prop) (a : A) (b : B) :
    terminalSupport (ProductStep R S) (a, b) =
      terminalSupport R a ×ˢ terminalSupport S b := by
  classical
  ext p
  rw [Finset.mem_product]
  exact mem_terminalSupport_product_iff

/-- Reachable terminal multiplicities multiply under asynchronous product. -/
theorem terminalMultiplicity_product
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (R : A → A → Prop) (S : B → B → Prop) (a : A) (b : B) :
    terminalMultiplicity (ProductStep R S) (a, b) =
      terminalMultiplicity R a * terminalMultiplicity S b := by
  unfold terminalMultiplicity
  rw [terminalSupport_product_eq, Finset.card_product]

/-- Under local normalization in both factors, terminal Hartley entropy is
additive. -/
theorem terminalHartleyEntropy_product
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {R : A → A → Prop} {S : B → B → Prop} {a : A} {b : B}
    (hR : NormalizingAt R a) (hS : NormalizingAt S b) :
    terminalHartleyEntropy (ProductStep R S) (a, b) =
      terminalHartleyEntropy R a + terminalHartleyEntropy S b := by
  have hRp : (terminalMultiplicity R a : ℝ) ≠ 0 := by
    exact_mod_cast (terminalMultiplicity_pos_of_normalizingAt hR).ne'
  have hSp : (terminalMultiplicity S b : ℝ) ≠ 0 := by
    exact_mod_cast (terminalMultiplicity_pos_of_normalizingAt hS).ne'
  unfold terminalHartleyEntropy
  rw [terminalMultiplicity_product, Nat.cast_mul, Real.logb_mul hRp hSp]

/-! ## Independent normalized channel products -/

/-- The normalization assumptions needed for exact channel-product algebra. -/
structure NormalizedChannel
    {X W C : Type} [Fintype X] [Fintype W] [Fintype C]
    (μ : W → ℝ) (ν : W → C → ℝ) (r : W → C → X → ℝ) : Prop where
  direct_sum_one : ∑ w, μ w = 1
  channel_sum_one : ∀ w, ∑ c, ν w c = 1
  target_sum_one : ∀ w c, ∑ x, r w c x = 1

/-- Product direct-surface mass. -/
def productMu {W₁ W₂ : Type}
    (μ₁ : W₁ → ℝ) (μ₂ : W₂ → ℝ) : W₁ × W₂ → ℝ :=
  fun w => μ₁ w.1 * μ₂ w.2

/-- Product licensed-channel mass. -/
def productNu {W₁ W₂ C₁ C₂ : Type}
    (ν₁ : W₁ → C₁ → ℝ) (ν₂ : W₂ → C₂ → ℝ) :
    W₁ × W₂ → C₁ × C₂ → ℝ :=
  fun w c => ν₁ w.1 c.1 * ν₂ w.2 c.2

/-- Product target conditional. -/
def productConditional {W₁ W₂ C₁ C₂ X₁ X₂ : Type}
    (r₁ : W₁ → C₁ → X₁ → ℝ) (r₂ : W₂ → C₂ → X₂ → ℝ) :
    W₁ × W₂ → C₁ × C₂ → X₁ × X₂ → ℝ :=
  fun w c x => r₁ w.1 c.1 x.1 * r₂ w.2 c.2 x.2

/-- Sum of a product mass is the product of the sums. -/
theorem sum_product_mass
    {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) :
    (∑ z : A × B, p z.1 * q z.2) = (∑ a, p a) * (∑ b, q b) := by
  rw [Fintype.sum_prod_type]
  calc
    ∑ a, ∑ b, p a * q b = ∑ a, p a * (∑ b, q b) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ = (∑ a, p a) * (∑ b, q b) := by rw [Finset.sum_mul]

/-- Weighted product averaging preserves addition when both weights are
normalized. -/
theorem weightedProductAverageAdd
    {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f : A → ℝ) (g : B → ℝ)
    (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1) :
    (∑ z : A × B, (p z.1 * q z.2) * (f z.1 + g z.2)) =
      (∑ a, p a * f a) + (∑ b, q b * g b) := by
  rw [Fintype.sum_prod_type]
  calc
    ∑ a, ∑ b, (p a * q b) * (f a + g b) =
      ∑ a, ((p a * f a) * (∑ b, q b) +
        p a * (∑ b, q b * g b)) := by
          apply Finset.sum_congr rfl
          intro a ha
          calc
            ∑ b, (p a * q b) * (f a + g b) =
                ∑ b, ((p a * f a) * q b + p a * (q b * g b)) := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  ring
            _ = (∑ b, (p a * f a) * q b) +
                ∑ b, p a * (q b * g b) := Finset.sum_add_distrib
            _ = (p a * f a) * (∑ b, q b) +
                p a * (∑ b, q b * g b) := by
                  rw [Finset.mul_sum, Finset.mul_sum]
    _ = ∑ a, (p a * f a + p a * (∑ b, q b * g b)) := by
      rw [hq]
      simp
    _ = (∑ a, p a * f a) +
        (∑ a, p a * (∑ b, q b * g b)) := Finset.sum_add_distrib
    _ = (∑ a, p a * f a) +
        (∑ a, p a) * (∑ b, q b * g b) := by rw [Finset.sum_mul]
    _ = _ := by rw [hp, one_mul]

/-- Independent product channel data remain normalized. -/
theorem normalizedChannel_product
    {X₁ X₂ W₁ W₂ C₁ C₂ : Type}
    [Fintype X₁] [Fintype X₂] [Fintype W₁] [Fintype W₂]
    [Fintype C₁] [Fintype C₂]
    {μ₁ : W₁ → ℝ} {μ₂ : W₂ → ℝ}
    {ν₁ : W₁ → C₁ → ℝ} {ν₂ : W₂ → C₂ → ℝ}
    {r₁ : W₁ → C₁ → X₁ → ℝ} {r₂ : W₂ → C₂ → X₂ → ℝ}
    (h₁ : NormalizedChannel μ₁ ν₁ r₁)
    (h₂ : NormalizedChannel μ₂ ν₂ r₂) :
    NormalizedChannel (productMu μ₁ μ₂) (productNu ν₁ ν₂)
      (productConditional r₁ r₂) := by
  constructor
  · change (∑ z : W₁ × W₂, μ₁ z.1 * μ₂ z.2) = 1
    rw [sum_product_mass, h₁.direct_sum_one, h₂.direct_sum_one, one_mul]
  · intro w
    change (∑ z : C₁ × C₂, ν₁ w.1 z.1 * ν₂ w.2 z.2) = 1
    rw [sum_product_mass, h₁.channel_sum_one, h₂.channel_sum_one, one_mul]
  · intro w c
    change (∑ z : X₁ × X₂, r₁ w.1 c.1 z.1 * r₂ w.2 c.2 z.2) = 1
    rw [sum_product_mass, h₁.target_sum_one, h₂.target_sum_one, one_mul]

/-- A normalized channel mixture is a normalized target distribution. -/
theorem mixture_sum_one
    {X C : Type} [Fintype X] [Fintype C]
    (ν : C → ℝ) (r : C → X → ℝ)
    (hν : ∑ c, ν c = 1) (hr : ∀ c, ∑ x, r c x = 1) :
    ∑ x, mixture ν r x = 1 := by
  unfold mixture
  rw [Finset.sum_comm]
  calc
    ∑ c, ∑ x, ν c * r c x = ∑ c, ν c * (∑ x, r c x) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ = ∑ c, ν c := by simp [hr]
    _ = 1 := hν

/-- The mixture of product channel data factors pointwise. -/
theorem mixture_product
    {X₁ X₂ C₁ C₂ : Type}
    [Fintype X₁] [Fintype X₂] [Fintype C₁] [Fintype C₂]
    (ν₁ : C₁ → ℝ) (ν₂ : C₂ → ℝ)
    (r₁ : C₁ → X₁ → ℝ) (r₂ : C₂ → X₂ → ℝ) :
    mixture (fun c : C₁ × C₂ => ν₁ c.1 * ν₂ c.2)
        (fun (c : C₁ × C₂) (x : X₁ × X₂) => r₁ c.1 x.1 * r₂ c.2 x.2) =
      fun x : X₁ × X₂ => mixture ν₁ r₁ x.1 * mixture ν₂ r₂ x.2 := by
  funext x
  unfold mixture
  rw [Fintype.sum_prod_type]
  calc
    ∑ c₁, ∑ c₂, (ν₁ c₁ * ν₂ c₂) * (r₁ c₁ x.1 * r₂ c₂ x.2) =
      ∑ c₁, (ν₁ c₁ * r₁ c₁ x.1) *
        (∑ c₂, ν₂ c₂ * r₂ c₂ x.2) := by
          apply Finset.sum_congr rfl
          intro c₁ hc₁
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c₂ hc₂
          ring
    _ = (∑ c₁, ν₁ c₁ * r₁ c₁ x.1) *
        (∑ c₂, ν₂ c₂ * r₂ c₂ x.2) := by rw [Finset.sum_mul]

/-- Direct conditional entropy is additive under independent normalized
products. -/
theorem condEntropyDirect_product
    {X₁ X₂ W₁ W₂ C₁ C₂ : Type}
    [Fintype X₁] [Fintype X₂] [Fintype W₁] [Fintype W₂]
    [Fintype C₁] [Fintype C₂]
    {μ₁ : W₁ → ℝ} {μ₂ : W₂ → ℝ}
    {ν₁ : W₁ → C₁ → ℝ} {ν₂ : W₂ → C₂ → ℝ}
    {r₁ : W₁ → C₁ → X₁ → ℝ} {r₂ : W₂ → C₂ → X₂ → ℝ}
    (h₁ : NormalizedChannel μ₁ ν₁ r₁)
    (h₂ : NormalizedChannel μ₂ ν₂ r₂) :
    condEntropyDirect (productMu μ₁ μ₂) (productNu ν₁ ν₂)
        (productConditional r₁ r₂) =
      condEntropyDirect μ₁ ν₁ r₁ + condEntropyDirect μ₂ ν₂ r₂ := by
  let f₁ : W₁ → ℝ := fun w => H (mixture (ν₁ w) (r₁ w))
  let f₂ : W₂ → ℝ := fun w => H (mixture (ν₂ w) (r₂ w))
  have hcell : ∀ (w₁ : W₁) (w₂ : W₂),
      H (mixture
          (fun c : C₁ × C₂ => ν₁ w₁ c.1 * ν₂ w₂ c.2)
          (fun (c : C₁ × C₂) (x : X₁ × X₂) =>
            r₁ w₁ c.1 x.1 * r₂ w₂ c.2 x.2)) = f₁ w₁ + f₂ w₂ := by
    intro w₁ w₂
    rw [mixture_product]
    exact H_product _ _
      (mixture_sum_one _ _ (h₁.channel_sum_one w₁) (h₁.target_sum_one w₁))
      (mixture_sum_one _ _ (h₂.channel_sum_one w₂) (h₂.target_sum_one w₂))
  unfold condEntropyDirect productMu productNu productConditional
  change (∑ w : W₁ × W₂, (μ₁ w.1 * μ₂ w.2) *
      H (mixture
        (fun c : C₁ × C₂ => ν₁ w.1 c.1 * ν₂ w.2 c.2)
        (fun (c : C₁ × C₂) (x : X₁ × X₂) =>
          r₁ w.1 c.1 x.1 * r₂ w.2 c.2 x.2))) = _
  simp_rw [hcell]
  simpa [f₁, f₂, condEntropyDirect] using
    weightedProductAverageAdd μ₁ μ₂ f₁ f₂ h₁.direct_sum_one h₂.direct_sum_one

/-- Licensed conditional entropy is additive under independent normalized
products. -/
theorem condEntropyLicensed_product
    {X₁ X₂ W₁ W₂ C₁ C₂ : Type}
    [Fintype X₁] [Fintype X₂] [Fintype W₁] [Fintype W₂]
    [Fintype C₁] [Fintype C₂]
    {μ₁ : W₁ → ℝ} {μ₂ : W₂ → ℝ}
    {ν₁ : W₁ → C₁ → ℝ} {ν₂ : W₂ → C₂ → ℝ}
    {r₁ : W₁ → C₁ → X₁ → ℝ} {r₂ : W₂ → C₂ → X₂ → ℝ}
    (h₁ : NormalizedChannel μ₁ ν₁ r₁)
    (h₂ : NormalizedChannel μ₂ ν₂ r₂) :
    condEntropyLicensed (productMu μ₁ μ₂) (productNu ν₁ ν₂)
        (productConditional r₁ r₂) =
      condEntropyLicensed μ₁ ν₁ r₁ + condEntropyLicensed μ₂ ν₂ r₂ := by
  let g₁ : W₁ → ℝ := fun w => ∑ c, ν₁ w c * H (r₁ w c)
  let g₂ : W₂ → ℝ := fun w => ∑ c, ν₂ w c * H (r₂ w c)
  have hinner : ∀ (w₁ : W₁) (w₂ : W₂),
      (∑ c : C₁ × C₂, (ν₁ w₁ c.1 * ν₂ w₂ c.2) *
        H (fun x : X₁ × X₂ => r₁ w₁ c.1 x.1 * r₂ w₂ c.2 x.2)) =
        g₁ w₁ + g₂ w₂ := by
    intro w₁ w₂
    have hH : ∀ (c₁ : C₁) (c₂ : C₂),
        H (fun x : X₁ × X₂ => r₁ w₁ c₁ x.1 * r₂ w₂ c₂ x.2) =
          H (r₁ w₁ c₁) + H (r₂ w₂ c₂) := by
      intro c₁ c₂
      exact H_product _ _ (h₁.target_sum_one w₁ c₁) (h₂.target_sum_one w₂ c₂)
    simp_rw [hH]
    simpa [g₁, g₂] using
      weightedProductAverageAdd (ν₁ w₁) (ν₂ w₂)
        (fun c₁ => H (r₁ w₁ c₁)) (fun c₂ => H (r₂ w₂ c₂))
        (h₁.channel_sum_one w₁) (h₂.channel_sum_one w₂)
  unfold condEntropyLicensed productMu productNu productConditional
  change (∑ w : W₁ × W₂, (μ₁ w.1 * μ₂ w.2) *
      (∑ c : C₁ × C₂, (ν₁ w.1 c.1 * ν₂ w.2 c.2) *
        H (fun x : X₁ × X₂ => r₁ w.1 c.1 x.1 * r₂ w.2 c.2 x.2))) = _
  simp_rw [hinner]
  simpa [g₁, g₂, condEntropyLicensed] using
    weightedProductAverageAdd μ₁ μ₂ g₁ g₂ h₁.direct_sum_one h₂.direct_sum_one

/-- Licensed conditional mutual-information gain is additive under independent
normalized products. -/
theorem deficit_product
    {X₁ X₂ W₁ W₂ C₁ C₂ : Type}
    [Fintype X₁] [Fintype X₂] [Fintype W₁] [Fintype W₂]
    [Fintype C₁] [Fintype C₂]
    {μ₁ : W₁ → ℝ} {μ₂ : W₂ → ℝ}
    {ν₁ : W₁ → C₁ → ℝ} {ν₂ : W₂ → C₂ → ℝ}
    {r₁ : W₁ → C₁ → X₁ → ℝ} {r₂ : W₂ → C₂ → X₂ → ℝ}
    (h₁ : NormalizedChannel μ₁ ν₁ r₁)
    (h₂ : NormalizedChannel μ₂ ν₂ r₂) :
    deficit (productMu μ₁ μ₂) (productNu ν₁ ν₂) (productConditional r₁ r₂) =
      deficit μ₁ ν₁ r₁ + deficit μ₂ ν₂ r₂ := by
  unfold deficit
  rw [condEntropyDirect_product h₁ h₂, condEntropyLicensed_product h₁ h₂]
  ring

/-- Deficit in bits is additive as well. -/
theorem deficitBits_product
    {X₁ X₂ W₁ W₂ C₁ C₂ : Type}
    [Fintype X₁] [Fintype X₂] [Fintype W₁] [Fintype W₂]
    [Fintype C₁] [Fintype C₂]
    {μ₁ : W₁ → ℝ} {μ₂ : W₂ → ℝ}
    {ν₁ : W₁ → C₁ → ℝ} {ν₂ : W₂ → C₂ → ℝ}
    {r₁ : W₁ → C₁ → X₁ → ℝ} {r₂ : W₂ → C₂ → X₂ → ℝ}
    (h₁ : NormalizedChannel μ₁ ν₁ r₁)
    (h₂ : NormalizedChannel μ₂ ν₂ r₂) :
    deficitBits (productMu μ₁ μ₂) (productNu ν₁ ν₂) (productConditional r₁ r₂) =
      deficitBits μ₁ ν₁ r₁ + deficitBits μ₂ ν₂ r₂ := by
  unfold deficitBits
  rw [deficit_product h₁ h₂]
  ring

/-- **W3 headline.** Omega is additive for independent asynchronous operational
products with independently producted normalized evidence channels. -/
theorem overproductionGap_independent_product
    {A B : Type} [Fintype A] [Fintype B]
    {R : A → A → Prop} {S : B → B → Prop} {a : A} {b : B}
    (hR : NormalizingAt R a) (hS : NormalizingAt S b)
    {X₁ X₂ W₁ W₂ C₁ C₂ : Type}
    [Fintype X₁] [Fintype X₂] [Fintype W₁] [Fintype W₂]
    [Fintype C₁] [Fintype C₂]
    {μ₁ : W₁ → ℝ} {μ₂ : W₂ → ℝ}
    {ν₁ : W₁ → C₁ → ℝ} {ν₂ : W₂ → C₂ → ℝ}
    {r₁ : W₁ → C₁ → X₁ → ℝ} {r₂ : W₂ → C₂ → X₂ → ℝ}
    (hc₁ : NormalizedChannel μ₁ ν₁ r₁)
    (hc₂ : NormalizedChannel μ₂ ν₂ r₂) :
    overproductionGap (ProductStep R S) (a, b)
        (productMu μ₁ μ₂) (productNu ν₁ ν₂) (productConditional r₁ r₂) =
      overproductionGap R a μ₁ ν₁ r₁ + overproductionGap S b μ₂ ν₂ r₂ := by
  unfold overproductionGap
  rw [terminalHartleyEntropy_product hR hS, deficitBits_product hc₁ hc₂]
  ring

/-! ## Sequential overwrite countermodel -/

inductive SequentialOverwriteNode where
  | source
  | mid0
  | mid1
  | final0
  | final1
  deriving DecidableEq, Fintype

/-- Two binary stages in sequence, where the second stage overwrites the first
choice in the terminal state. -/
inductive SequentialOverwriteStep : SequentialOverwriteNode → SequentialOverwriteNode → Prop
  | first0 : SequentialOverwriteStep .source .mid0
  | first1 : SequentialOverwriteStep .source .mid1
  | second00 : SequentialOverwriteStep .mid0 .final0
  | second01 : SequentialOverwriteStep .mid0 .final1
  | second10 : SequentialOverwriteStep .mid1 .final0
  | second11 : SequentialOverwriteStep .mid1 .final1

/-- First final state is normal. -/
theorem sequential_final0_normal :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm
      SequentialOverwriteStep .final0 := by
  intro y h
  cases h

/-- Second final state is normal. -/
theorem sequential_final1_normal :
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm
      SequentialOverwriteStep .final1 := by
  intro y h
  cases h

/-- Exactly the second-stage outcomes remain terminal. -/
theorem sequential_terminalSupport_eq :
    terminalSupport SequentialOverwriteStep .source = {.final0, .final1} := by
  classical
  ext x
  cases x with
  | source =>
      constructor
      · intro hx
        exact False.elim ((mem_terminalSupport.mp hx).2 .mid0 SequentialOverwriteStep.first0)
      · simp
  | mid0 =>
      constructor
      · intro hx
        exact False.elim ((mem_terminalSupport.mp hx).2 .final0 SequentialOverwriteStep.second00)
      · simp
  | mid1 =>
      constructor
      · intro hx
        exact False.elim ((mem_terminalSupport.mp hx).2 .final0 SequentialOverwriteStep.second10)
      · simp
  | final0 =>
      constructor
      · intro _; simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_trans (reach_step SequentialOverwriteStep.first0)
            (reach_step SequentialOverwriteStep.second00), sequential_final0_normal⟩
  | final1 =>
      constructor
      · intro _; simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_trans (reach_step SequentialOverwriteStep.first0)
            (reach_step SequentialOverwriteStep.second01), sequential_final1_normal⟩

/-- Sequential overwrite has two terminal results. -/
theorem sequential_terminalMultiplicity_eq_two :
    terminalMultiplicity SequentialOverwriteStep .source = 2 := by
  simp [terminalMultiplicity, sequential_terminalSupport_eq]

/-- Its Hartley branch entropy is one bit. -/
theorem sequential_terminalHartleyEntropy_eq_one :
    terminalHartleyEntropy SequentialOverwriteStep .source = 1 := by
  unfold terminalHartleyEntropy
  rw [sequential_terminalMultiplicity_eq_two]
  exact Real.logb_self_eq_one (by norm_num)

/-- Against echo evidence, sequential overwrite has one bit of Omega. -/
theorem sequential_echo_overproduction_eq_one :
    overproductionGap SequentialOverwriteStep .source
      unitSurface uniformChannelWeights echoChannel = 1 := by
  unfold overproductionGap
  rw [sequential_terminalHartleyEntropy_eq_one, echoChannel_deficitBits_zero]
  ring

/-- **W3 countermodel.** Sequential composition is not additive in general: the
second stage erases the first-stage distinction, leaving one bit instead of two. -/
theorem sequential_composition_not_additive :
    overproductionGap SequentialOverwriteStep .source
        unitSurface uniformChannelWeights echoChannel ≠
      overproductionGap Fork3Step Fork3.source
          unitSurface uniformChannelWeights echoChannel +
        overproductionGap Fork3Step Fork3.source
          unitSurface uniformChannelWeights echoChannel := by
  rw [sequential_echo_overproduction_eq_one, fork3_raw_overproduction_eq_one]
  norm_num

/-- W3 receipt. -/
theorem overproduction_product_law :
    (overproductionGap SequentialOverwriteStep .source
        unitSurface uniformChannelWeights echoChannel ≠
      overproductionGap Fork3Step Fork3.source unitSurface uniformChannelWeights echoChannel +
        overproductionGap Fork3Step Fork3.source unitSurface uniformChannelWeights echoChannel) ∧
    terminalMultiplicity (ProductStep Fork3Step Fork3Step)
        (Fork3.source, Fork3.source) = 4 := by
  refine ⟨sequential_composition_not_additive, ?_⟩
  rw [terminalMultiplicity_product, fork3_raw_terminalMultiplicity_eq_two]

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapProduct
