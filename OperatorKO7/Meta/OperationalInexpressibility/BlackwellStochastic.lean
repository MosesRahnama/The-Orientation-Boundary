import OperatorKO7.Meta.OperationalInexpressibility.BlackwellOrder
import OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology

/-!
# Comparison of finite experiments

A finite experiment supports at least the value of another in every finite decision problem
exactly when the other is obtained from it by a stochastic matrix. The converse separates the
target experiment from the convex hull of the deterministic post-processings of the source by a
hyperplane and reads the separating functional as a utility.

Relation: post-processing by stochastic matrices; domination of decision values.
Property: the two orders coincide; deterministic and gain-function forms.
Trust: kernel only; the separation theorem of Mathlib.
Scope: finite types with decidable equality; real matrices and utilities; nonempty output type
for the converse.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.BlackwellStochastic

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
open OperatorKO7.Meta.OperationalInexpressibility.BlackwellOrder

universe u v w

/-- A finite experiment with real transition probabilities. -/
structure RealExperiment (X : Type u) (O : Type v) [Fintype O] where
  kernel : X → O → ℝ
  nonneg : ∀ x o, 0 ≤ kernel x o
  sum_one : ∀ x, ∑ o, kernel x o = 1

variable {X : Type u} {O₁ : Type v} {O₂ : Type w}
variable [Fintype X] [DecidableEq X] [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]

/-- The value of the decision problem with actions `A` and utility `u`; the prior is part of `u`. -/
noncomputable def decisionValue {O : Type*} [Fintype O] {A : Type*} [Fintype A] [Nonempty A]
    (E : RealExperiment X O) (u : X → A → ℝ) : ℝ :=
  ∑ o, (Finset.univ : Finset A).sup' Finset.univ_nonempty fun a => ∑ x, E.kernel x o * u x a

/-- `E₂` is `E₁` followed by a stochastic matrix. -/
def IsGarbling (E₁ : RealExperiment X O₁) (E₂ : RealExperiment X O₂) : Prop :=
  ∃ K : O₁ → O₂ → ℝ, (∀ o₁ o₂, 0 ≤ K o₁ o₂) ∧ (∀ o₁, ∑ o₂, K o₁ o₂ = 1) ∧
    ∀ x o₂, E₂.kernel x o₂ = ∑ o₁, E₁.kernel x o₁ * K o₁ o₂

/-- `E₁` supports at least the value of `E₂` in every finite decision problem. -/
def Dominates (E₁ : RealExperiment X O₁) (E₂ : RealExperiment X O₂) : Prop :=
  ∀ (A : Type w) [Fintype A] [Nonempty A] (u : X → A → ℝ), decisionValue E₂ u ≤ decisionValue E₁ u

omit [DecidableEq X] [DecidableEq O₁] [DecidableEq O₂] in
/-- **Garbling lowers every decision value.** -/
theorem dominates_of_isGarbling {E₁ : RealExperiment X O₁} {E₂ : RealExperiment X O₂}
    (h : IsGarbling E₁ E₂) : Dominates E₁ E₂ := by
  obtain ⟨K, hK0, hK1, hE⟩ := h
  intro A _ _ u
  classical
  choose a ha using fun o₂ => Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := A))
    (fun a => ∑ x, E₂.kernel x o₂ * u x a)
  unfold decisionValue
  have h₂ : (∑ o₂, (Finset.univ : Finset A).sup' Finset.univ_nonempty
      (fun a => ∑ x, E₂.kernel x o₂ * u x a)) =
      ∑ o₂, ∑ x, E₂.kernel x o₂ * u x (a o₂) := by
    apply Finset.sum_congr rfl
    intro o₂ _
    exact (ha o₂).2
  rw [h₂]
  calc ∑ o₂, ∑ x, E₂.kernel x o₂ * u x (a o₂)
      = ∑ o₂, ∑ x, (∑ o₁, E₁.kernel x o₁ * K o₁ o₂) * u x (a o₂) := by
        apply Finset.sum_congr rfl
        intro o₂ _
        apply Finset.sum_congr rfl
        intro x _
        rw [hE x o₂]
    _ = ∑ o₁, ∑ o₂, K o₁ o₂ * (∑ x, E₁.kernel x o₁ * u x (a o₂)) := by
        have hpt : ∀ (o₂ : O₂) (x : X),
            (∑ o₁, E₁.kernel x o₁ * K o₁ o₂) * u x (a o₂) =
              ∑ o₁, K o₁ o₂ * (E₁.kernel x o₁ * u x (a o₂)) := by
          intro o₂ x
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro o₁ _
          ring
        simp only [hpt]
        calc ∑ o₂, ∑ x, ∑ o₁, K o₁ o₂ * (E₁.kernel x o₁ * u x (a o₂))
            = ∑ o₂, ∑ o₁, ∑ x, K o₁ o₂ * (E₁.kernel x o₁ * u x (a o₂)) := by
              apply Finset.sum_congr rfl
              intro o₂ _
              rw [Finset.sum_comm]
          _ = ∑ o₁, ∑ o₂, ∑ x, K o₁ o₂ * (E₁.kernel x o₁ * u x (a o₂)) :=
              Finset.sum_comm
          _ = ∑ o₁, ∑ o₂, K o₁ o₂ * (∑ x, E₁.kernel x o₁ * u x (a o₂)) := by
              apply Finset.sum_congr rfl
              intro o₁ _
              apply Finset.sum_congr rfl
              intro o₂ _
              rw [Finset.mul_sum]
    _ ≤ ∑ o₁, (Finset.univ : Finset A).sup' Finset.univ_nonempty
          (fun a => ∑ x, E₁.kernel x o₁ * u x a) := by
        apply Finset.sum_le_sum
        intro o₁ _
        calc ∑ o₂, K o₁ o₂ * (∑ x, E₁.kernel x o₁ * u x (a o₂))
            ≤ ∑ o₂, K o₁ o₂ *
                ((Finset.univ : Finset A).sup' Finset.univ_nonempty
                  (fun a => ∑ x, E₁.kernel x o₁ * u x a)) := by
              apply Finset.sum_le_sum
              intro o₂ _
              exact mul_le_mul_of_nonneg_left
                (Finset.le_sup' (fun a => ∑ x, E₁.kernel x o₁ * u x a) (Finset.mem_univ _))
                (hK0 o₁ o₂)
          _ = (∑ o₂, K o₁ o₂) *
                ((Finset.univ : Finset A).sup' Finset.univ_nonempty
                  (fun a => ∑ x, E₁.kernel x o₁ * u x a)) := by
              rw [Finset.sum_mul]
          _ = (Finset.univ : Finset A).sup' Finset.univ_nonempty
                (fun a => ∑ x, E₁.kernel x o₁ * u x a) := by
              rw [hK1 o₁, one_mul]

/-! ## The converse -/

/-- The deterministic post-processing of `E₁` by `g`, as a point of `X × O₂ → ℝ`. -/
def garblingPoint (E₁ : RealExperiment X O₁) (g : O₁ → O₂) : X × O₂ → ℝ :=
  fun p => ∑ o₁, if g o₁ = p.2 then E₁.kernel p.1 o₁ else 0

/-- The experiment `E₂` as a point of `X × O₂ → ℝ`. -/
def experimentPoint (E₂ : RealExperiment X O₂) : X × O₂ → ℝ := fun p => E₂.kernel p.1 p.2

omit [Fintype X] [DecidableEq X] [DecidableEq O₁] in
/-- A point of the convex hull of the deterministic post-processings is a garbling. -/
theorem isGarbling_of_mem_convexHull {E₁ : RealExperiment X O₁} {E₂ : RealExperiment X O₂}
    (h : experimentPoint E₂ ∈ convexHull ℝ (Set.range (garblingPoint E₁))) :
    IsGarbling E₁ E₂ := by
  classical
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 h
  choose g hg using hz
  refine ⟨fun o₁ o₂ => ∑ i, w i * (if g i o₁ = o₂ then 1 else 0), ?_, ?_, ?_⟩
  · intro o₁ o₂
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hw0 i) (by split_ifs <;> norm_num)
  · intro o₁
    calc ∑ o₂, ∑ i, w i * (if g i o₁ = o₂ then 1 else 0)
        = ∑ i, w i * (∑ o₂, if g i o₁ = o₂ then 1 else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
      _ = ∑ i, w i * 1 := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          rw [Finset.sum_ite_eq]
          simp
      _ = 1 := by simp [hw1]
  · intro x o₂
    have hcongr := congrFun hsum (x, o₂)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcongr
    have hz' : ∀ i, z i (x, o₂) = ∑ o₁, if g i o₁ = o₂ then E₁.kernel x o₁ else 0 := by
      intro i
      rw [← hg i]
      rfl
    simp only [hz', experimentPoint] at hcongr
    rw [← hcongr]
    calc ∑ i, w i * (∑ o₁, if g i o₁ = o₂ then E₁.kernel x o₁ else 0)
        = ∑ i, ∑ o₁, w i * (if g i o₁ = o₂ then E₁.kernel x o₁ else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
      _ = ∑ o₁, ∑ i, w i * (if g i o₁ = o₂ then E₁.kernel x o₁ else 0) := Finset.sum_comm
      _ = ∑ o₁, E₁.kernel x o₁ * (∑ i, w i * (if g i o₁ = o₂ then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro o₁ _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hc : g i o₁ = o₂
          · simp [hc]
            ring
          · simp [hc]

/-- A continuous linear functional on `X × O₂ → ℝ` is a weighted sum of coordinates. -/
theorem continuousLinearMap_apply_eq_sum (f : (X × O₂ → ℝ) →L[ℝ] ℝ) (v : X × O₂ → ℝ) :
    f v = ∑ x, ∑ o₂, v (x, o₂) * f (fun p => if (x, o₂) = p then 1 else 0) := by
  classical
  have h : f v = ∑ i : X × O₂, v i • f (fun j => if i = j then 1 else 0) :=
    LinearMap.pi_apply_eq_sum_univ (f : (X × O₂ → ℝ) →ₗ[ℝ] ℝ) v
  rw [h, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro o₂ _
  rw [smul_eq_mul]

omit [DecidableEq O₁] in
/-- **The converse.** Domination in every finite decision problem forces a garbling. -/
theorem isGarbling_of_dominates [Nonempty O₂] {E₁ : RealExperiment X O₁}
    {E₂ : RealExperiment X O₂} (h : Dominates E₁ E₂) : IsGarbling E₁ E₂ := by
  classical
  by_cases hmem : experimentPoint E₂ ∈ convexHull ℝ (Set.range (garblingPoint E₁))
  · exact isGarbling_of_mem_convexHull hmem
  · exfalso
    obtain ⟨f, s, hfs, hsf⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) (Set.Finite.isClosed_convexHull (Set.finite_range _)) hmem
    let W : X → O₂ → ℝ := fun x o₂ => f (fun p => if (x, o₂) = p then 1 else 0)
    have h4 : f (experimentPoint E₂) ≤ decisionValue E₂ W := by
      rw [continuousLinearMap_apply_eq_sum f (experimentPoint E₂)]
      unfold decisionValue
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro o₂ _
      exact Finset.le_sup' (fun a => ∑ x, E₂.kernel x o₂ * W x a) (Finset.mem_univ o₂)
    choose gstar hgstar using fun o₁ => Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty (α := O₂)) (fun a => ∑ x, E₁.kernel x o₁ * W x a)
    have h5 : decisionValue E₁ W = f (garblingPoint E₁ gstar) := by
      unfold decisionValue
      trans ∑ o₁, ∑ x, E₁.kernel x o₁ * W x (gstar o₁)
      · apply Finset.sum_congr rfl
        intro o₁ _
        exact (hgstar o₁).2
      · rw [continuousLinearMap_apply_eq_sum f (garblingPoint E₁ gstar)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        have hpt : ∑ o₁, E₁.kernel x o₁ * W x (gstar o₁) =
            ∑ o₂, (∑ o₁, if gstar o₁ = o₂ then E₁.kernel x o₁ else 0) * W x o₂ := by
          symm
          calc ∑ o₂, (∑ o₁, if gstar o₁ = o₂ then E₁.kernel x o₁ else 0) * W x o₂
              = ∑ o₂, ∑ o₁, (if gstar o₁ = o₂ then E₁.kernel x o₁ else 0) * W x o₂ := by
                apply Finset.sum_congr rfl
                intro o₂ _
                rw [Finset.sum_mul]
            _ = ∑ o₁, ∑ o₂, (if gstar o₁ = o₂ then E₁.kernel x o₁ else 0) * W x o₂ :=
                Finset.sum_comm
            _ = ∑ o₁, E₁.kernel x o₁ * W x (gstar o₁) := by
                apply Finset.sum_congr rfl
                intro o₁ _
                have hite : ∀ o₂, (if gstar o₁ = o₂ then E₁.kernel x o₁ else 0) * W x o₂ =
                    (if gstar o₁ = o₂ then E₁.kernel x o₁ * W x o₂ else 0) := by
                  intro o₂
                  by_cases hc : gstar o₁ = o₂ <;> simp [hc]
                simp only [hite]
                rw [Finset.sum_ite_eq]
                simp
        simp only [hpt]
        rfl
    have h6 : f (garblingPoint E₁ gstar) < s :=
      hfs _ (subset_convexHull ℝ _ ⟨gstar, rfl⟩)
    have hd := h O₂ W
    linarith

omit [DecidableEq O₁] in
/-- **Comparison of finite experiments.** -/
theorem isGarbling_iff_dominates [Nonempty O₂] (E₁ : RealExperiment X O₁)
    (E₂ : RealExperiment X O₂) : IsGarbling E₁ E₂ ↔ Dominates E₁ E₂ :=
  ⟨dominates_of_isGarbling, isGarbling_of_dominates⟩

/-! ## Corollaries and controls -/

/-- The deterministic experiment of an observer. -/
def RealExperiment.ofObserver {O : Type*} [Fintype O] [DecidableEq O] (q : X → O) :
    RealExperiment X O where
  kernel x o := if q x = o then 1 else 0
  nonneg x o := by split_ifs <;> norm_num
  sum_one x := by simp

omit [DecidableEq X] in
/-- **For observers, garbling is refinement.** -/
theorem isGarbling_ofObserver_iff_refines [Nonempty O₂] (q₁ : X → O₁) (q₂ : X → O₂) :
    IsGarbling (RealExperiment.ofObserver q₁) (RealExperiment.ofObserver q₂) ↔
      ObserverRefines q₁ q₂ := by
  classical
  constructor
  · intro h x y hxy
    obtain ⟨K, hK0, hK1, hK⟩ := h
    have hx := hK x (q₂ x)
    have hy := hK y (q₂ x)
    simp only [RealExperiment.ofObserver, ite_mul, one_mul, zero_mul] at hx hy
    rw [Finset.sum_ite_eq] at hx hy
    simp at hx hy
    rw [← hxy] at hy
    have h1 : (if q₂ y = q₂ x then (1 : ℝ) else 0) = 1 := hy.trans hx.symm
    by_cases hc : q₂ y = q₂ x
    · exact hc.symm
    · rw [if_neg hc] at h1
      norm_num at h1
  · intro h
    let g : O₁ → O₂ := fun o₁ => if h : ∃ x, q₁ x = o₁ then q₂ (Classical.choose h) else Classical.arbitrary O₂
    refine ⟨fun o₁ o₂ => if g o₁ = o₂ then 1 else 0, ?_, ?_, ?_⟩
    · intro o₁ o₂
      change 0 ≤ (if g o₁ = o₂ then (1 : ℝ) else 0)
      split_ifs <;> norm_num
    · intro o₁
      rw [Finset.sum_ite_eq]
      simp
    · intro x o₂
      have hgx : g (q₁ x) = q₂ x := by
        have hex : ∃ y, q₁ y = q₁ x := ⟨x, rfl⟩
        unfold g
        rw [dif_pos hex]
        exact h (Classical.choose_spec hex)
      simp only [RealExperiment.ofObserver]
      have hite : ∀ o₁, (if q₁ x = o₁ then (1 : ℝ) else 0) * (if g o₁ = o₂ then 1 else 0) =
          (if q₁ x = o₁ then (if g o₁ = o₂ then (1 : ℝ) else 0) else 0) := by
        intro o₁
        by_cases hc : q₁ x = o₁ <;> simp [hc]
      simp only [hite]
      rw [Finset.sum_ite_eq, hgx]
      simp

/-- A rational observation model read as a real experiment. -/
def RealExperiment.ofRational {O : Type*} [Fintype O]
    (M : NoisyRecovery.RationalObservationModel X O) : RealExperiment X O where
  kernel x o := (M.kernel x o : ℝ)
  nonneg x o := by exact_mod_cast M.kernel_nonneg x o
  sum_one x := by exact_mod_cast M.kernel_sum_one x

/-- The posterior vulnerability of a gain function `g` under the prior `π`. -/
noncomputable def gainVulnerability {O : Type*} [Fintype O] {A : Type*} [Fintype A] [Nonempty A]
    (E : RealExperiment X O) (π : X → ℝ) (g : A → X → ℝ) : ℝ :=
  decisionValue E fun x a => π x * g a x

omit [DecidableEq X] [DecidableEq O₁] [DecidableEq O₂] in
/-- **Gain-function form.** -/
theorem dominates_iff_gainVulnerability_le (E₁ : RealExperiment X O₁) (E₂ : RealExperiment X O₂) :
    Dominates E₁ E₂ ↔
      ∀ (A : Type w) [Fintype A] [Nonempty A] (π : X → ℝ), (∀ x, 0 ≤ π x) → ∑ x, π x = 1 →
        ∀ g : A → X → ℝ, gainVulnerability E₂ π g ≤ gainVulnerability E₁ π g := by
  constructor
  · intro h A _ _ π _ _ g
    exact h A (fun x a => π x * g a x)
  · intro h A _ _ u
    rcases isEmpty_or_nonempty X with hX | hX
    · haveI : IsEmpty X := hX
      simp [decisionValue]
    · haveI : Nonempty X := hX
      have hn : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      have hpos : ∀ x, 0 ≤ (fun _ : X => (1 : ℝ) / (Fintype.card X : ℝ)) x := fun x => by positivity
      have hsum : ∑ x, (fun _ : X => (1 : ℝ) / (Fintype.card X : ℝ)) x = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
      have hgain := h A (fun _ : X => (1 : ℝ) / (Fintype.card X : ℝ)) hpos hsum
        (fun a x => (Fintype.card X : ℝ) * u x a)
      have h₂ : gainVulnerability E₂ (fun _ : X => (1 : ℝ) / (Fintype.card X : ℝ))
          (fun a x => (Fintype.card X : ℝ) * u x a) = decisionValue E₂ u := by
        unfold gainVulnerability
        congr 1
        funext x a
        field_simp
      have h₁ : gainVulnerability E₁ (fun _ : X => (1 : ℝ) / (Fintype.card X : ℝ))
          (fun a x => (Fintype.card X : ℝ) * u x a) = decisionValue E₁ u := by
        unfold gainVulnerability
        congr 1
        funext x a
        field_simp
      rwa [h₂, h₁] at hgain

/-- **The nonempty output type is required.** -/
theorem nonempty_output_is_required :
    ∃ (E₁ : RealExperiment Empty Unit) (E₂ : RealExperiment Empty Empty),
      Dominates E₁ E₂ ∧ ¬ IsGarbling E₁ E₂ := by
  have hE₁ : RealExperiment Empty Unit :=
    { kernel := fun x _ => Empty.elim x
      nonneg := fun x _ => Empty.elim x
      sum_one := fun x => Empty.elim x }
  have hE₂ : RealExperiment Empty Empty :=
    { kernel := fun x _ => Empty.elim x
      nonneg := fun x _ => Empty.elim x
      sum_one := fun x => Empty.elim x }
  refine ⟨hE₁, hE₂, ?_, ?_⟩
  · intro A _ _ u
    simp [decisionValue]
  · rintro ⟨K, -, hK1, -⟩
    simpa using hK1 ()

/-- The fully noisy binary experiment: every transition has probability one half. -/
noncomputable def noisyBinaryExperiment : RealExperiment (Fin 2) (Fin 2) where
  kernel := fun _ _ => 1 / 2
  nonneg := by intro x o; norm_num
  sum_one := by
    intro x
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num

/-- A fully noisy experiment is a garbling of a perfect one and not conversely. -/
theorem noisy_isGarbling_perfect_not_conversely :
    IsGarbling (RealExperiment.ofObserver (id : Fin 2 → Fin 2)) noisyBinaryExperiment ∧
      ¬ IsGarbling noisyBinaryExperiment (RealExperiment.ofObserver (id : Fin 2 → Fin 2)) := by
  constructor
  · refine ⟨fun _ _ => 1 / 2, (by intro o₁ o₂; norm_num), ?_, ?_⟩
    · intro o₁
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      norm_num
    · intro x o₂
      simp only [noisyBinaryExperiment, RealExperiment.ofObserver]
      have hite : ∀ o₁, (if id x = o₁ then (1 : ℝ) else 0) * (1 / 2) =
          (if id x = o₁ then (1 : ℝ) * (1 / 2) else 0) := by
        intro o₁
        by_cases hc : id x = o₁
        · simp only [hc, if_true]
        · simp only [hc, if_false]
          ring
      simp only [hite]
      rw [Finset.sum_ite_eq]
      simp
  · rintro ⟨K, -, -, hK⟩
    have h0 := hK 0 0
    have h1 := hK 1 0
    simp only [noisyBinaryExperiment, RealExperiment.ofObserver] at h0 h1
    simp at h0 h1
    linarith

/-! ## Zero-one utilities: the deterministic order is the restriction of this one -/

/-- The zero-one utility of a rational prior and a target: the prior mass of a state when the
action names its target value, and zero otherwise. -/
def zeroOneUtility {V : Type*} [DecidableEq V] (prior : X → ℚ) (P : X → V) : X → V → ℝ :=
  fun x v => if P x = v then (prior x : ℝ) else 0

omit [DecidableEq X] in
/-- The decision value of an observer under a zero-one utility is one minus the Bayes risk of
guessing the target from the observer. -/
theorem decisionValue_ofObserver_zeroOne {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (EV : Enumeration V) (prior : X → ℚ) (h0 : ∀ x, 0 ≤ prior x) (h1 : ∑ x, prior x = 1)
    (q : X → O₁) (P : X → V) :
    decisionValue (RealExperiment.ofObserver q) (zeroOneUtility prior P) =
      1 - ((bayesRisk EV (deterministicModel prior h0 h1 q) P : ℚ) : ℝ) := by
  classical
  have hpt : ∀ (o : O₁) (a : V),
      (∑ x, (RealExperiment.ofObserver q).kernel x o * zeroOneUtility prior P x a) =
        ((joint (deterministicModel prior h0 h1 q) P a o : ℚ) : ℝ) := by
    intro o a
    simp only [joint, deterministicModel]
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    simp only [RealExperiment.ofObserver, zeroOneUtility]
    by_cases hq : q x = o <;> by_cases hP : P x = a <;> simp [hq, hP]
  have hsup : ∀ o : O₁,
      (Finset.univ : Finset V).sup' Finset.univ_nonempty
          (fun a => ((joint (deterministicModel prior h0 h1 q) P a o : ℚ) : ℝ)) =
        ((joint (deterministicModel prior h0 h1 q) P
          (bayesTarget EV (deterministicModel prior h0 h1 q) P o) o : ℚ) : ℝ) := by
    intro o
    apply le_antisymm
    · apply Finset.sup'_le
      intro a _
      exact_mod_cast joint_le_bayesTarget EV (deterministicModel prior h0 h1 q) P o a
    · exact Finset.le_sup'
        (fun a => ((joint (deterministicModel prior h0 h1 q) P a o : ℚ) : ℝ)) (Finset.mem_univ _)
  unfold decisionValue
  simp_rw [hpt, hsup]
  rw [bayesRisk_eq_one_sub_sum_max]
  push_cast
  ring

/-- Domination in every zero-one decision problem: every prior and every finite target. -/
def DominatesZeroOne (E₁ : RealExperiment X O₁) (E₂ : RealExperiment X O₂) : Prop :=
  ∀ (V : Type w) [Fintype V] [DecidableEq V] [Nonempty V] (prior : X → ℚ),
    (∀ x, 0 ≤ prior x) → ∑ x, prior x = 1 → ∀ P : X → V,
      decisionValue E₂ (zeroOneUtility prior P) ≤ decisionValue E₁ (zeroOneUtility prior P)

omit [DecidableEq X] [DecidableEq O₁] [DecidableEq O₂] in
/-- Zero-one domination is the restriction of domination to zero-one utilities. -/
theorem dominatesZeroOne_of_dominates {E₁ : RealExperiment X O₁} {E₂ : RealExperiment X O₂}
    (h : Dominates E₁ E₂) : DominatesZeroOne E₁ E₂ := by
  intro V _ _ _ prior _ _ P
  exact h V (zeroOneUtility prior P)

/-- **On observers, zero-one domination is refinement.** -/
theorem dominatesZeroOne_ofObserver_iff_refines [Nonempty O₂] (EO₂ : Enumeration O₂)
    (q₁ : X → O₁) (q₂ : X → O₂) :
    DominatesZeroOne (RealExperiment.ofObserver q₁) (RealExperiment.ofObserver q₂) ↔
      ObserverRefines q₁ q₂ := by
  constructor
  · intro h
    apply refines_of_bayesRisk_le_twoPoint EO₂ q₁ q₂
    intro x y hxy
    have hd := h O₂ (halfHalfPrior x y) (halfHalfPrior_nonneg x y) (halfHalfPrior_sum_one hxy) q₂
    rw [decisionValue_ofObserver_zeroOne EO₂ (halfHalfPrior x y) (halfHalfPrior_nonneg x y)
        (halfHalfPrior_sum_one hxy) q₂ q₂,
      decisionValue_ofObserver_zeroOne EO₂ (halfHalfPrior x y) (halfHalfPrior_nonneg x y)
        (halfHalfPrior_sum_one hxy) q₁ q₂] at hd
    have hcast : ((bayesRisk EO₂ (deterministicModel (halfHalfPrior x y) (halfHalfPrior_nonneg x y)
          (halfHalfPrior_sum_one hxy) q₁) q₂ : ℚ) : ℝ) ≤
        ((bayesRisk EO₂ (deterministicModel (halfHalfPrior x y) (halfHalfPrior_nonneg x y)
          (halfHalfPrior_sum_one hxy) q₂) q₂ : ℚ) : ℝ) := by linarith
    exact_mod_cast hcast
  · intro h
    exact dominatesZeroOne_of_dominates
      (dominates_of_isGarbling ((isGarbling_ofObserver_iff_refines q₁ q₂).2 h))

/-- **The order of deterministic observers is the restriction to zero-one utilities.** On
observers, domination in every zero-one decision problem is domination of the Bayes risk over
every finite target and every rational prior. -/
theorem dominatesZeroOne_ofObserver_iff_bayesRisk_le [Nonempty O₂] (EO₂ : Enumeration O₂)
    (q₁ : X → O₁) (q₂ : X → O₂) :
    DominatesZeroOne (RealExperiment.ofObserver q₁) (RealExperiment.ofObserver q₂) ↔
      ∀ (V : Type w) [Fintype V] [DecidableEq V] (EV : Enumeration V) (P : X → V)
        (prior : X → ℚ) (h0 : ∀ x, 0 ≤ prior x) (h1 : ∑ x, prior x = 1),
        bayesRisk EV (deterministicModel prior h0 h1 q₁) P ≤
          bayesRisk EV (deterministicModel prior h0 h1 q₂) P :=
  (dominatesZeroOne_ofObserver_iff_refines EO₂ q₁ q₂).trans (refines_iff_bayesRisk_le EO₂ q₁ q₂)

/-- **Garbling of observers is the Bayes-risk order.** -/
theorem isGarbling_ofObserver_iff_bayesRisk_le [Nonempty O₂] (EO₂ : Enumeration O₂)
    (q₁ : X → O₁) (q₂ : X → O₂) :
    IsGarbling (RealExperiment.ofObserver q₁) (RealExperiment.ofObserver q₂) ↔
      ∀ (V : Type w) [Fintype V] [DecidableEq V] (EV : Enumeration V) (P : X → V)
        (prior : X → ℚ) (h0 : ∀ x, 0 ≤ prior x) (h1 : ∑ x, prior x = 1),
        bayesRisk EV (deterministicModel prior h0 h1 q₁) P ≤
          bayesRisk EV (deterministicModel prior h0 h1 q₂) P :=
  (isGarbling_ofObserver_iff_refines q₁ q₂).trans (refines_iff_bayesRisk_le EO₂ q₁ q₂)

end OperatorKO7.Meta.OperationalInexpressibility.BlackwellStochastic
