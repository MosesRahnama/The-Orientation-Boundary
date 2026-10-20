/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Norm

/-!
# Compact-uniform separation from zero and locally uniform inversion

A family `F : ℕ → ℂ → ℂ` is compact-uniformly separated from zero on `U` when, on every compact
subset of `U`, its stages are eventually bounded below in norm by one positive constant. Separation
plus locally uniform convergence on an open set gives locally uniform convergence of the
reciprocals. The family `1/(n+1)` is pointwise nonzero and fails separation.

These declarations carry the Mathlib-only analysis used by the metric diagonal grade
(`Meta/DistinctionBoundary/MetricDiagonalGrade.lean`) and the metric licenses of the licensed
boundary calculus.

Relation: families of complex functions indexed by `ℕ`.
Closure: compact subsets of the stated domain.
External trust: none.
-/

set_option autoImplicit false

open Filter Set Topology

namespace OperatorKO7.Analysis.UniformSeparation

noncomputable section

/-- On every compact subset of `U`, the family is eventually bounded away from zero, uniformly. -/
def CompactUniformSeparation (F : ℕ → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ K : Set ℂ, K ⊆ U → IsCompact K →
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ K, ε ≤ ‖F n z‖

/-- If a stage is at least `δ` from zero and the limit is within `δ/2`, the limit is at least
`δ/2` from zero. -/
theorem norm_limit_ge_half_of_stage
    {a b : ℂ} {δ : ℝ} (_hδ : 0 < δ) (ha : δ ≤ ‖a‖) (hdiff : ‖b - a‖ < δ / 2) :
    δ / 2 ≤ ‖b‖ := by
  have htri : ‖a‖ ≤ ‖b‖ + ‖b - a‖ := by
    have h := norm_add_le b (a - b)
    rwa [add_comm b (a - b), sub_add_cancel, norm_sub_rev] at h
  linarith

/-- Uniform inversion on a compact, given separation and uniform convergence. -/
theorem reciprocal_tendstoUniformlyOn_of_separation
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {K : Set ℂ}
    (hsep : ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ K, ε ≤ ‖F n z‖)
    (hlim : TendstoUniformlyOn F f atTop K) :
    TendstoUniformlyOn (fun n z => (F n z)⁻¹) (fun z => (f z)⁻¹) atTop K := by
  obtain ⟨δ, hδ, N, hN⟩ := hsep
  refine Metric.tendstoUniformlyOn_iff.2 ?_
  intro ε hε
  let η : ℝ := min (δ / 2) (ε * δ * δ / 2)
  have hηpos : 0 < η := by
    have h1 : 0 < δ / 2 := half_pos hδ
    have h2 : 0 < ε * δ * δ / 2 := by positivity
    exact lt_min h1 h2
  have hclose := (Metric.tendstoUniformlyOn_iff.1 hlim) η hηpos
  have hNev : ∀ᶠ n in atTop, N ≤ n := eventually_ge_atTop N
  filter_upwards [hclose, hNev] with n hdist hnN
  intro z hz
  have hFn : δ ≤ ‖F n z‖ := hN n hnN z hz
  have hdiff : ‖f z - F n z‖ < η := by
    simpa [dist_eq_norm] using hdist z hz
  have hdiff' : ‖f z - F n z‖ < δ / 2 :=
    lt_of_lt_of_le hdiff (min_le_left _ _)
  have hfbound : δ / 2 ≤ ‖f z‖ :=
    norm_limit_ge_half_of_stage hδ hFn hdiff'
  have hFn0 : F n z ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hFn
    linarith
  have hf0 : f z ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hfbound
    linarith
  have heq :
      dist ((f z)⁻¹) ((F n z)⁻¹) =
        ‖f z - F n z‖ / (‖F n z‖ * ‖f z‖) := by
    rw [dist_eq_norm, inv_sub_inv hf0 hFn0, norm_div, norm_mul, mul_comm (‖f z‖),
      norm_sub_rev]
  have hden_ge : δ * (δ / 2) ≤ ‖F n z‖ * ‖f z‖ :=
    mul_le_mul hFn hfbound (le_of_lt (half_pos hδ)) (norm_nonneg _)
  have hquot :
      ‖f z - F n z‖ / (‖F n z‖ * ‖f z‖) ≤
        ‖f z - F n z‖ / (δ * (δ / 2)) :=
    div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden_ge
  have hηle : η ≤ ε * δ * δ / 2 := min_le_right _ _
  have : ‖f z - F n z‖ / (δ * (δ / 2)) < ε := by
    have hpos : 0 < δ * (δ / 2) := by positivity
    have : ‖f z - F n z‖ < ε * (δ * (δ / 2)) := by
      have hη' : η ≤ ε * (δ * (δ / 2)) := by
        convert hηle using 1
        ring
      exact lt_of_lt_of_le hdiff hη'
    exact (div_lt_iff₀ hpos).2 this
  rw [heq]
  exact lt_of_le_of_lt hquot this

/-- Separation plus locally uniform convergence implies locally uniform convergence of
reciprocals, on an open set in `ℂ`. -/
theorem reciprocal_tendstoLocallyUniformlyOn
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hsep : CompactUniformSeparation F U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U) :
    TendstoLocallyUniformlyOn (fun n z => (F n z)⁻¹) (fun z => (f z)⁻¹) atTop U := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds ?_
  intro x hx
  obtain ⟨K, hKc, hxint, hKU⟩ := exists_compact_subset hU hx
  have huni : TendstoUniformlyOn F f atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hKc).mp (hlim.mono hKU)
  have hrec := reciprocal_tendstoUniformlyOn_of_separation (hsep K hKU hKc) huni
  refine ⟨interior K, ?_, hrec.mono interior_subset⟩
  rw [hU.nhdsWithin_eq hx]
  exact isOpen_interior.mem_nhds hxint

/-- Guard-expiry family: `F n z = 1/(n+1)`. -/
def guardExpiryFamily (n : ℕ) (_z : ℂ) : ℂ :=
  ((n + 1 : ℕ) : ℂ)⁻¹

theorem guardExpiry_norm (n : ℕ) (z : ℂ) :
    ‖guardExpiryFamily n z‖ = ((n + 1 : ℕ) : ℝ)⁻¹ := by
  simp only [guardExpiryFamily, norm_inv]
  rw [Complex.norm_natCast]

theorem guardExpiry_pointwise_ne_zero (n : ℕ) (z : ℂ) :
    guardExpiryFamily n z ≠ 0 := by
  simp [guardExpiryFamily]
  exact Nat.cast_add_one_ne_zero n

theorem guardExpiry_not_separated :
    ¬ CompactUniformSeparation guardExpiryFamily univ := by
  intro hsep
  obtain ⟨ε, hε, N, hN⟩ := hsep {0} (subset_univ _) isCompact_singleton
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
  let n := max N m
  have hle : ε ≤ ‖guardExpiryFamily n 0‖ := hN n (le_max_left _ _) 0 rfl
  have hnorm : ‖guardExpiryFamily n 0‖ = ((n + 1 : ℕ) : ℝ)⁻¹ :=
    guardExpiry_norm n 0
  have hlt : ((n + 1 : ℕ) : ℝ)⁻¹ < ε := by
    have hn1 : (1 / ε) < ((n + 1 : ℕ) : ℝ) := by
      have : (m : ℝ) < (n : ℝ) + 1 := by
        have : (n : ℝ) ≥ (m : ℝ) := by exact_mod_cast le_max_right N m
        linarith
      have hncast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
      rw [hncast]
      exact lt_trans hm this
    have hpos : 0 < 1 / ε := one_div_pos.mpr hε
    have := inv_strictAnti₀ hpos hn1
    simpa [inv_div] using this
  rw [hnorm] at hle
  exact not_le_of_gt hlt hle

end

end OperatorKO7.Analysis.UniformSeparation
