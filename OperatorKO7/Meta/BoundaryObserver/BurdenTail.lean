import OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden
import OperatorKO7.Meta.BoundaryObserver.BurdenGibbs
import OperatorKO7.Meta.BoundaryGeneral.CountableRoleExchange
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# The unbounded hidden-depth law

The exact existing carrierRaw count is used, not a normal runtime assumption.
There is one state per natural depth. Positive penalty and nonzero payload are necessary.
The finite optimizer lives in BurdenGibbs; this file supplies its genuinely countable extension.
-/

set_option autoImplicit false
open scoped BigOperators
open Filter
open OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden

namespace OperatorKO7.Meta.BoundaryObserver.BurdenTail

noncomputable def rawWeight (L : ℕ) (β : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-β * (carrierRaw L k : ℝ))

noncomputable def partition (L : ℕ) (β : ℝ) : ℝ := ∑' k, rawWeight L β k

/-- The terminal summand alone gives a linear lower bound on total structural burden. -/
theorem carrierRaw_ge_last (L k : ℕ) : (k + 1) * L ≤ carrierRaw L k := by
  cases k with
  | zero => simp [carrierRaw]
  | succ k =>
    change (k + 1 + 1) * L ≤ carrierRaw L k + (k + 2) * L
    rw [show k + 1 + 1 = k + 2 by omega]
    omega

theorem rawWeight_pos (L : ℕ) (β : ℝ) (k : ℕ) : 0 < rawWeight L β k := Real.exp_pos _

/-- Quadratic burden is bounded by an actual summable geometric envelope. -/
theorem rawWeight_le_geometric (L : ℕ) (β : ℝ) (hβ : 0 ≤ β) (k : ℕ) :
    rawWeight L β k ≤ Real.exp (-β * L) ^ k := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h : (k : ℝ) * L ≤ (carrierRaw L k : ℝ) := by
    exact_mod_cast (Nat.mul_le_mul_right L (Nat.le_succ k)).trans (carrierRaw_ge_last L k)
  nlinarith [mul_le_mul_of_nonneg_left h hβ]

theorem geometric_ratio_lt_one (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    Real.exp (-β * L) < 1 := by
  rw [Real.exp_lt_one_iff]
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  nlinarith [mul_pos hβ hLR]

theorem rawWeight_summable (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    Summable (rawWeight L β) := by
  exact Summable.of_nonneg_of_le (fun k => (rawWeight_pos L β k).le)
    (rawWeight_le_geometric L β hβ.le)
    (summable_geometric_of_lt_one (Real.exp_pos _).le (geometric_ratio_lt_one L β hL hβ))

theorem partition_pos (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    0 < partition L β :=
  (rawWeight_summable L β hL hβ).tsum_pos (fun k => (rawWeight_pos L β k).le) 0
    (rawWeight_pos L β 0)

noncomputable def probability (L : ℕ) (β : ℝ) (k : ℕ) : ℝ :=
  rawWeight L β k / partition L β

theorem probability_pos (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (k : ℕ) :
    0 < probability L β k := div_pos (rawWeight_pos L β k) (partition_pos L β hL hβ)

/-- Normalization is a convergent sum, not Lean's totalized value of a divergent series. -/
theorem probability_hasSum (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    HasSum (probability L β) 1 := by
  have h := (rawWeight_summable L β hL hβ).hasSum.div_const (partition L β)
  have he : (∑' k, rawWeight L β k) / partition L β = 1 :=
    div_self (partition_pos L β hL hβ).ne'
  rw [he] at h
  exact h

/-- Every natural depth remains possible. -/
theorem probability_infinite_support (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    Function.support (probability L β) = Set.univ := by
  ext k
  simp only [Function.mem_support, Set.mem_univ, iff_true]
  exact (probability_pos L β hL hβ k).ne'

noncomputable def tail (L : ℕ) (β : ℝ) (n : ℕ) : ℝ := ∑' k, probability L β (k + n)

theorem prefix_add_tail (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (n : ℕ) :
    (∑ k ∈ Finset.range n, probability L β k) + tail L β n = 1 := by
  have h := (probability_hasSum L β hL hβ).summable.sum_add_tsum_nat_add n
  simpa only [(probability_hasSum L β hL hβ).tsum_eq] using h

/-- Infinite support has vanishing tail mass, with no maximum possible depth. -/
theorem tail_tendsto_zero (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    Tendsto (tail L β) atTop (nhds 0) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub
    (probability_hasSum L β hL hβ).tendsto_sum_nat
  have he : tail L β = fun n => 1 - ∑ k ∈ Finset.range n, probability L β k := by
    funext n
    linarith [prefix_add_tail L β hL hβ n]
  rw [he]
  simpa only [sub_self] using h

theorem rawWeight_polynomial_moment (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (m : ℕ) :
    Summable (fun k : ℕ => (k : ℝ) ^ m * rawWeight L β k) := by
  have hnorm : ‖Real.exp (-β * L)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact geometric_ratio_lt_one L β hL hβ
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (Nat.cast_nonneg k) m) (rawWeight_pos L β k).le)
    (fun k => mul_le_mul_of_nonneg_left (rawWeight_le_geometric L β hβ.le k) (pow_nonneg (Nat.cast_nonneg k) m))
    (summable_pow_mul_geometric_of_norm_lt_one m hnorm)

theorem probability_polynomial_moment (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (m : ℕ) :
    Summable (fun k : ℕ => (k : ℝ) ^ m * probability L β k) := by
  simpa only [probability, mul_div_assoc] using
    (rawWeight_polynomial_moment L β hL hβ m).div_const (partition L β)

/-- The Gibbs law has finite expected raw carrier burden. -/
theorem probability_burden_summable (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    Summable (fun k => probability L β k * (carrierRaw L k : ℝ)) := by
  have h2 := (probability_polynomial_moment L β hL hβ 2).mul_left ((L : ℝ) / 2)
  have h1 := (probability_polynomial_moment L β hL hβ 1).mul_left (3 * (L : ℝ) / 2)
  have h0 := (probability_hasSum L β hL hβ).summable.mul_left (L : ℝ)
  apply (h2.add h1 |>.add h0).congr
  intro k
  have hc : (2 : ℝ) * (carrierRaw L k : ℝ) = ((k : ℝ) + 1) * (k + 2) * L := by
    exact_mod_cast carrierRaw_two_mul L k
  have he : (carrierRaw L k : ℝ) = (L : ℝ) / 2 * (k : ℝ) ^ 2 + 3 * L / 2 * k + L := by
    nlinarith
  simp only [pow_one]
  rw [he]
  ring

theorem log_probability (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (k : ℕ) :
    Real.log (probability L β k) = -β * (carrierRaw L k : ℝ) - Real.log (partition L β) := by
  rw [probability, rawWeight, Real.log_div (Real.exp_ne_zero _) (partition_pos L β hL hβ).ne',
    Real.log_exp]

theorem probability_entropy_summable (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    Summable (fun k => Real.negMulLog (probability L β k)) := by
  apply ((probability_burden_summable L β hL hβ).mul_left β |>.add
    ((probability_hasSum L β hL hβ).summable.mul_left (Real.log (partition L β)))).congr
  intro k
  rw [Real.negMulLog, log_probability L β hL hβ]
  ring

/-- Zero or negative penalty cannot give a finite partition on all natural depths. -/
theorem nonpositive_penalty_not_summable (L : ℕ) (β : ℝ) (hβ : β ≤ 0) :
    ¬ Summable (rawWeight L β) := by
  intro h
  have hbound : ∀ k, (1 : ℝ) ≤ rawWeight L β k := by
    intro k
    change 1 ≤ Real.exp _
    rw [Real.one_le_exp_iff]
    have hc : (0 : ℝ) ≤ (carrierRaw L k : ℝ) := by positivity
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hβ hc]
  have hconst := Summable.of_nonneg_of_le (fun _k : ℕ => (by norm_num : (0 : ℝ) ≤ 1)) hbound h
  exact (by norm_num : (1 : ℝ) ≠ 0) ((summable_const_iff (1 : ℝ)).mp hconst)

theorem zero_payload_not_summable (β : ℝ) : ¬ Summable (rawWeight 0 β) := by
  have hzero : ∀ k, carrierRaw 0 k = 0 := by
    intro k
    have h := carrierRaw_two_mul 0 k
    omega
  have he : rawWeight 0 β = fun _ : ℕ => (1 : ℝ) := by
    funext k
    simp [rawWeight, hzero]
  rw [he, summable_const_iff]
  norm_num

/-- Exact existence regime of the natural-depth partition. -/
theorem partition_summable_iff (L : ℕ) (β : ℝ) :
    Summable (rawWeight L β) ↔ 0 < L ∧ 0 < β := by
  constructor
  · intro h
    constructor
    · by_contra hn
      have he : L = 0 := by omega
      subst L
      exact zero_payload_not_summable β h
    · by_contra hn
      exact nonpositive_penalty_not_summable L β (le_of_not_gt hn) h
  · rintro ⟨hL, hβ⟩
    exact rawWeight_summable L β hL hβ

/-! ## Countable entropy-cost optimization -/

open OperatorKO7.Meta.BoundaryGeneral.CountableRoleExchange

noncomputable def entropy (p : ℕ → ℝ) : ℝ := ∑' k, Real.negMulLog (p k)

noncomputable def meanBurden (L : ℕ) (p : ℕ → ℝ) : ℝ :=
  ∑' k, p k * (carrierRaw L k : ℝ)

noncomputable def objective (L : ℕ) (β : ℝ) (p : ℕ → ℝ) : ℝ :=
  entropy p - β * meanBurden L p

/-- The relative-entropy summand expands even at a zero competing mass. -/
theorem divergence_term (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β)
    (p : ℕ → ℝ) (k : ℕ) :
    p k * Real.log (p k / probability L β k) =
      -Real.negMulLog (p k) + β * (p k * (carrierRaw L k : ℝ)) +
        Real.log (partition L β) * p k := by
  by_cases hp : p k = 0
  · simp [hp]
  · rw [Real.log_div hp (probability_pos L β hL hβ k).ne', log_probability L β hL hβ,
      Real.negMulLog]
    ring

/-- Finite expected burden already forces finite entropy; it need not be assumed separately. -/
theorem entropy_summable_of_burden (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β)
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp1 : HasSum p 1)
    (hcost : Summable (fun k => p k * (carrierRaw L k : ℝ))) :
    Summable (fun k => Real.negMulLog (p k)) := by
  have hq := probability_hasSum L β hL hβ
  have hu : Summable (fun k => probability L β k + β * (p k * (carrierRaw L k : ℝ)) +
      |Real.log (partition L β)| * p k) :=
    (hq.summable.add (hcost.mul_left β)).add (hp1.summable.mul_left _)
  apply Summable.of_nonneg_of_le _ _ hu
  · intro k
    apply Real.negMulLog_nonneg (hp k)
    have h := hp1.summable.le_tsum k (fun j _ => hp j)
    simpa only [hp1.tsum_eq] using h
  · intro k
    have h := neg_divergence_term_le p (probability L β) hp
      (probability_pos L β hL hβ) k
    rw [divergence_term L β hL hβ] at h
    have hl := mul_le_mul_of_nonneg_right (le_abs_self (Real.log (partition L β))) (hp k)
    linarith [hp k]

/-- Both sides of the countable Gibbs gap are convergent sums. -/
theorem countable_gap_hasSum (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β)
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp1 : HasSum p 1)
    (hcost : Summable (fun k => p k * (carrierRaw L k : ℝ))) :
    HasSum (fun k => p k * Real.log (p k / probability L β k))
      (Real.log (partition L β) - objective L β p) := by
  have hH := entropy_summable_of_burden L β hL hβ p hp hp1 hcost
  have h := (hH.hasSum.neg.add (hcost.hasSum.mul_left β)).add
    (hp1.mul_left (Real.log (partition L β)))
  have he : (fun k => p k * Real.log (p k / probability L β k)) =
      fun k => -Real.negMulLog (p k) + β * (p k * (carrierRaw L k : ℝ)) +
        Real.log (partition L β) * p k := funext (divergence_term L β hL hβ p)
  rw [he]
  convert h using 1
  unfold objective entropy meanBurden
  ring

/-- Equality in the countable Gibbs inequality identifies the whole probability law. -/
theorem countable_divergence_eq_zero_iff (p q : ℕ → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 < q k)
    (hp1 : HasSum p 1) (hq1 : HasSum q 1)
    (hD : Summable (fun k => p k * Real.log (p k / q k))) :
    countableRoleDivergence p q = 0 ↔ p = q := by
  constructor
  · intro hz
    by_contra hne
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
    have hs := (hq1.sub hp1).add hD.hasSum
    have ht : HasSum (fun i => q i - p i + p i * Real.log (p i / q i)) 0 := by
      have hz' : (∑' i, p i * Real.log (p i / q i)) = 0 := hz
      simpa only [sub_self, zero_add, hz'] using hs
    have hpos : 0 < ∑' i, (q i - p i + p i * Real.log (p i / q i)) := by
      exact ht.summable.tsum_pos
        (fun i => by linarith [neg_divergence_term_le p q hp hq i]) k
        (by linarith [BurdenGibbs.neg_divergence_term_lt (hp k) (hq k) hk])
    rw [ht.tsum_eq] at hpos
    exact lt_irrefl _ hpos
  · intro h
    subst q
    exact countableRoleDivergence_self p

/-- The natural-depth Gibbs law attains the partition bound. -/
theorem probability_objective (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    objective L β (probability L β) = Real.log (partition L β) := by
  have h := (countable_gap_hasSum L β hL hβ (probability L β)
    (fun k => (probability_pos L β hL hβ k).le) (probability_hasSum L β hL hβ)
    (probability_burden_summable L β hL hβ)).tsum_eq
  change countableRoleDivergence (probability L β) (probability L β) = _ at h
  rw [countableRoleDivergence_self] at h
  linarith

/-- The unbounded Gibbs law uniquely optimizes entropy minus expected burden among all
nonnegative mass-one natural-depth laws with finite expected burden, including zero masses. -/
theorem countable_unique_maximum (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β)
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp1 : HasSum p 1)
    (hcost : Summable (fun k => p k * (carrierRaw L k : ℝ))) :
    objective L β p ≤ objective L β (probability L β) ∧
      (objective L β p = objective L β (probability L β) ↔ p = probability L β) := by
  have hgap := countable_gap_hasSum L β hL hβ p hp hp1 hcost
  have hq := probability_hasSum L β hL hβ
  have hnon := countableRoleDivergence_nonneg p (probability L β) hp
    (probability_pos L β hL hβ) hp1 hq hgap.summable
  have he := hgap.tsum_eq
  change countableRoleDivergence p (probability L β) = _ at he
  rw [probability_objective L β hL hβ]
  refine ⟨by linarith, ?_⟩
  rw [← countable_divergence_eq_zero_iff p (probability L β) hp
    (probability_pos L β hL hβ) hp1 hq hgap.summable]
  constructor <;> intro h <;> linarith

/-! ## Finite-horizon laws approach the unbounded law -/

noncomputable def prefixPartition (L : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), rawWeight L β k

noncomputable def prefixProbability (L : ℕ) (β : ℝ) (n k : ℕ) : ℝ :=
  if k ≤ n then rawWeight L β k / prefixPartition L β n else 0

theorem prefixPartition_pos (L : ℕ) (β : ℝ) (n : ℕ) : 0 < prefixPartition L β n := by
  apply Finset.sum_pos
  · intro k _
    exact rawWeight_pos L β k
  · exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩

theorem prefixProbability_nonneg (L : ℕ) (β : ℝ) (n k : ℕ) :
    0 ≤ prefixProbability L β n k := by
  unfold prefixProbability
  split_ifs
  · exact (div_pos (rawWeight_pos L β k) (prefixPartition_pos L β n)).le
  · exact le_rfl

theorem prefixProbability_sum (L : ℕ) (β : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), prefixProbability L β n k) = 1 := by
  have he : (∑ k ∈ Finset.range (n + 1), prefixProbability L β n k) =
      (∑ k ∈ Finset.range (n + 1), rawWeight L β k) / prefixPartition L β n := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    exact if_pos (by have h := Finset.mem_range.mp hk; omega)
  rw [he]
  exact div_self (prefixPartition_pos L β n).ne'

theorem prefixProbability_hasSum (L : ℕ) (β : ℝ) (n : ℕ) :
    HasSum (prefixProbability L β n) 1 := by
  rw [← prefixProbability_sum L β n]
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  have hn : ¬ k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  exact if_neg hn

/-- This is exactly the pre-existing finite Gibbs optimizer, extended by zero outside its horizon. -/
theorem prefixProbability_eq_finite (L : ℕ) (β : ℝ) (n : ℕ) (k : Fin (n + 1)) :
    prefixProbability L β n k.val = (BurdenGibbs.burdenLaw n L β).p k := by
  have hk : k.val ≤ n := by omega
  simp only [prefixProbability, if_pos hk, BurdenGibbs.burdenLaw, BurdenGibbs.gibbsLaw,
    rawWeight, prefixPartition, BurdenGibbs.partition]
  congr 1
  exact (Fin.sum_univ_eq_sum_range _ (n + 1)).symm

theorem prefixPartition_tendsto (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    Tendsto (prefixPartition L β) atTop (nhds (partition L β)) := by
  exact (rawWeight_summable L β hL hβ).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)

theorem prefixProbability_tendsto (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (k : ℕ) :
    Tendsto (fun n => prefixProbability L β n k) atTop (nhds (probability L β k)) := by
  have h := (tendsto_const_nhds (x := rawWeight L β k) (f := atTop)).div
    (prefixPartition_tendsto L β hL hβ) (partition_pos L β hL hβ).ne'
  apply h.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (if_pos hn).symm

theorem prefixPartition_le (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (n : ℕ) :
    prefixPartition L β n ≤ partition L β := by
  have h := (rawWeight_summable L β hL hβ).sum_add_tsum_nat_add (n + 1)
  have ht : 0 ≤ ∑' k, rawWeight L β (k + (n + 1)) :=
    tsum_nonneg (fun k => (rawWeight_pos L β _).le)
  change prefixPartition L β n + _ = partition L β at h
  linarith

theorem probability_le_prefix (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β)
    (n k : ℕ) (hk : k ≤ n) : probability L β k ≤ prefixProbability L β n k := by
  rw [prefixProbability, if_pos hk]
  exact div_le_div_of_nonneg_left (rawWeight_pos L β k).le
    (prefixPartition_pos L β n) (prefixPartition_le L β hL hβ n)

/-- The L1 error of the finite Gibbs optimizer is exactly twice the omitted tail probability. -/
theorem prefixProbability_l1 (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (n : ℕ) :
    (∑' k, |prefixProbability L β n k - probability L β k|) = 2 * tail L β (n + 1) := by
  have hsum := ((prefixProbability_hasSum L β n).summable.sub
    (probability_hasSum L β hL hβ).summable).abs
  have hs := hsum.sum_add_tsum_nat_add (n + 1)
  have hp : (∑ k ∈ Finset.range (n + 1), |prefixProbability L β n k - probability L β k|) =
      1 - ∑ k ∈ Finset.range (n + 1), probability L β k := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1), (prefixProbability L β n k - probability L β k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact abs_of_nonneg (sub_nonneg.mpr (probability_le_prefix L β hL hβ n k
          (by have h := Finset.mem_range.mp hk; omega)))
      _ = (∑ k ∈ Finset.range (n + 1), prefixProbability L β n k) -
          ∑ k ∈ Finset.range (n + 1), probability L β k := by rw [Finset.sum_sub_distrib]
      _ = _ := by rw [prefixProbability_sum]
  have ht : (∑' k, |prefixProbability L β n (k + (n + 1)) -
      probability L β (k + (n + 1))|) = tail L β (n + 1) := by
    apply tsum_congr
    intro k
    have hk : ¬ k + (n + 1) ≤ n := by omega
    rw [prefixProbability, if_neg hk, zero_sub, abs_neg,
      abs_of_pos (probability_pos L β hL hβ _)]
  rw [hp, ht] at hs
  linarith [prefix_add_tail L β hL hβ (n + 1)]

/-- The finite optimizers converge in total variation, not only at each fixed depth. -/
theorem prefixProbability_l1_tendsto_zero (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    Tendsto (fun n => ∑' k, |prefixProbability L β n k - probability L β k|)
      atTop (nhds 0) := by
  simp_rw [prefixProbability_l1 L β hL hβ]
  have h := (tail_tendsto_zero L β hL hβ).comp (tendsto_add_atTop_nat 1)
  simpa only [mul_zero] using (tendsto_const_nhds (x := (2 : ℝ)) (f := atTop)).mul h

/-! ## Finite-cutoff guarantees -/

/-- Each new depth multiplies the weight by the exponential of the added carrier burden. -/
theorem rawWeight_succ (L : ℕ) (β : ℝ) (n : ℕ) :
    rawWeight L β (n + 1) = rawWeight L β n * Real.exp (-β * ((n : ℝ) + 2) * L) := by
  unfold rawWeight
  rw [carrierRaw, Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, mul_add,
    Real.exp_add]
  congr 1
  congr 1
  ring

theorem probability_succ (L : ℕ) (β : ℝ) (n : ℕ) :
    probability L β (n + 1) = probability L β n * Real.exp (-β * ((n : ℝ) + 2) * L) := by
  unfold probability
  rw [rawWeight_succ]
  ring

theorem probability_strict_decrease (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (n : ℕ) :
    probability L β (n + 1) < probability L β n := by
  rw [probability_succ]
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hr : Real.exp (-β * ((n : ℝ) + 2) * L) < 1 := by
    rw [Real.exp_lt_one_iff]
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    nlinarith [mul_pos (mul_pos hβ hn) hLR]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hr (probability_pos L β hL hβ n)

/-- The logarithmic second difference is the negative penalty times the payload length. -/
theorem log_probability_curvature (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (n : ℕ) :
    Real.log (probability L β (n + 2)) - 2 * Real.log (probability L β (n + 1)) +
      Real.log (probability L β n) = -β * L := by
  rw [log_probability L β hL hβ, log_probability L β hL hβ,
    log_probability L β hL hβ]
  rw [show n + 2 = (n + 1) + 1 by omega, carrierRaw, carrierRaw]
  push_cast
  ring

/-- After depth n every further increment costs at least (n + 2) times the payload length. -/
theorem carrierRaw_shift_lower (L n j : ℕ) :
    carrierRaw L n + j * (n + 2) * L ≤ carrierRaw L (n + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      carrierRaw L n + (j + 1) * (n + 2) * L =
          (carrierRaw L n + j * (n + 2) * L) + (n + 2) * L := by ring
      _ ≤ carrierRaw L (n + j) + (n + j + 2) * L :=
        Nat.add_le_add ih (Nat.mul_le_mul_right L (by omega))
      _ = carrierRaw L (n + (j + 1)) := rfl

theorem rawWeight_shift_geometric (L : ℕ) (β : ℝ) (hβ : 0 ≤ β) (n j : ℕ) :
    rawWeight L β (n + j) ≤ rawWeight L β n *
      Real.exp (-β * ((n : ℝ) + 2) * L) ^ j := by
  unfold rawWeight
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc : (carrierRaw L n : ℝ) + (j : ℝ) * ((n : ℝ) + 2) * L ≤
      (carrierRaw L (n + j) : ℝ) := by exact_mod_cast carrierRaw_shift_lower L n j
  nlinarith [mul_le_mul_of_nonneg_left hc hβ]

theorem probability_shift_geometric (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (n j : ℕ) :
    probability L β (n + j) ≤ probability L β n *
      Real.exp (-β * ((n : ℝ) + 2) * L) ^ j := by
  unfold probability
  have h := div_le_div_of_nonneg_right (rawWeight_shift_geometric L β hβ.le n j)
    (partition_pos L β hL hβ).le
  convert h using 1
  ring

/-- A cutoff-specific bound on omitted probability; the denominator is strictly positive. -/
theorem tail_le_geometric (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (n : ℕ) :
    tail L β n ≤ probability L β n / (1 - Real.exp (-β * ((n : ℝ) + 2) * L)) := by
  let r := Real.exp (-β * ((n : ℝ) + 2) * L)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    unfold r
    rw [Real.exp_lt_one_iff]
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    nlinarith [mul_pos (mul_pos hβ hn) hLR]
  have hs := (summable_nat_add_iff n).mpr (probability_hasSum L β hL hβ).summable
  have hg := (summable_geometric_of_lt_one hr0 hr1).mul_left (probability L β n)
  calc
    tail L β n ≤ ∑' j, probability L β n * r ^ j := by
      apply Summable.tsum_le_tsum _ hs hg
      intro j
      rw [Nat.add_comm j n]
      exact probability_shift_geometric L β hL hβ n j
    _ = probability L β n / (1 - r) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      rfl

/-- The omitted-mass bound is an explicit L1 error guarantee for the finite Gibbs optimizer. -/
theorem prefixProbability_l1_le (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) (n : ℕ) :
    (∑' k, |prefixProbability L β n k - probability L β k|) ≤
      2 * probability L β (n + 1) / (1 - Real.exp (-β * ((n : ℝ) + 3) * L)) := by
  rw [prefixProbability_l1 L β hL hβ]
  have h := mul_le_mul_of_nonneg_left (tail_le_geometric L β hL hβ (n + 1))
    (by norm_num : (0 : ℝ) ≤ 2)
  convert h using 1
  push_cast
  ring

/-! ## Probability and amplitude at infinite support -/

/-- Probability normalization is a convergent sum. No finite support is required. -/
structure SummableLaw (K : Type*) where
  mass : K → ℝ
  nonneg : ∀ k, 0 ≤ mass k
  total : HasSum mass 1

/-- Nonnegative real amplitudes with a convergent square sum equal to one. -/
def UnitAmplitude (K : Type*) :=
  {a : K → ℝ // (∀ k, 0 ≤ a k) ∧ HasSum (fun k => (a k) ^ 2) 1}

theorem summableLaw_ext {K : Type*} {p q : SummableLaw K} (h : p.mass = q.mass) : p = q := by
  cases p
  cases q
  cases h
  rfl

noncomputable def amplitudeOfLaw {K : Type*} (p : SummableLaw K) : UnitAmplitude K :=
  ⟨fun k => Real.sqrt (p.mass k), fun _ => Real.sqrt_nonneg _, by
    simp only [Real.sq_sqrt (p.nonneg _)]
    exact p.total⟩

noncomputable def lawOfAmplitude {K : Type*} (a : UnitAmplitude K) : SummableLaw K where
  mass k := (a.val k) ^ 2
  nonneg k := sq_nonneg (a.val k)
  total := a.property.2

/-- The inverse maps extend the finite correspondence to arbitrary summable supports.
The positivity condition chooses the nonnegative real representative, not a complex phase. -/
noncomputable def summableLawAmplitudeEquiv (K : Type*) : SummableLaw K ≃ UnitAmplitude K where
  toFun := amplitudeOfLaw
  invFun := lawOfAmplitude
  left_inv p := by
    apply summableLaw_ext
    funext k
    exact Real.sq_sqrt (p.nonneg k)
  right_inv a := by
    apply Subtype.ext
    funext k
    exact Real.sqrt_sq (a.property.1 k)

/-- A bounded nonnegative likelihood has summable evidence weight under any law. -/
theorem bounded_likelihood_summable {K : Type*} (p : SummableLaw K)
    (likelihood : K → ℝ) (M : ℝ) (h0 : ∀ k, 0 ≤ likelihood k)
    (hM : ∀ k, likelihood k ≤ M) : Summable (fun k => likelihood k * p.mass k) := by
  exact Summable.of_nonneg_of_le (fun k => mul_nonneg (h0 k) (p.nonneg k))
    (fun k => mul_le_mul_of_nonneg_right (hM k) (p.nonneg k)) (p.total.summable.mul_left M)

/-- Conditioning uses a positive, convergent evidence sum. It also permits unbounded
likelihoods when their product with the law is summable. -/
noncomputable def conditionalLaw {K : Type*} (p : SummableLaw K) (likelihood : K → ℝ)
    (h0 : ∀ k, 0 ≤ likelihood k) (hs : Summable (fun k => likelihood k * p.mass k))
    (hz : 0 < ∑' k, likelihood k * p.mass k) : SummableLaw K where
  mass k := likelihood k * p.mass k / ∑' j, likelihood j * p.mass j
  nonneg k := div_nonneg (mul_nonneg (h0 k) (p.nonneg k)) hz.le
  total := by
    have h := hs.hasSum.div_const (∑' k, likelihood k * p.mass k)
    simpa only [div_self hz.ne'] using h

/-- Conditioning then taking amplitudes agrees with multiplying by square-root likelihood
and normalizing. This is an equality of the actual infinite-support laws. -/
theorem amplitude_conditioning_commutes {K : Type*} (p : SummableLaw K)
    (likelihood : K → ℝ) (h0 : ∀ k, 0 ≤ likelihood k)
    (hs : Summable (fun k => likelihood k * p.mass k))
    (hz : 0 < ∑' k, likelihood k * p.mass k) (k : K) :
    (amplitudeOfLaw (conditionalLaw p likelihood h0 hs hz)).val k =
      Real.sqrt (likelihood k) * (amplitudeOfLaw p).val k /
        Real.sqrt (∑' j, likelihood j * p.mass j) := by
  change Real.sqrt (likelihood k * p.mass k / ∑' j, likelihood j * p.mass j) = _
  rw [Real.sqrt_div (mul_nonneg (h0 k) (p.nonneg k)), Real.sqrt_mul (h0 k)]
  rfl

theorem amplitude_conditioning_normalized {K : Type*} (p : SummableLaw K)
    (likelihood : K → ℝ) (h0 : ∀ k, 0 ≤ likelihood k)
    (hs : Summable (fun k => likelihood k * p.mass k))
    (hz : 0 < ∑' k, likelihood k * p.mass k) :
    HasSum (fun k => (Real.sqrt (likelihood k) * (amplitudeOfLaw p).val k /
      Real.sqrt (∑' j, likelihood j * p.mass j)) ^ 2) 1 := by
  simp_rw [← amplitude_conditioning_commutes p likelihood h0 hs hz]
  exact (amplitudeOfLaw (conditionalLaw p likelihood h0 hs hz)).property.2

/-- Zero evidence fails the positive-normalization premise. -/
theorem zero_likelihood_no_normalization {K : Type*} (p : SummableLaw K) :
    ¬ 0 < ∑' k, (0 : ℝ) * p.mass k := by simp

/-- The squared change of a nonnegative amplitude is bounded by its probability change. -/
theorem sqrt_difference_sq_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ |p - q| := by
  have hps := Real.sq_sqrt hp
  have hqs := Real.sq_sqrt hq
  rcases le_total p q with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hm := mul_nonneg (Real.sqrt_nonneg p) (sub_nonneg.mpr (Real.sqrt_le_sqrt h))
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hm := mul_nonneg (Real.sqrt_nonneg q) (sub_nonneg.mpr (Real.sqrt_le_sqrt h))
    nlinarith

/-- The square-distance series of two probability amplitudes converges. -/
theorem amplitude_difference_summable {K : Type*} (p q : SummableLaw K) :
    Summable (fun k => ((amplitudeOfLaw p).val k - (amplitudeOfLaw q).val k) ^ 2) := by
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun k => sqrt_difference_sq_le (p.nonneg k) (q.nonneg k))
    (p.total.summable.sub q.total.summable).abs

noncomputable def amplitudeSqDistance {K : Type*} (p q : SummableLaw K) : ℝ :=
  ∑' k, ((amplitudeOfLaw p).val k - (amplitudeOfLaw q).val k) ^ 2

theorem amplitudeSqDistance_nonneg {K : Type*} (p q : SummableLaw K) :
    0 ≤ amplitudeSqDistance p q := tsum_nonneg (fun _ => sq_nonneg _)

/-- Total-variation convergence implies norm convergence of the nonnegative amplitudes. -/
theorem amplitudeSqDistance_le_l1 {K : Type*} (p q : SummableLaw K) :
    amplitudeSqDistance p q ≤ ∑' k, |p.mass k - q.mass k| := by
  exact (amplitude_difference_summable p q).tsum_le_tsum
    (fun k => sqrt_difference_sq_le (p.nonneg k) (q.nonneg k))
    (p.total.summable.sub q.total.summable).abs

noncomputable def burdenSummableLaw (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    SummableLaw ℕ where
  mass := probability L β
  nonneg k := (probability_pos L β hL hβ k).le
  total := probability_hasSum L β hL hβ

noncomputable def prefixSummableLaw (L : ℕ) (β : ℝ) (n : ℕ) : SummableLaw ℕ where
  mass := prefixProbability L β n
  nonneg k := by
    unfold prefixProbability
    split_ifs
    · exact div_nonneg (rawWeight_pos L β k).le (prefixPartition_pos L β n).le
    · exact le_rfl
  total := prefixProbability_hasSum L β n

/-- The omitted probability mass controls the entire infinite amplitude error. -/
theorem prefixAmplitudeSqDistance_le_tail (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β)
    (n : ℕ) :
    amplitudeSqDistance (prefixSummableLaw L β n) (burdenSummableLaw L β hL hβ) ≤
      2 * tail L β (n + 1) := by
  have h := amplitudeSqDistance_le_l1 (prefixSummableLaw L β n) (burdenSummableLaw L β hL hβ)
  exact h.trans_eq (prefixProbability_l1 L β hL hβ n)

/-- The cutoff expression bounds the infinite square-distance as well as probability error. -/
theorem prefixAmplitudeSqDistance_le_cutoff (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β)
    (n : ℕ) :
    amplitudeSqDistance (prefixSummableLaw L β n) (burdenSummableLaw L β hL hβ) ≤
      2 * probability L β (n + 1) / (1 - Real.exp (-β * ((n : ℝ) + 3) * L)) := by
  exact (amplitudeSqDistance_le_l1 (prefixSummableLaw L β n)
    (burdenSummableLaw L β hL hβ)).trans (prefixProbability_l1_le L β hL hβ n)

/-- Finite Gibbs optimizers converge as square-summable amplitude vectors, not only coordinatewise. -/
theorem prefixAmplitudeSqDistance_tendsto_zero (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    Tendsto (fun n => amplitudeSqDistance (prefixSummableLaw L β n)
      (burdenSummableLaw L β hL hβ)) atTop (nhds 0) := by
  apply squeeze_zero (fun n => amplitudeSqDistance_nonneg _ _)
    (fun n => amplitudeSqDistance_le_l1 (prefixSummableLaw L β n) (burdenSummableLaw L β hL hβ))
  exact prefixProbability_l1_tendsto_zero L β hL hβ

/-- The unique countable entropy-cost optimizer transports through the two-sided amplitude
correspondence. Competing amplitudes need only finite expected burden; finite entropy follows. -/
theorem countable_amplitude_unique_maximum (L : ℕ) (β : ℝ) (hL : 0 < L) (hβ : 0 < β)
    (a : UnitAmplitude ℕ)
    (hcost : Summable (fun k => (a.val k) ^ 2 * (carrierRaw L k : ℝ))) :
    objective L β (lawOfAmplitude a).mass ≤ objective L β (probability L β) ∧
      (objective L β (lawOfAmplitude a).mass = objective L β (probability L β) ↔
        a = amplitudeOfLaw (burdenSummableLaw L β hL hβ)) := by
  have h := countable_unique_maximum L β hL hβ (lawOfAmplitude a).mass
    (lawOfAmplitude a).nonneg (lawOfAmplitude a).total hcost
  refine ⟨h.1, h.2.trans ?_⟩
  constructor
  · intro he
    have hlaw : lawOfAmplitude a = burdenSummableLaw L β hL hβ := summableLaw_ext he
    have ha := congrArg amplitudeOfLaw hlaw
    exact ((summableLawAmplitudeEquiv ℕ).apply_symm_apply a).symm.trans ha
  · intro he
    subst a
    exact congrArg SummableLaw.mass
      ((summableLawAmplitudeEquiv ℕ).symm_apply_apply (burdenSummableLaw L β hL hβ))

end OperatorKO7.Meta.BoundaryObserver.BurdenTail
