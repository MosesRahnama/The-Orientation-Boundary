import OperatorKO7.Meta.BoundaryObserver.BurdenTail
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The countable Gibbs law for a general cost

Manuscript: Theorem `thm:countable-gibbs-general` of the Observation-Boundary Principle.

For a cost `c : ℕ → ℝ` and a real `β` with summable weights `e^{-β c(k)}` and summable weighted
costs `|c(k)| e^{-β c(k)}`, the law `q_β(k) = e^{-β c(k)} / Z_β` has full support, finite entropy
and finite expected cost, and it is the one law of largest `H(p) - β E_p c` among the laws with
`E_p |c| < ∞`, with the gap `log Z_β - (H(p) - β E_p c) = D(p ‖ q_β)`. Three instances: the burden
cost of `BurdenTail`, the linear cost (the geometric law and its mean) and the cost `log n` on the
positive integers, whose partition function is the Riemann zeta function.
-/

set_option autoImplicit false

open scoped BigOperators
open OperatorKO7.Meta.InformationalIncompleteness.CarrierBurden
open OperatorKO7.Meta.BoundaryGeneral.CountableRoleExchange

namespace OperatorKO7.Meta.BoundaryObserver.CountableGibbsGeneral

/-- The Gibbs weight `e^{-β c(k)}`. -/
noncomputable def weight (c : ℕ → ℝ) (β : ℝ) (k : ℕ) : ℝ := Real.exp (-β * c k)

/-- The partition function `Z_β = ∑ₖ e^{-β c(k)}`. -/
noncomputable def partition (c : ℕ → ℝ) (β : ℝ) : ℝ := ∑' k, weight c β k

/-- The Gibbs law `q_β(k) = e^{-β c(k)} / Z_β`. -/
noncomputable def law (c : ℕ → ℝ) (β : ℝ) (k : ℕ) : ℝ := weight c β k / partition c β

/-- The expected cost `E_p c`. -/
noncomputable def meanCost (c : ℕ → ℝ) (p : ℕ → ℝ) : ℝ := ∑' k, p k * c k

/-- The objective `H(p) - β E_p c`. -/
noncomputable def objective (c : ℕ → ℝ) (β : ℝ) (p : ℕ → ℝ) : ℝ :=
  BurdenTail.entropy p - β * meanCost c p

variable (c : ℕ → ℝ) (β : ℝ)

theorem weight_pos (k : ℕ) : 0 < weight c β k := Real.exp_pos _

theorem partition_pos (hZ : Summable (weight c β)) : 0 < partition c β :=
  hZ.tsum_pos (fun k => (weight_pos c β k).le) 0 (weight_pos c β 0)

theorem law_pos (hZ : Summable (weight c β)) (k : ℕ) : 0 < law c β k :=
  div_pos (weight_pos c β k) (partition_pos c β hZ)

theorem law_hasSum (hZ : Summable (weight c β)) : HasSum (law c β) 1 := by
  have h := hZ.hasSum.div_const (partition c β)
  have he : (∑' k, weight c β k) / partition c β = 1 := div_self (partition_pos c β hZ).ne'
  rw [he] at h
  exact h

theorem log_law (hZ : Summable (weight c β)) (k : ℕ) :
    Real.log (law c β k) = -β * c k - Real.log (partition c β) := by
  rw [law, weight, Real.log_div (Real.exp_ne_zero _) (partition_pos c β hZ).ne', Real.log_exp]

theorem law_cost_abs_summable (hM : Summable (fun k => |c k| * weight c β k)) :
    Summable (fun k => law c β k * |c k|) :=
  (hM.div_const (partition c β)).congr fun k => by rw [law]; ring

theorem law_cost_summable (hZ : Summable (weight c β))
    (hM : Summable (fun k => |c k| * weight c β k)) :
    Summable (fun k => law c β k * c k) :=
  Summable.of_norm_bounded (law_cost_abs_summable c β hM) fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (law_pos c β hZ k)]

/-- The law has finite entropy, through `-q log q = β q c + q log Z`. -/
theorem law_entropy_summable (hZ : Summable (weight c β))
    (hM : Summable (fun k => |c k| * weight c β k)) :
    Summable (fun k => Real.negMulLog (law c β k)) := by
  have h := ((law_cost_summable c β hZ hM).mul_left β).add
    ((law_hasSum c β hZ).summable.mul_left (Real.log (partition c β)))
  refine h.congr fun k => ?_
  rw [Real.negMulLog, log_law c β hZ k]
  ring

/-- The relative-entropy summand expands, also at a zero competing mass. -/
theorem divergence_term (hZ : Summable (weight c β)) (p : ℕ → ℝ) (k : ℕ) :
    p k * Real.log (p k / law c β k) =
      -Real.negMulLog (p k) + β * (p k * c k) + Real.log (partition c β) * p k := by
  by_cases hp : p k = 0
  · simp [hp]
  · rw [Real.log_div hp (law_pos c β hZ k).ne', log_law c β hZ, Real.negMulLog]
    ring

theorem cost_summable (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hpc : Summable (fun k => p k * |c k|)) : Summable (fun k => p k * c k) :=
  Summable.of_norm_bounded hpc fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp k)]

/-- A competing law with `E_p |c| < ∞` has finite entropy. -/
theorem entropy_summable_of_cost (hZ : Summable (weight c β)) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hp1 : HasSum p 1) (hpc : Summable (fun k => p k * |c k|)) :
    Summable (fun k => Real.negMulLog (p k)) := by
  have hq := law_hasSum c β hZ
  have hu : Summable (fun k => law c β k + |β| * (p k * |c k|) +
      |Real.log (partition c β)| * p k) :=
    (hq.summable.add (hpc.mul_left |β|)).add (hp1.summable.mul_left _)
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hu
  · apply Real.negMulLog_nonneg (hp k)
    have h := hp1.summable.le_tsum k (fun j _ => hp j)
    simpa only [hp1.tsum_eq] using h
  · have h := neg_divergence_term_le p (law c β) hp (law_pos c β hZ) k
    rw [divergence_term c β hZ] at h
    have h1 : β * (p k * c k) ≤ |β| * (p k * |c k|) := by
      calc β * (p k * c k) ≤ |β * (p k * c k)| := le_abs_self _
        _ = |β| * (p k * |c k|) := by rw [abs_mul, abs_mul, abs_of_nonneg (hp k)]
    have h2 := mul_le_mul_of_nonneg_right (le_abs_self (Real.log (partition c β))) (hp k)
    linarith [hp k]

/-- The gap identity `log Z_β - (H(p) - β E_p c) = D(p ‖ q_β)` as a convergent sum. -/
theorem gap_hasSum (hZ : Summable (weight c β)) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hp1 : HasSum p 1) (hpc : Summable (fun k => p k * |c k|)) :
    HasSum (fun k => p k * Real.log (p k / law c β k))
      (Real.log (partition c β) - objective c β p) := by
  have hH := entropy_summable_of_cost c β hZ p hp hp1 hpc
  have h := (hH.hasSum.neg.add ((cost_summable c p hp hpc).hasSum.mul_left β)).add
    (hp1.mul_left (Real.log (partition c β)))
  have he : (fun k => p k * Real.log (p k / law c β k)) =
      fun k => -Real.negMulLog (p k) + β * (p k * c k) + Real.log (partition c β) * p k :=
    funext (divergence_term c β hZ p)
  rw [he]
  convert h using 1
  unfold objective BurdenTail.entropy meanCost
  ring

theorem law_objective (hZ : Summable (weight c β))
    (hM : Summable (fun k => |c k| * weight c β k)) :
    objective c β (law c β) = Real.log (partition c β) := by
  have h := (gap_hasSum c β hZ (law c β) (fun k => (law_pos c β hZ k).le) (law_hasSum c β hZ)
    (law_cost_abs_summable c β hM)).tsum_eq
  change countableRoleDivergence (law c β) (law c β) = _ at h
  rw [countableRoleDivergence_self] at h
  linarith

/-- The Gibbs law is a probability law with every natural number in its support, finite entropy
and finite expected cost. -/
theorem law_properties (hZ : Summable (weight c β))
    (hM : Summable (fun k => |c k| * weight c β k)) :
    (∀ k, 0 < law c β k) ∧ HasSum (law c β) 1 ∧
      Summable (fun k => Real.negMulLog (law c β k)) ∧ Summable (fun k => law c β k * c k) ∧
      Summable (fun k => law c β k * |c k|) :=
  ⟨law_pos c β hZ, law_hasSum c β hZ, law_entropy_summable c β hZ hM,
    law_cost_summable c β hZ hM, law_cost_abs_summable c β hM⟩

/-- **Theorem `thm:countable-gibbs-general`.** Every law with `E_p |c| < ∞` has finite entropy,
its divergence from `q_β` converges and equals the gap, the gap is nonnegative, and it vanishes
exactly at `q_β`. -/
theorem gibbs_unique_maximum (hZ : Summable (weight c β))
    (hM : Summable (fun k => |c k| * weight c β k))
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp1 : HasSum p 1)
    (hpc : Summable (fun k => p k * |c k|)) :
    Summable (fun k => Real.negMulLog (p k)) ∧
    HasSum (fun k => p k * Real.log (p k / law c β k))
      (Real.log (partition c β) - objective c β p) ∧
    0 ≤ countableRoleDivergence p (law c β) ∧
    (countableRoleDivergence p (law c β) = 0 ↔ p = law c β) ∧
    objective c β p ≤ objective c β (law c β) ∧
    (objective c β p = objective c β (law c β) ↔ p = law c β) := by
  have hgap := gap_hasSum c β hZ p hp hp1 hpc
  have hq := law_hasSum c β hZ
  have hnon := countableRoleDivergence_nonneg p (law c β) hp (law_pos c β hZ) hp1 hq
    hgap.summable
  have hiff := BurdenTail.countable_divergence_eq_zero_iff p (law c β) hp (law_pos c β hZ) hp1 hq
    hgap.summable
  have he := hgap.tsum_eq
  change countableRoleDivergence p (law c β) = _ at he
  rw [law_objective c β hZ hM]
  refine ⟨entropy_summable_of_cost c β hZ p hp hp1 hpc, hgap, hnon, hiff, by linarith, ?_⟩
  rw [← hiff]
  constructor <;> intro h <;> linarith

/-! ## The burden instance -/

/-- The burden cost `C_L` gives the law and the objective of `BurdenTail`. -/
theorem burden_instance (L : ℕ) (hL : 0 < L) (hβ : 0 < β) :
    law (fun k => (carrierRaw L k : ℝ)) β = BurdenTail.probability L β ∧
    (∀ p, objective (fun k => (carrierRaw L k : ℝ)) β p = BurdenTail.objective L β p) ∧
    Summable (weight (fun k => (carrierRaw L k : ℝ)) β) ∧
    Summable (fun k => |(carrierRaw L k : ℝ)| * weight (fun k => (carrierRaw L k : ℝ)) β k) := by
  refine ⟨rfl, fun p => rfl, BurdenTail.rawWeight_summable L β hL hβ, ?_⟩
  have hZ := BurdenTail.partition_pos L β hL hβ
  refine ((BurdenTail.probability_burden_summable L β hL hβ).mul_left
    (BurdenTail.partition L β)).congr fun k => ?_
  rw [abs_of_nonneg (Nat.cast_nonneg _), BurdenTail.probability]
  change BurdenTail.partition L β * (BurdenTail.rawWeight L β k / BurdenTail.partition L β *
    (carrierRaw L k : ℝ)) = (carrierRaw L k : ℝ) * BurdenTail.rawWeight L β k
  field_simp
  ring

/-! ## The linear cost: the geometric law -/

theorem linear_weight (L : ℝ) (k : ℕ) :
    weight (fun k => L * k) β k = Real.exp (-β * L) ^ k := by
  rw [weight, ← Real.exp_nat_mul]
  ring_nf

theorem linear_ratio (L : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    0 ≤ Real.exp (-β * L) ∧ Real.exp (-β * L) < 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_lt_one_iff.mpr (by nlinarith)⟩

theorem linear_partition (L : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    partition (fun k => L * k) β = (1 - Real.exp (-β * L))⁻¹ := by
  obtain ⟨h0, h1⟩ := linear_ratio β L hL hβ
  rw [partition]
  simp_rw [linear_weight]
  exact tsum_geometric_of_lt_one h0 h1

theorem linear_hypotheses (L : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    Summable (weight (fun k => L * k) β) ∧
      Summable (fun k : ℕ => |L * (k : ℝ)| * weight (fun k : ℕ => L * (k : ℝ)) β k) := by
  obtain ⟨h0, h1⟩ := linear_ratio β L hL hβ
  have hnorm : ‖Real.exp (-β * L)‖ < 1 := by rw [Real.norm_of_nonneg h0]; exact h1
  refine ⟨?_, ?_⟩
  · have := summable_geometric_of_lt_one h0 h1
    exact this.congr fun k => (linear_weight β L k).symm
  · have := ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable).mul_left L
    refine this.congr fun k => ?_
    rw [linear_weight, abs_of_nonneg (by positivity : (0 : ℝ) ≤ L * k)]
    ring

/-- The linear cost `c(k) = L k` gives the geometric law `(1 - e^{-βL}) e^{-βLk}`. -/
theorem linear_law (L : ℝ) (hL : 0 < L) (hβ : 0 < β) (k : ℕ) :
    law (fun k => L * k) β k = (1 - Real.exp (-β * L)) * Real.exp (-β * L) ^ k := by
  rw [law, linear_weight, linear_partition β L hL hβ, div_inv_eq_mul, mul_comm]

/-- The geometric law has mean `(e^{βL} - 1)⁻¹`: the level of a ladder of spacing `L`. -/
theorem linear_mean (L : ℝ) (hL : 0 < L) (hβ : 0 < β) :
    HasSum (fun k => law (fun k => L * k) β k * k) (Real.exp (β * L) - 1)⁻¹ := by
  obtain ⟨h0, h1⟩ := linear_ratio β L hL hβ
  have hnorm : ‖Real.exp (-β * L)‖ < 1 := by rw [Real.norm_of_nonneg h0]; exact h1
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left (1 - Real.exp (-β * L))
  have hx : Real.exp (-β * L) * Real.exp (β * L) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < 1 - Real.exp (-β * L) := by linarith
  have hgt : 0 < Real.exp (β * L) - 1 := by
    have hbl : 0 < β * L := mul_pos hβ hL
    have := Real.add_one_lt_exp hbl.ne'
    linarith
  convert h using 1
  · funext k
    rw [linear_law β L hL hβ]
    ring
  · have hne : (1 - Real.exp (-β * L)) ≠ 0 := hpos.ne'
    rw [pow_two, mul_div_assoc', mul_div_mul_left _ _ hne]
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [div_mul_eq_mul_div, div_eq_one_iff_eq hne]
    linear_combination hx

/-! ## The logarithmic cost on the positive integers: the zeta function -/

/-- The cost `log n` on the positive integer `n = k + 1`. -/
noncomputable def logCost (k : ℕ) : ℝ := Real.log ((k : ℝ) + 1)

theorem logCost_weight (k : ℕ) : weight logCost β k = ((k : ℝ) + 1) ^ (-β) := by
  rw [weight, logCost, Real.rpow_def_of_pos (by positivity)]
  ring_nf

theorem log_le_rpow_div {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) : Real.log x ≤ x ^ ε / ε := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx ε)
  rw [Real.log_rpow hx] at h
  rw [le_div_iff₀ hε]
  have := Real.rpow_pos_of_pos hx ε
  nlinarith

theorem logCost_hypotheses (hβ : 1 < β) :
    Summable (weight logCost β) ∧ Summable (fun k => |logCost k| * weight logCost β k) := by
  have hs : ∀ r : ℝ, r < -1 → Summable (fun k : ℕ => ((k : ℝ) + 1) ^ r) := fun r hr => by
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hr)
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine ⟨(hs (-β) (by linarith)).congr fun k => (logCost_weight β k).symm, ?_⟩
  set ε := (β - 1) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (weight_pos _ _ k).le) (fun k => ?_)
    ((hs (ε - β) (by rw [hε]; linarith)).mul_left (1 / ε))
  have hx : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlog : 0 ≤ logCost k := Real.log_nonneg (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  rw [abs_of_nonneg hlog, logCost_weight, Real.rpow_sub hx]
  have hb := log_le_rpow_div hx hεpos
  have hw : 0 ≤ ((k : ℝ) + 1) ^ (-β) := (Real.rpow_pos_of_pos hx _).le
  have hpow : ((k : ℝ) + 1) ^ (-β) = (((k : ℝ) + 1) ^ β)⁻¹ := Real.rpow_neg hx.le β
  rw [hpow, div_eq_mul_inv]
  have hb' : logCost k * (((k : ℝ) + 1) ^ β)⁻¹ ≤ ((k : ℝ) + 1) ^ ε / ε * (((k : ℝ) + 1) ^ β)⁻¹ :=
    mul_le_mul_of_nonneg_right hb (by rw [← hpow]; exact hw)
  calc logCost k * (((k : ℝ) + 1) ^ β)⁻¹ ≤ ((k : ℝ) + 1) ^ ε / ε * (((k : ℝ) + 1) ^ β)⁻¹ := hb'
    _ = 1 / ε * (((k : ℝ) + 1) ^ ε * (((k : ℝ) + 1) ^ β)⁻¹) := by ring

/-- The partition function of the cost `log n` at `β > 1` is the Riemann zeta function. -/
theorem logCost_partition_zeta (hβ : 1 < β) :
    ((partition logCost β : ℝ) : ℂ) = riemannZeta (β : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hβ), partition, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  have hx : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  rw [logCost_weight, Real.rpow_neg hx, Complex.ofReal_inv, Complex.ofReal_cpow hx, one_div]
  push_cast
  rfl

/-- The law of the cost `log n` is `n^{-β} / ζ(β)` on the positive integer `n = k + 1`. -/
theorem logCost_law (k : ℕ) :
    law logCost β k = ((k : ℝ) + 1) ^ (-β) / partition logCost β := by
  rw [law, logCost_weight]

end OperatorKO7.Meta.BoundaryObserver.CountableGibbsGeneral
