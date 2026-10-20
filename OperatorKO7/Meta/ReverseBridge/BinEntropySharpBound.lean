import Mathlib
import OperatorKO7.Meta.ReverseBridge.QMLaw_MonogamyEntropicDerived

/-!
# The sharp binary-entropy quadratic bound and the SHARP qubit Maassen-Uffink floor (SP2-120)

Closes the named external fence on SP2-120: "the sharp Maassen-Uffink constant `log 2` needs a
quadratic lower bound on `Real.binEntropy` that Mathlib does not carry". This module PROVES that
bound and lands the sharp constant:

* **`binEntropy_ge_four_mul_log_two`:** for `p ∈ [0,1]`,
 `4·log 2·p·(1-p) ≤ binEntropy p` (in bits: `h(p) ≥ 4p(1-p)`), tight at `p ∈ {0, 1/2, 1}`.
 Fully elementary, three pieces with RATIONAL endpoints plus symmetry; every numeric input is a
 Mathlib `log 2` bound (`Real.log_two_gt_d9`, `Real.log_two_lt_d9`):
 - `(0, 2/9]` (`left_piece`): `-q·log q ≥ pq` (from `log y ≤ y - 1`) plus
 `-log p ≥ (4 log 2 - 1)(1 - p)`, the latter by an antitone-slack argument whose endpoint
 value reduces to `7 ≥ 10·log 2`;
 - `(2/9, 1/4]`: the derivative of the gap is at most `log (7/8) < 0` by pure log monotonicity;
 - `(1/4, 1/2)`: the derivative bound reduces to `log(1+u) - log(1-u) ≤ 4·log 2·u` on
 `[0, 1/2]` (`log_ratio_le`), whose slack has nonnegative derivative because `log 2 ≥ 2/3`;
 - `[1/2, 1]` by the symmetry `binEntropy (1-p) = binEntropy p`.

* **`qubit_entropic_floor_sharp` (SP2-120 upgraded):** for ANY normalized qubit amplitude pair,
 `log 2 ≤ H(Z-readout) + H(X-readout)`: the SHARP Maassen-Uffink constant (`-2 log c` at the
 qubit overlap `c = 1/√2`) for the complementary qubit pair, superseding the `log (16/9)`
 collision floor (`sharp_improves_collision_floor`). Chain: the per-readout quadratic bound plus
 the derived Bloch constraint `x² + z² ≤ 1` give `H(Z) + H(X) ≥ log 2·(2 - z² - x²) ≥ log 2`.

Claim typing (binding):
* PROVEN (the theorems below): real analysis on `Real.binEntropy` and the Bloch algebra.
* The pure-qubit Pauli identification uses exactly the displayed Born probabilities.
 `bloch_entropic_floor_sharp` also proves the sharp bound on the closed Bloch disk,
 covering mixed qubit states; `weighted_bias_entropic_floor` gives the finite weighted law.
 The quantified results concern these readout laws, not arbitrary observables or dimensions.

## Audit slots
- Relation: NA. Closure: `propext, Classical.choice, Quot.sound` per `#print axioms` below.
- Trust: no `sorry`/`admit`/`axiom`/`native_decide`/`bv_decide`/`@[csimp]`/`implemented_by`/
 `unsafe`/`partial`/`opaque`. No assumed-inequality fields.
- Non-vacuity (R5): the quadratic bound is TIGHT at `p = 1/2` (`bound_tight_at_half`), so the
 inequality is exact, not loose; the sharp qubit floor strictly improves the previous collision
 floor (`sharp_improves_collision_floor`); the floor itself is strictly positive (`log_pos`).
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ReverseBridge.BinEntropySharpBound

open Real

/-- The gap function: `F p = binEntropy p - 4 log 2 · p(1-p)`. Nonnegativity of `F` on `[0,1]`
is the sharp quadratic bound. -/
noncomputable def F (p : ℝ) : ℝ := Real.binEntropy p - 4 * Real.log 2 * (p * (1 - p))

theorem log_two_gt_two_thirds : (2 : ℝ) / 3 < Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

theorem log_two_lt_seven_tenths : Real.log 2 < 7 / 10 := by
  have h := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith

/-- The derivative of the gap function away from `0` and `1`. -/
theorem hasDerivAt_F {p : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    HasDerivAt F (Real.log (1 - p) - Real.log p - 4 * Real.log 2 * (1 - 2 * p)) p := by
  have h1 := Real.hasDerivAt_binEntropy hp0 hp1
  have hq : HasDerivAt (fun q : ℝ => q * (1 - q)) (1 - 2 * p) p := by
    have ha := hasDerivAt_id p
    have hb : HasDerivAt (fun q : ℝ => 1 - q) (-1) p := (hasDerivAt_id p).const_sub 1
    have hab := ha.mul hb
    convert hab using 1
    simp only [id_eq]
    ring
  have h2 : HasDerivAt (fun q : ℝ => 4 * Real.log 2 * (q * (1 - q)))
      (4 * Real.log 2 * (1 - 2 * p)) p := hq.const_mul (4 * Real.log 2)
  exact h1.sub h2

/-- The artanh-form bound: `log (1+u) - log (1-u) ≤ 4 log 2 · u` on `[0, 1/2]`. The slack's
derivative is `4 log 2 - 2/(1-u²) ≥ 4 log 2 - 8/3 ≥ 0` since `log 2 ≥ 2/3`. -/
theorem log_ratio_le {u : ℝ} (hu0 : 0 ≤ u) (hu2 : u ≤ 1 / 2) :
    Real.log (1 + u) - Real.log (1 - u) ≤ 4 * Real.log 2 * u := by
  set g : ℝ → ℝ := fun v => 4 * Real.log 2 * v - (Real.log (1 + v) - Real.log (1 - v)) with hg
  have hder : ∀ v ∈ Set.Ioo (0 : ℝ) (1 / 2),
      HasDerivAt g (4 * Real.log 2 - (1 / (1 + v) - -1 / (1 - v))) v := by
    intro v hv
    have h1v : (0 : ℝ) < 1 + v := by linarith [hv.1]
    have h2v : (0 : ℝ) < 1 - v := by linarith [hv.2]
    have ha : HasDerivAt (fun w : ℝ => Real.log (1 + w)) (1 / (1 + v)) v := by
      have := ((hasDerivAt_id v).const_add 1).log (ne_of_gt h1v)
      simpa using this
    have hb : HasDerivAt (fun w : ℝ => Real.log (1 - w)) (-1 / (1 - v)) v := by
      have := ((hasDerivAt_id v).const_sub 1).log (ne_of_gt h2v)
      simpa using this
    have hlin : HasDerivAt (fun w : ℝ => 4 * Real.log 2 * w) (4 * Real.log 2) v := by
      simpa using (hasDerivAt_id v).const_mul (4 * Real.log 2)
    exact hlin.sub (ha.sub hb)
  have hcont : ContinuousOn g (Set.Icc (0 : ℝ) (1 / 2)) := by
    apply ContinuousOn.sub (by fun_prop)
    apply ContinuousOn.sub
    · apply ContinuousOn.log (by fun_prop)
      intro v hv
      nlinarith [hv.1]
    · apply ContinuousOn.log (by fun_prop)
      intro v hv
      nlinarith [hv.2]
  have hmono : MonotoneOn g (Set.Icc (0 : ℝ) (1 / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont
    · intro v hv
      rw [interior_Icc] at hv
      exact (hder v hv).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      rw [(hder v hv).deriv]
      have h1v : (0 : ℝ) < 1 + v := by linarith [hv.1]
      have h2v : (0 : ℝ) < 1 - v := by linarith [hv.2]
      have hsum : 1 / (1 + v) - -1 / (1 - v) = 2 / ((1 + v) * (1 - v)) := by
        field_simp
        ring

      rw [hsum, sub_nonneg, div_le_iff₀ (mul_pos h1v h2v)]
      have hv2 : v * v ≤ 1 / 4 := by nlinarith [hv.1, hv.2]
      have h34 : (3 : ℝ) / 4 ≤ (1 + v) * (1 - v) := by nlinarith
      have hm := mul_nonneg
        (by linarith [log_two_gt_two_thirds] : (0 : ℝ) ≤ Real.log 2 - 2 / 3)
        (by linarith : (0 : ℝ) ≤ (1 + v) * (1 - v) - 3 / 4)
      nlinarith [hm, log_two_gt_two_thirds, h34]
  have hg0 : g 0 = 0 := by simp [hg]
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) := Set.left_mem_Icc.mpr (by norm_num)
  have hmemu : u ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨hu0, hu2⟩
  have := hmono hmem0 hmemu hu0
  rw [hg0] at this
  simp only [hg] at this
  linarith

/-- The gap's derivative is nonpositive on `(2/9, 1/2)`. Middle piece by pure log monotonicity
(the bound collapses to `log (7/8) < 0`); right piece by the artanh bound. -/
theorem derivF_nonpos {p : ℝ} (hp : p ∈ Set.Ioo (2 / 9 : ℝ) (1 / 2)) : deriv F p ≤ 0 := by
  have hp0 : (0 : ℝ) < p := lt_trans (by norm_num) hp.1
  have hp1 : p < 1 := lt_trans hp.2 (by norm_num)
  rw [(hasDerivAt_F (ne_of_gt hp0) (ne_of_lt hp1)).deriv]
  rcases le_or_gt p (1 / 4) with hc | hc
  · have e1 : Real.log (1 - p) ≤ Real.log (7 / 9) :=
      Real.log_le_log (by linarith) (by linarith [hp.1])
    have e2 : Real.log (2 / 9) ≤ Real.log p :=
      Real.log_le_log (by norm_num) (le_of_lt hp.1)
    have hL0 : (0 : ℝ) < Real.log 2 := by linarith [log_two_gt_two_thirds]
    have e3 : 2 * Real.log 2 ≤ 4 * Real.log 2 * (1 - 2 * p) := by nlinarith
    have e4 : Real.log (7 / 9) - Real.log (2 / 9) = Real.log (7 / 2) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]
      norm_num
    have e5 : Real.log (7 / 2) - 2 * Real.log 2 = Real.log (7 / 8) := by
      have h4 : (2 : ℝ) * Real.log 2 = Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      rw [h4, ← Real.log_div (by norm_num) (by norm_num)]
      norm_num
    have e6 : Real.log (7 / 8) < 0 := Real.log_neg (by norm_num) (by norm_num)
    linarith
  · have hu0 : (0 : ℝ) ≤ 1 - 2 * p := by linarith [hp.2]
    have hu2 : 1 - 2 * p ≤ 1 / 2 := by linarith
    have hr := log_ratio_le hu0 hu2
    have hA : Real.log (1 + (1 - 2 * p)) = Real.log 2 + Real.log (1 - p) := by
      rw [show (1 + (1 - 2 * p) : ℝ) = 2 * (1 - p) by ring,
        Real.log_mul (by norm_num) (by linarith)]
    have hB : Real.log (1 - (1 - 2 * p)) = Real.log 2 + Real.log p := by
      rw [show (1 - (1 - 2 * p) : ℝ) = 2 * p by ring,
        Real.log_mul (by norm_num) (by linarith)]
    rw [hA, hB] at hr
    linarith

/-- The left piece: `0 ≤ F p` on `(0, 2/9]`. `-q log q ≥ pq` from `log y ≤ y - 1`, and
`-log p ≥ (4 log 2 - 1)(1-p)` by the antitone slack `φ t = -log t - (4 log 2 - 1)(1 - t)`
(endpoint value nonnegative because `7 ≥ 10 log 2`). -/
theorem left_piece {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 2 / 9) : 0 ≤ F p := by
  have hq0 : (0 : ℝ) < 1 - p := by linarith
  set c : ℝ := 4 * Real.log 2 - 1 with hc
  have hphi : c * (1 - p) ≤ -Real.log p := by
    set φ : ℝ → ℝ := fun t => -Real.log t - c * (1 - t) with hφ
    have hder : ∀ t ∈ Set.Ioo (0 : ℝ) (2 / 9), HasDerivAt φ (-t⁻¹ + c) t := by
      intro t ht
      have h1 := (Real.hasDerivAt_log (ne_of_gt ht.1)).neg
      have h2 : HasDerivAt (fun s : ℝ => c * (1 - s)) (c * -1) t :=
        ((hasDerivAt_id t).const_sub 1).const_mul c
      have h12 := h1.sub h2
      convert h12 using 1
      ring
    have hanti : AntitoneOn φ (Set.Ioc (0 : ℝ) (2 / 9)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioc _ _)
      · apply ContinuousOn.sub
        · apply ContinuousOn.neg
          apply ContinuousOn.mono Real.continuousOn_log
          intro t ht
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact ne_of_gt ht.1
        · fun_prop
      · intro t ht
        rw [interior_Ioc] at ht
        exact (hder t ht).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ioc] at ht
        rw [(hder t ht).deriv]
        have hc95 : c ≤ 9 / 5 := by
          rw [hc]
          linarith [log_two_lt_seven_tenths]
        have hc0 : 0 ≤ c := by
          rw [hc]
          linarith [log_two_gt_two_thirds]
        have hct : c * t ≤ 1 := by
          have := mul_le_mul hc95 (le_of_lt ht.2) (le_of_lt ht.1) (by norm_num)
          linarith
        have hinv : c ≤ t⁻¹ := by
          rw [inv_eq_one_div, le_div_iff₀ ht.1]
          exact hct
        linarith
    have hend : 0 ≤ φ (2 / 9) := by
      have hlog92 : Real.log (2 / 9) = -Real.log (9 / 2) := by
        rw [show (2 / 9 : ℝ) = (9 / 2)⁻¹ by norm_num, Real.log_inv]
      have h4 : Real.log 4 ≤ Real.log (9 / 2) :=
        Real.log_le_log (by norm_num) (by norm_num)
      have h4eq : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      simp only [hφ, hlog92, hc]
      rw [h4eq] at h4
      have := log_two_lt_seven_tenths
      nlinarith
    have hmemp : p ∈ Set.Ioc (0 : ℝ) (2 / 9) := ⟨hp0, hp⟩
    have hmem29 : (2 / 9 : ℝ) ∈ Set.Ioc (0 : ℝ) (2 / 9) := ⟨by norm_num, le_refl _⟩
    have := hanti hmemp hmem29 hp
    have hphi_p : 0 ≤ φ p := le_trans hend this
    simp only [hφ] at hphi_p
    linarith
  have hlogq : Real.log (1 - p) ≤ -p := by
    have := Real.log_le_sub_one_of_pos hq0
    linarith
  have hbe : Real.binEntropy p = Real.negMulLog p + Real.negMulLog (1 - p) :=
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub p
  unfold F
  rw [hbe]
  simp only [Real.negMulLog]
  have t1 : p * (c * (1 - p)) ≤ p * (-Real.log p) :=
    mul_le_mul_of_nonneg_left hphi (le_of_lt hp0)
  have t2 : (1 - p) * Real.log (1 - p) ≤ (1 - p) * (-p) :=
    mul_le_mul_of_nonneg_left hlogq (le_of_lt hq0)
  have hcexp : c + 1 = 4 * Real.log 2 := by
    rw [hc]
    ring
  nlinarith [t1, t2]

/-- `0 ≤ F` on `[0, 1/2]`: edge at `0`, left piece to `2/9`, antitone descent to `F (1/2) = 0`
beyond. -/
theorem F_nonneg_half {q : ℝ} (hq0 : 0 ≤ q) (hq2 : q ≤ 1 / 2) : 0 ≤ F q := by
  rcases eq_or_lt_of_le hq0 with h0 | hq0'
  · rw [← h0]
    unfold F
    norm_num
  rcases le_or_gt q (2 / 9) with hL | hR
  · exact left_piece hq0' hL
  · have hFcont : Continuous F := by
      unfold F
      fun_prop
    have hanti : AntitoneOn F (Set.Icc (2 / 9 : ℝ) (1 / 2)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hFcont.continuousOn
      · intro p hp
        rw [interior_Icc] at hp
        exact (hasDerivAt_F (ne_of_gt (lt_trans (by norm_num) hp.1))
          (ne_of_lt (lt_trans hp.2 (by norm_num)))).differentiableAt.differentiableWithinAt
      · intro p hp
        rw [interior_Icc] at hp
        exact derivF_nonpos hp
    have h12 : F (1 / 2) = 0 := by
      unfold F
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
      ring
    have hmemq : q ∈ Set.Icc (2 / 9 : ℝ) (1 / 2) := ⟨le_of_lt hR, hq2⟩
    have hmem12 : (1 / 2 : ℝ) ∈ Set.Icc (2 / 9 : ℝ) (1 / 2) :=
      ⟨by norm_num, le_refl _⟩
    have := hanti hmemq hmem12 hq2
    rw [h12] at this
    exact this

/-- **The sharp quadratic bound (PROVEN, headline).** For `p ∈ [0,1]`:
`4·log 2·p·(1-p) ≤ binEntropy p`. In bits: `h(p) ≥ 4p(1-p)`, tight at `0`, `1/2`, `1`. This is
the bound whose absence from Mathlib was the named fence on the sharp Maassen-Uffink constant. -/
theorem binEntropy_ge_four_mul_log_two {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    4 * Real.log 2 * (p * (1 - p)) ≤ Real.binEntropy p := by
  have key : 0 ≤ F p := by
    rcases le_or_gt p (1 / 2) with h | h
    · exact F_nonneg_half hp0 h
    · have h1 : 0 ≤ 1 - p := by linarith
      have h2 : 1 - p ≤ 1 / 2 := by linarith
      have hh := F_nonneg_half h1 h2
      unfold F at hh ⊢
      rw [Real.binEntropy_one_sub] at hh
      have hcomm : (1 - p) * (1 - (1 - p)) = p * (1 - p) := by ring
      rw [hcomm] at hh
      exact hh
  unfold F at key
  linarith

/-- **R5 tightness.** The bound is EXACT at `p = 1/2`: both sides equal `log 2`. The inequality
is sharp, not loose. -/
theorem bound_tight_at_half :
    4 * Real.log 2 * ((1 / 2 : ℝ) * (1 - 1 / 2)) = Real.binEntropy (1 / 2) := by
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
  ring

/-- Binary entropy in bias coordinates. The probability is exactly (1+b)/2. -/
theorem binEntropy_bias_lower {b : ℝ} (hb0 : -1 ≤ b) (hb1 : b ≤ 1) :
    Real.log 2 * (1 - b ^ 2) ≤ Real.binEntropy ((1 + b) / 2) := by
  calc
    Real.log 2 * (1 - b ^ 2) =
        4 * Real.log 2 * (((1 + b) / 2) * (1 - (1 + b) / 2)) := by ring
    _ ≤ Real.binEntropy ((1 + b) / 2) :=
      binEntropy_ge_four_mul_log_two (by linarith) (by linarith)

/-- Finite nonnegative weighted readout bound, with no normalization required of the weights. -/
theorem weighted_bias_entropic_floor {ι : Type*} [Fintype ι] (w b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hb : ∀ i, -1 ≤ b i ∧ b i ≤ 1) :
    Real.log 2 * (∑ i, w i * (1 - (b i) ^ 2)) ≤
      ∑ i, w i * Real.binEntropy ((1 + b i) / 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    Real.log 2 * (w i * (1 - (b i) ^ 2)) =
        w i * (Real.log 2 * (1 - (b i) ^ 2)) := by ring
    _ ≤ w i * Real.binEntropy ((1 + b i) / 2) :=
      mul_le_mul_of_nonneg_left (binEntropy_bias_lower (hb i).1 (hb i).2) (hw i)

/-- Sharp complementary-readout bound on the entire closed Bloch disk.
For a qubit density matrix, x,z are the actual Pauli expectation values and the
two displayed arguments are the actual Born probabilities. Pure amplitudes are
not required; the disk condition also covers mixed states. -/
theorem bloch_entropic_floor_sharp (x z : ℝ) (hdisk : x ^ 2 + z ^ 2 ≤ 1) :
    Real.log 2 ≤ Real.binEntropy ((1 + x) / 2) + Real.binEntropy ((1 + z) / 2) := by
  have hx0 : -1 ≤ x := by nlinarith [sq_nonneg z]
  have hx1 : x ≤ 1 := by nlinarith [sq_nonneg z]
  have hz0 : -1 ≤ z := by nlinarith [sq_nonneg x]
  have hz1 : z ≤ 1 := by nlinarith [sq_nonneg x]
  have hX := binEntropy_bias_lower hx0 hx1
  have hZ := binEntropy_bias_lower hz0 hz1
  have hL : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
  have hmul := mul_le_mul_of_nonneg_left hdisk hL
  nlinarith

/-- The disk bound is attained at the Pauli eigenstate with biases (0,1). -/
theorem bloch_entropic_floor_attained :
    Real.binEntropy ((1 + (0 : ℝ)) / 2) +
      Real.binEntropy ((1 + (1 : ℝ)) / 2) = Real.log 2 := by
  have hp : ((1 + (0 : ℝ)) / 2) = 2⁻¹ := by norm_num
  have hz : ((1 + (1 : ℝ)) / 2) = 1 := by norm_num
  rw [hp, hz, Real.binEntropy_two_inv]
  simp

open OperatorKO7.Meta.ReverseBridge.QMLaw_MonogamyEntropicDerived in
/-- **SP2-120 SHARP (PROVEN, the fence closed).** For ANY normalized qubit amplitude pair, the
summed Shannon entropies of the two complementary readouts are at least `log 2`: the SHARP
Maassen-Uffink constant for the qubit `Z`/`X` pair. Every input derived: the Bloch constraint
from normalization, the per-readout quadratic floor from `binEntropy_ge_four_mul_log_two`.

The arguments below are exactly the Pauli Z and X Born probabilities for the normalized
state `(a,b)`. Their mutual-unbiasedness overlap is `c = 1/√2`, so the attained constant
is `-2 log c = log 2`. The closed-disk theorem above also covers mixed qubit states. -/
theorem qubit_entropic_floor_sharp (a b : ℂ) (hn : Complex.normSq a + Complex.normSq b = 1) :
    Real.log 2 ≤ Real.binEntropy (Complex.normSq a)
      + Real.binEntropy (Complex.normSq (a + b) / 2) := by
  set x : ℝ := 2 * (a.re * b.re + a.im * b.im) with hxdef
  set z : ℝ := Complex.normSq a - Complex.normSq b with hzdef
  have hna : (0 : ℝ) ≤ Complex.normSq a := Complex.normSq_nonneg a
  have hnb : (0 : ℝ) ≤ Complex.normSq b := Complex.normSq_nonneg b
  have hcon : x ^ 2 + z ^ 2 ≤ 1 := bloch_constraint a b hn
  have hpZ : Complex.normSq a = (1 + z) / 2 := by
    rw [hzdef]
    linarith
  have hpX : Complex.normSq (a + b) / 2 = (1 + x) / 2 := by
    rw [xReadout_eq a b hn]
  have hZ01 : Complex.normSq a ≤ 1 := by linarith
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg z]
  have hx1a : -1 ≤ x := by nlinarith
  have hx1b : x ≤ 1 := by nlinarith
  have hX0 : (0 : ℝ) ≤ Complex.normSq (a + b) / 2 := by
    have := Complex.normSq_nonneg (a + b)
    linarith
  have hX1 : Complex.normSq (a + b) / 2 ≤ 1 := by
    rw [hpX]
    linarith
  have hZbound := binEntropy_ge_four_mul_log_two hna hZ01
  have hXbound := binEntropy_ge_four_mul_log_two hX0 hX1
  have hqZ : Complex.normSq a * (1 - Complex.normSq a) = (1 - z ^ 2) / 4 := by
    rw [hpZ]
    ring
  have hqX : Complex.normSq (a + b) / 2 * (1 - Complex.normSq (a + b) / 2)
      = (1 - x ^ 2) / 4 := by
    rw [hpX]
    ring
  rw [hqZ] at hZbound
  rw [hqX] at hXbound
  have hL0 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hcon (le_of_lt hL0)
  nlinarith [hZbound, hXbound, hmul]

/-- **R5 supersession.** The sharp floor strictly improves the previous derived collision floor:
`log (16/9) < log 2`. SP2-120's named fence is closed, not merely matched. -/
theorem sharp_improves_collision_floor : Real.log (16 / 9) < Real.log 2 :=
  Real.log_lt_log (by norm_num) (by norm_num)

-- Complete public interface: paired declaration and axiom checks.
#check @F
#print axioms F
#check @log_two_gt_two_thirds
#print axioms log_two_gt_two_thirds
#check @log_two_lt_seven_tenths
#print axioms log_two_lt_seven_tenths
#check @hasDerivAt_F
#print axioms hasDerivAt_F
#check @log_ratio_le
#print axioms log_ratio_le
#check @derivF_nonpos
#print axioms derivF_nonpos
#check @left_piece
#print axioms left_piece
#check @F_nonneg_half
#print axioms F_nonneg_half
#check @binEntropy_ge_four_mul_log_two
#print axioms binEntropy_ge_four_mul_log_two
#check @bound_tight_at_half
#print axioms bound_tight_at_half
#check @binEntropy_bias_lower
#print axioms binEntropy_bias_lower
#check @weighted_bias_entropic_floor
#print axioms weighted_bias_entropic_floor
#check @bloch_entropic_floor_sharp
#print axioms bloch_entropic_floor_sharp
#check @bloch_entropic_floor_attained
#print axioms bloch_entropic_floor_attained
#check @qubit_entropic_floor_sharp
#print axioms qubit_entropic_floor_sharp
#check @sharp_improves_collision_floor
#print axioms sharp_improves_collision_floor

end OperatorKO7.Meta.ReverseBridge.BinEntropySharpBound
