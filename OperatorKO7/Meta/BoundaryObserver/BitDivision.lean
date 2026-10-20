import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
import OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Convex.Jensen

set_option autoImplicit false

/-!
# The bit of a pair under a reading that errs

Sections 4.3 and 5 of the observation-principle manuscript, with clause (7) of Theorem 4.1 and
Proposition 6.1(iii). Entropies are in natural units: one bit is `Real.log 2`, and the binary
entropy `h(p)` of the manuscript, in bits, is `Real.binEntropy p / Real.log 2`.

* Proposition 4.5(ii), (iii): the entropy of the self-test of one point among `n`, and its value
  one bit only for `n = 2`.
* Proposition 5.1: a reading of reliability `1/2 + ε` leaves `binEntropy (1/2 + ε)` with the
  pair and holds `log 2 - binEntropy (1/2 + ε)`, which is `2 ε² + O(ε⁴)`.
* Proposition 5.2: repeating a deterministic observer adds no test; `N` readings hold at most
  `min (log 2) (N (log 2 - binEntropy (1/2 + ε)))`; the tuples in which fewer than half of the
  readings equal the label have total weight at most `exp (-2 N ε²)`.
* Proposition 5.3: the entropy left by an observer under the uniform law, its two extreme
  values, and the uniform law as the one law of largest entropy.

Proof graph: `Audit/ledgers/operational-inexpressibility/TWO-VOIDS-PROOF-GRAPH.md`, node M4.

Relation: none; finite laws with real weights.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.

STATEMENT CHANGE against the plan file `OBSERVATION-PRINCIPLE-LEAN-ROADMAP.md`, all
strengthenings by removal of a hypothesis that the proof does not consume:
* `selfTest_one_bit_iff` holds for every natural number `n`;
* `reading_condEntropy`, `reading_mutualInfo`, `reading_independent_iff` and
  `reading_exact_iff` hold for every real `ε` (the weights are a probability law when
  `0 ≤ ε ≤ 1/2`);
* `majority_error_le` holds for every `N`; for odd `N` the event is "the majority value differs
  from the label".
-/

namespace OperatorKO7.Meta.BoundaryObserver.BitDivision

open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy

/-! ## Entropy of a finite weight function -/

/-- The entropy, in natural units, of a weight function on a finite type. For a type in
`Type` this is `ShannonFinite.H`. -/
noncomputable def entropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ := ∑ a, Real.negMulLog (p a)

/-- On a type in `Type`, `entropy` is the entropy `H` of the observer-paper development. -/
theorem entropy_eq_H {A : Type} [Fintype A] (p : A → ℝ) : entropy p = H p := rfl

/-- The value of `-x log x` at one half. -/
theorem negMulLog_half : Real.negMulLog (1 / 2 : ℝ) = Real.log 2 / 2 := by
  rw [Real.negMulLog, one_div, Real.log_inv]
  ring

/-- The entropy of the uniform law on a nonempty finite type is the logarithm of its size. -/
theorem entropy_uniform (X : Type*) [Fintype X] [Nonempty X] :
    entropy (fun _ : X => (1 : ℝ) / Fintype.card X) = Real.log (Fintype.card X) := by
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  unfold entropy
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.negMulLog, one_div, Real.log_inv]
  field_simp

/-- `-x log x` is subadditive on the nonnegative reals. -/
theorem negMulLog_add_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.negMulLog (u + v) ≤ Real.negMulLog u + Real.negMulLog v := by
  rcases hu.eq_or_lt with hu0 | hu'
  · rw [← hu0, zero_add, Real.negMulLog_zero, zero_add]
  rcases hv.eq_or_lt with hv0 | hv'
  · rw [← hv0, add_zero, Real.negMulLog_zero, add_zero]
  have h1 : Real.log u ≤ Real.log (u + v) := Real.log_le_log hu' (by linarith)
  have h2 : Real.log v ≤ Real.log (u + v) := Real.log_le_log hv' (by linarith)
  have h1' := mul_le_mul_of_nonneg_left h1 hu
  have h2' := mul_le_mul_of_nonneg_left h2 hv
  simp only [Real.negMulLog]
  linarith

/-! ## Proposition 4.5(ii), (iii): the self-test -/

/-- Proposition 4.5(ii): the logarithm of `n` is the entropy of the indicator of one point among
`n` plus the entropy that remains when the indicator is zero. -/
theorem log_eq_binEntropy_add (n : ℕ) (hn : 2 ≤ n) :
    Real.log n = Real.binEntropy (1 / (n : ℝ)) + (((n : ℝ) - 1) / n) * Real.log ((n : ℝ) - 1) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h1 : (1 / (n : ℝ))⁻¹ = n := by rw [one_div, inv_inv]
  have h2 : (1 - 1 / (n : ℝ))⁻¹ = n / (n - 1) := by
    field_simp
  rw [Real.binEntropy, h1, h2, Real.log_div hn0.ne' hn1.ne']
  field_simp
  ring

/-- Proposition 4.5(iii): the indicator of one point among `n` holds one bit if and only if
`n = 2`. -/
theorem selfTest_one_bit_iff (n : ℕ) :
    Real.binEntropy (1 / (n : ℝ)) = Real.log 2 ↔ n = 2 := by
  rw [Real.binEntropy_eq_log_two]
  constructor
  · intro h
    have h2 : (n : ℝ) = 2 := by
      have h' := congrArg (fun x : ℝ => x⁻¹) h
      simpa using h'
    exact_mod_cast h2
  · intro h
    rw [h]
    norm_num

/-! ## Proposition 5.1: one reading -/

/-- The joint weight of a label `b`, uniform on `Bool`, and a reading `y` that equals the label
with chance `1/2 + ε`. -/
noncomputable def readingJoint (ε : ℝ) (b y : Bool) : ℝ :=
  (1 / 2) * (if y = b then 1 / 2 + ε else 1 / 2 - ε)

/-- The weight of a reading that equals the label. -/
theorem readingJoint_same (ε : ℝ) (b : Bool) : readingJoint ε b b = 1 / 2 * (1 / 2 + ε) := by
  unfold readingJoint
  rw [if_pos rfl]

/-- The weight of a reading that differs from the label. -/
theorem readingJoint_diff (ε : ℝ) {b y : Bool} (h : y ≠ b) :
    readingJoint ε b y = 1 / 2 * (1 / 2 - ε) := by
  unfold readingJoint
  rw [if_neg h]

/-- Each value of the reading has weight one half. -/
theorem readingJoint_marginal_reading (ε : ℝ) (y : Bool) : ∑ b, readingJoint ε b y = 1 / 2 := by
  rw [Fintype.sum_bool]
  cases y
  · rw [readingJoint_same, readingJoint_diff ε (b := true) (y := false) (by decide)]
    ring
  · rw [readingJoint_same, readingJoint_diff ε (b := false) (y := true) (by decide)]
    ring

/-- Each value of the label has weight one half. -/
theorem readingJoint_marginal_label (ε : ℝ) (b : Bool) : ∑ y, readingJoint ε b y = 1 / 2 := by
  rw [Fintype.sum_bool]
  cases b
  · rw [readingJoint_same, readingJoint_diff ε (b := false) (y := true) (by decide)]
    ring
  · rw [readingJoint_same, readingJoint_diff ε (b := true) (y := false) (by decide)]
    ring

/-- The entropy of the constant weight one half on `Bool` is one bit. -/
theorem entropy_const_half : entropy (fun _ : Bool => (1 / 2 : ℝ)) = Real.log 2 := by
  unfold entropy
  rw [Fintype.sum_bool, negMulLog_half]
  ring

/-- The joint entropy of the label and one reading. -/
theorem entropy_readingJoint (ε : ℝ) :
    entropy (fun z : Bool × Bool => readingJoint ε z.1 z.2) =
      Real.log 2 + Real.binEntropy (1 / 2 + ε) := by
  have hTT : readingJoint ε true true = 1 / 2 * (1 / 2 + ε) := readingJoint_same ε true
  have hFF : readingJoint ε false false = 1 / 2 * (1 / 2 + ε) := readingJoint_same ε false
  have hTF : readingJoint ε true false = 1 / 2 * (1 / 2 - ε) := readingJoint_diff ε (by decide)
  have hFT : readingJoint ε false true = 1 / 2 * (1 / 2 - ε) := readingJoint_diff ε (by decide)
  have hq : (1 : ℝ) - (1 / 2 + ε) = 1 / 2 - ε := by ring
  unfold entropy
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, hTT, hFF, hTF, hFT, Real.negMulLog_mul]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hq, negMulLog_half]
  ring

/--
Proposition 5.1, the part that stays with the pair.

Proves: for the label and one reading, the joint entropy minus the entropy of the reading is
`binEntropy (1/2 + ε)`.
Does not prove: any statement about readings whose error depends on the label.
Relation: none. Trust: kernel-only.
-/
theorem reading_condEntropy (ε : ℝ) :
    entropy (fun z : Bool × Bool => readingJoint ε z.1 z.2) -
        entropy (fun y : Bool => ∑ b, readingJoint ε b y) = Real.binEntropy (1 / 2 + ε) := by
  have hmarg : (fun y : Bool => ∑ b, readingJoint ε b y) = fun _ => (1 / 2 : ℝ) :=
    funext (readingJoint_marginal_reading ε)
  rw [entropy_readingJoint, hmarg, entropy_const_half]
  ring

/-- Proposition 5.1, the part that the reading holds: the mutual information of the label and
one reading is `log 2 - binEntropy (1/2 + ε)`, so the two parts add to one bit. -/
theorem reading_mutualInfo (ε : ℝ) :
    entropy (fun b : Bool => ∑ y, readingJoint ε b y) +
        entropy (fun y : Bool => ∑ b, readingJoint ε b y) -
        entropy (fun z : Bool × Bool => readingJoint ε z.1 z.2) =
      Real.log 2 - Real.binEntropy (1 / 2 + ε) := by
  have hmargR : (fun y : Bool => ∑ b, readingJoint ε b y) = fun _ => (1 / 2 : ℝ) :=
    funext (readingJoint_marginal_reading ε)
  have hmargL : (fun b : Bool => ∑ y, readingJoint ε b y) = fun _ => (1 / 2 : ℝ) :=
    funext (readingJoint_marginal_label ε)
  rw [entropy_readingJoint, hmargR, hmargL, entropy_const_half]
  ring

/-- Proposition 5.1: the reading is independent of the label if and only if `ε = 0`. -/
theorem reading_independent_iff (ε : ℝ) :
    (∀ b y, readingJoint ε b y =
        (∑ y', readingJoint ε b y') * (∑ b', readingJoint ε b' y)) ↔ ε = 0 := by
  simp only [readingJoint_marginal_label, readingJoint_marginal_reading]
  constructor
  · intro h
    have h' := h true true
    rw [readingJoint_same] at h'
    linarith
  · intro h b y
    rw [h]
    by_cases hyb : y = b
    · rw [hyb, readingJoint_same]
      ring
    · rw [readingJoint_diff 0 hyb]
      ring

/-- Proposition 5.1: the reading equals the label with chance one if and only if
`ε = 1/2`. -/
theorem reading_exact_iff (ε : ℝ) :
    (∀ b y, y ≠ b → readingJoint ε b y = 0) ↔ ε = 1 / 2 := by
  constructor
  · intro h
    have h' := h true false (by decide)
    rw [readingJoint_diff ε (by decide)] at h'
    linarith
  · intro h b y hyb
    rw [readingJoint_diff ε hyb, h]
    ring

/--
Proposition 5.1, the expansion.

Proves: `log 2 - binEntropy (1/2 + ε) - 2 ε²` is `O(ε⁴)` as `ε → 0`; in bits the leading term is
`(2 / ln 2) ε²`.
Does not prove: the value of the constant; the proof gives `60` on `|ε| < 1/4`.
Relation: none. Trust: kernel-only. The remainders of the logarithm come from
`Real.abs_log_sub_add_sum_range_le`.
-/
theorem one_sub_binEntropy_expansion :
    Asymptotics.IsBigO (nhds (0 : ℝ))
      (fun ε : ℝ => Real.log 2 - Real.binEntropy (1 / 2 + ε) - 2 * ε ^ 2)
      (fun ε : ℝ => ε ^ 4) := by
  refine Asymptotics.IsBigO.of_bound 60 ?_
  have hball : Metric.ball (0 : ℝ) (1 / 4) ∈ nhds (0 : ℝ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  filter_upwards [hball] with ε hε
  have hε' : |ε| < 1 / 4 := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hε
    exact hε
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hε'
  have hp : 0 < 1 + 2 * ε := by linarith
  have hq : 0 < 1 - 2 * ε := by linarith
  have hε4 : (0 : ℝ) ≤ ε ^ 4 := by positivity
  -- the identity that removes the constant `log 2`
  have hident : Real.log 2 - Real.binEntropy (1 / 2 + ε) =
      (1 + 2 * ε) / 2 * Real.log (1 + 2 * ε) + (1 - 2 * ε) / 2 * Real.log (1 - 2 * ε) := by
    have e1 : (1 / 2 + ε) = (1 + 2 * ε) / 2 := by ring
    have e2 : 1 - (1 + 2 * ε) / 2 = (1 - 2 * ε) / 2 := by ring
    rw [e1, Real.binEntropy, Real.log_inv, Real.log_inv, e2,
      Real.log_div hp.ne' two_ne_zero, Real.log_div hq.ne' two_ne_zero]
    ring
  -- the two remainders of the logarithm
  have hx : |2 * ε| < 1 / 2 := by
    rw [abs_mul, abs_two]
    linarith
  have hx1 : |2 * ε| < 1 := by linarith
  have hx1' : |-(2 * ε)| < 1 := by rwa [abs_neg]
  have hpow : |2 * ε| ^ 4 = 16 * ε ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
    ring
  have hdiv : |2 * ε| ^ 4 / (1 - |2 * ε|) ≤ 32 * ε ^ 4 := by
    rw [div_le_iff₀ (by linarith), hpow]
    nlinarith [abs_nonneg (2 * ε)]
  have hr1 : |2 * ε + (2 * ε) ^ 2 / 2 + (2 * ε) ^ 3 / 3 + Real.log (1 - 2 * ε)| ≤ 32 * ε ^ 4 := by
    have h := Real.abs_log_sub_add_sum_range_le hx1 3
    have hsum : (∑ i ∈ Finset.range 3, (2 * ε) ^ (i + 1) / ((i : ℝ) + 1)) =
        2 * ε + (2 * ε) ^ 2 / 2 + (2 * ε) ^ 3 / 3 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    rw [hsum] at h
    exact h.trans hdiv
  have hr2 : |-(2 * ε) + (2 * ε) ^ 2 / 2 - (2 * ε) ^ 3 / 3 + Real.log (1 + 2 * ε)| ≤
      32 * ε ^ 4 := by
    have h := Real.abs_log_sub_add_sum_range_le hx1' 3
    have hsum : (∑ i ∈ Finset.range 3, (-(2 * ε)) ^ (i + 1) / ((i : ℝ) + 1)) =
        -(2 * ε) + (2 * ε) ^ 2 / 2 - (2 * ε) ^ 3 / 3 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
      ring
    rw [hsum, sub_neg_eq_add, abs_neg] at h
    exact h.trans hdiv
  obtain ⟨r1lo, r1hi⟩ := abs_le.mp hr1
  obtain ⟨r2lo, r2hi⟩ := abs_le.mp hr2
  have hexpr : Real.log 2 - Real.binEntropy (1 / 2 + ε) - 2 * ε ^ 2 =
      (1 + 2 * ε) / 2 *
          (-(2 * ε) + (2 * ε) ^ 2 / 2 - (2 * ε) ^ 3 / 3 + Real.log (1 + 2 * ε)) +
        (1 - 2 * ε) / 2 *
          (2 * ε + (2 * ε) ^ 2 / 2 + (2 * ε) ^ 3 / 3 + Real.log (1 - 2 * ε)) +
        16 / 3 * ε ^ 4 := by
    rw [hident]
    ring
  have ha0 : 0 ≤ (1 + 2 * ε) / 2 := by linarith
  have ha1 : (1 + 2 * ε) / 2 ≤ 3 / 4 := by linarith
  have hb0 : 0 ≤ (1 - 2 * ε) / 2 := by linarith
  have hb1 : (1 - 2 * ε) / 2 ≤ 3 / 4 := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hε4, hexpr, abs_le]
  constructor
  · nlinarith [mul_nonneg ha0 hε4, mul_nonneg hb0 hε4,
      mul_le_mul_of_nonneg_left r2lo ha0, mul_le_mul_of_nonneg_left r1lo hb0,
      mul_le_mul_of_nonneg_right ha1 hε4, mul_le_mul_of_nonneg_right hb1 hε4]
  · nlinarith [mul_nonneg ha0 hε4, mul_nonneg hb0 hε4,
      mul_le_mul_of_nonneg_left r2hi ha0, mul_le_mul_of_nonneg_left r1hi hb0,
      mul_le_mul_of_nonneg_right ha1 hε4, mul_le_mul_of_nonneg_right hb1 hε4]

/-! ## Proposition 5.2: copies of a reading -/

/-- Proposition 5.2(i): the observer that repeats the record of `q` in `N ≥ 1` entries has the
kernel of `q`. -/
theorem repeat_same_kernel {X Q : Type*} (q : X → Q) (N : ℕ) (hN : 1 ≤ N) (x y : X) :
    ((fun _ : Fin N => q x) = (fun _ : Fin N => q y)) ↔ q x = q y := by
  constructor
  · intro h
    exact congrFun h ⟨0, hN⟩
  · intro h
    rw [h]

/-- The joint weight of a label `b`, uniform on `Bool`, and `N` readings that are independent
given the label and equal it with chance `1/2 + ε` each. -/
noncomputable def readingsJoint (N : ℕ) (ε : ℝ) (b : Bool) (ys : Fin N → Bool) : ℝ :=
  (1 / 2) * ∏ i, (if ys i = b then 1 / 2 + ε else 1 / 2 - ε)

/-- The weights of the tuples under a product of one law on `Bool` add to a power. -/
theorem sum_prod_bool (g : Bool → ℝ) (N : ℕ) :
    ∑ ys : Fin N → Bool, ∏ i, g (ys i) = (g true + g false) ^ N := by
  rw [← Fintype.sum_bool g]
  exact (Fintype.sum_pow g N).symm

/-- The entropy of the product of `N` copies of a law on `Bool` is `N` times its entropy. -/
theorem sum_negMulLog_prod_bool (g : Bool → ℝ) (hg : g true + g false = 1) (N : ℕ) :
    ∑ ys : Fin N → Bool, Real.negMulLog (∏ i, g (ys i)) =
      N * (Real.negMulLog (g true) + Real.negMulLog (g false)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hsplit : ∑ ys : Fin (N + 1) → Bool, Real.negMulLog (∏ i, g (ys i)) =
        ∑ z : Bool × (Fin N → Bool), Real.negMulLog (g z.1 * ∏ i, g (z.2 i)) := by
      refine (Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool)) _ _ fun z => ?_).symm
      show Real.negMulLog (g z.1 * ∏ i, g (z.2 i)) =
        Real.negMulLog (∏ i : Fin (N + 1), g ((Fin.cons z.1 z.2 : Fin (N + 1) → Bool) i))
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    have hP : ∑ y : Fin N → Bool, ∏ i, g (y i) = 1 := by
      rw [sum_prod_bool, hg, one_pow]
    rw [hsplit, Fintype.sum_prod_type]
    have hinner : ∀ x : Bool,
        ∑ y : Fin N → Bool, Real.negMulLog (g x * ∏ i, g (y i)) =
          Real.negMulLog (g x) +
            g x * (N * (Real.negMulLog (g true) + Real.negMulLog (g false))) := by
      intro x
      simp only [Real.negMulLog_mul]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hP, ih, one_mul]
    simp only [hinner]
    rw [Fintype.sum_bool]
    push_cast
    linear_combination
      ((N : ℝ) * (Real.negMulLog (g true) + Real.negMulLog (g false))) * hg

/-- The weights of one reading given the label add to one. -/
theorem readingWeight_sum (ε : ℝ) (b : Bool) :
    (if true = b then 1 / 2 + ε else 1 / 2 - ε) + (if false = b then 1 / 2 + ε else 1 / 2 - ε) =
      (1 : ℝ) := by
  cases b
  · rw [if_neg (by decide), if_pos rfl]
    ring
  · rw [if_pos rfl, if_neg (by decide)]
    ring

/-- The entropy of one reading given the label is the binary entropy of its reliability. -/
theorem readingWeight_entropy (ε : ℝ) (b : Bool) :
    Real.negMulLog (if true = b then 1 / 2 + ε else 1 / 2 - ε) +
        Real.negMulLog (if false = b then 1 / 2 + ε else 1 / 2 - ε) =
      Real.binEntropy (1 / 2 + ε) := by
  have hq : (1 : ℝ) - (1 / 2 + ε) = 1 / 2 - ε := by ring
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hq]
  cases b
  · rw [if_neg (by decide), if_pos rfl]
    ring
  · rw [if_pos rfl, if_neg (by decide)]

/-- Each value of the label has weight one half under `readingsJoint`. -/
theorem readingsJoint_marginal_label (N : ℕ) (ε : ℝ) (b : Bool) :
    ∑ ys, readingsJoint N ε b ys = 1 / 2 := by
  unfold readingsJoint
  rw [← Finset.mul_sum,
    sum_prod_bool (fun y => if y = b then 1 / 2 + ε else 1 / 2 - ε) N, readingWeight_sum,
    one_pow, mul_one]

/-- The joint entropy of the label and `N` readings. -/
theorem entropy_readingsJoint (N : ℕ) (ε : ℝ) :
    entropy (fun z : Bool × (Fin N → Bool) => readingsJoint N ε z.1 z.2) =
      Real.log 2 + N * Real.binEntropy (1 / 2 + ε) := by
  have hinner : ∀ b : Bool,
      ∑ ys : Fin N → Bool, Real.negMulLog (readingsJoint N ε b ys) =
        Real.log 2 / 2 + 1 / 2 * (N * Real.binEntropy (1 / 2 + ε)) := by
    intro b
    unfold readingsJoint
    simp only [Real.negMulLog_mul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      sum_prod_bool (fun y => if y = b then 1 / 2 + ε else 1 / 2 - ε) N,
      sum_negMulLog_prod_bool (fun y => if y = b then 1 / 2 + ε else 1 / 2 - ε)
        (readingWeight_sum ε b) N,
      readingWeight_sum, readingWeight_entropy, negMulLog_half, one_pow, one_mul]
  unfold entropy
  rw [Fintype.sum_prod_type]
  simp only [hinner]
  rw [Fintype.sum_bool]
  ring

/--
Proposition 5.2(ii), information.

Proves: for a label and `N` readings independent given the label, each of reliability
`1/2 + ε` with `0 ≤ ε ≤ 1/2`, the mutual information of the label and the readings is at most
one bit and at most `N` times the information of one reading.
Does not prove: equality in either bound.
Relation: none. Trust: kernel-only. The bound by the size of the alphabet is
`FiniteSupportEntropy.H_le_log_card`.
-/
theorem readings_mutualInfo_le (N : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) :
    entropy (fun b : Bool => ∑ ys, readingsJoint N ε b ys) +
        entropy (fun ys : Fin N → Bool => ∑ b, readingsJoint N ε b ys) -
        entropy (fun z : Bool × (Fin N → Bool) => readingsJoint N ε z.1 z.2) ≤
      min (Real.log 2) (N * (Real.log 2 - Real.binEntropy (1 / 2 + ε))) := by
  have hnn : ∀ (b : Bool) (ys : Fin N → Bool), 0 ≤ readingsJoint N ε b ys := by
    intro b ys
    unfold readingsJoint
    refine mul_nonneg (by norm_num) (Finset.prod_nonneg fun i _ => ?_)
    split_ifs <;> linarith
  have hmargL : (fun b : Bool => ∑ ys, readingsJoint N ε b ys) = fun _ => (1 / 2 : ℝ) :=
    funext (readingsJoint_marginal_label N ε)
  -- the entropy of the readings is at most the joint entropy
  have hsub : entropy (fun ys : Fin N → Bool => ∑ b, readingsJoint N ε b ys) ≤
      entropy (fun z : Bool × (Fin N → Bool) => readingsJoint N ε z.1 z.2) := by
    unfold entropy
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_le_sum fun ys _ => ?_
    show Real.negMulLog (∑ b, readingsJoint N ε b ys) ≤
      ∑ b, Real.negMulLog (readingsJoint N ε b ys)
    rw [Fintype.sum_bool, Fintype.sum_bool]
    exact negMulLog_add_le (hnn true ys) (hnn false ys)
  -- the entropy of the readings is at most the logarithm of the number of tuples
  have hcard : entropy (fun ys : Fin N → Bool => ∑ b, readingsJoint N ε b ys) ≤
      N * Real.log 2 := by
    have hsum : ∑ ys : Fin N → Bool, ∑ b, readingsJoint N ε b ys = 1 := by
      rw [Finset.sum_comm, Fintype.sum_bool, readingsJoint_marginal_label,
        readingsJoint_marginal_label]
      norm_num
    have hle := H_le_log_card (fun ys : Fin N → Bool => ∑ b, readingsJoint N ε b ys)
      (fun ys => Finset.sum_nonneg fun b _ => hnn b ys) hsum
    rw [Fintype.card_pi_const, Fintype.card_bool] at hle
    have hlog : Real.log (((2 ^ N : ℕ) : ℝ)) = N * Real.log 2 := by
      push_cast
      exact Real.log_pow 2 N
    rw [hlog] at hle
    exact hle
  rw [hmargL, entropy_const_half, entropy_readingsJoint] at *
  refine le_min ?_ ?_
  · linarith
  · linarith

/-- For weights `0 ≤ q ≤ p`, a tuple with `k` entries of weight `p` and `k + d` entries of
weight `q` has squared weight at most `(p q)^(2k + d)`. -/
theorem minority_weight_sq_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hqp : q ≤ p) (k d : ℕ) :
    (p ^ k * q ^ (k + d)) ^ 2 ≤ (p * q) ^ (2 * k + d) := by
  have hqd : q ^ d ≤ p ^ d := pow_le_pow_left₀ hq hqp d
  have e1 : (p ^ k * q ^ (k + d)) ^ 2 = (p * q) ^ (2 * k) * (q ^ d * q ^ d) := by ring
  have e2 : (p * q) ^ (2 * k + d) = (p * q) ^ (2 * k) * (p ^ d * q ^ d) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqd (pow_nonneg hq d))
    (pow_nonneg (mul_nonneg hp hq) _)

/--
Proposition 5.2(ii), the majority.

Proves: for `0 ≤ ε ≤ 1/2`, the tuples of `N` readings in which fewer than half of the entries
equal the label `b` have total weight at most `exp (-2 N ε²)` given the label.
Does not prove: a bound for ties, which occur only for even `N`.
Relation: none. Trust: kernel-only. The proof is elementary: each such tuple has squared weight
at most `((1/2 + ε)(1/2 - ε))^N`, there are at most `2^N` tuples, and `1 - x ≤ exp (-x)`.
-/
theorem majority_error_le (N : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) (b : Bool) :
    (∑ ys : Fin N → Bool,
        if 2 * (Finset.univ.filter (fun i => ys i = b)).card < N then
          ∏ i, (if ys i = b then 1 / 2 + ε else 1 / 2 - ε)
        else 0) ≤ Real.exp (-2 * N * ε ^ 2) := by
  have hp0 : (0 : ℝ) ≤ 1 / 2 + ε := by linarith
  have hq0 : (0 : ℝ) ≤ 1 / 2 - ε := by linarith
  have hqp : (1 : ℝ) / 2 - ε ≤ 1 / 2 + ε := by linarith
  have hEpos : 0 < Real.exp (-2 * N * ε ^ 2) := Real.exp_pos _
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hpq : 4 * ((1 / 2 + ε) * (1 / 2 - ε)) = 1 - 4 * ε ^ 2 := by ring
  have hbase0 : 0 ≤ 1 - 4 * ε ^ 2 := by nlinarith
  have hexp : 1 - 4 * ε ^ 2 ≤ Real.exp (-(4 * ε ^ 2)) := by
    have h := Real.add_one_le_exp (-(4 * ε ^ 2))
    linarith
  have hE2 : Real.exp (-2 * N * ε ^ 2) ^ 2 = Real.exp (-(4 * ε ^ 2)) ^ N := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hterm : ∀ ys : Fin N → Bool,
      (if 2 * (Finset.univ.filter (fun i => ys i = b)).card < N then
          ∏ i, (if ys i = b then 1 / 2 + ε else 1 / 2 - ε)
        else 0) ≤ Real.exp (-2 * N * ε ^ 2) / 2 ^ N := by
    intro ys
    split_ifs with hlt
    · have hkm : (Finset.univ.filter (fun i => ys i = b)).card +
          (Finset.univ.filter (fun i => ¬ ys i = b)).card = N := by
        rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ, Fintype.card_fin]
      obtain ⟨d, hd⟩ : ∃ d, (Finset.univ.filter (fun i => ¬ ys i = b)).card =
          (Finset.univ.filter (fun i => ys i = b)).card + d :=
        ⟨(Finset.univ.filter (fun i => ¬ ys i = b)).card -
          (Finset.univ.filter (fun i => ys i = b)).card, by omega⟩
      have hprod : ∏ i, (if ys i = b then 1 / 2 + ε else 1 / 2 - ε) =
          (1 / 2 + ε) ^ (Finset.univ.filter (fun i => ys i = b)).card *
            (1 / 2 - ε) ^ ((Finset.univ.filter (fun i => ys i = b)).card + d) := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hd]
      generalize (Finset.univ.filter (fun i => ys i = b)).card = k at hkm hd hprod hlt
      have hN : N = 2 * k + d := by omega
      have hw2 : ((1 / 2 + ε) ^ k * (1 / 2 - ε) ^ (k + d)) ^ 2 ≤
          ((1 / 2 + ε) * (1 / 2 - ε)) ^ (2 * k + d) := minority_weight_sq_le hp0 hq0 hqp k d
      have h4 : ((2 : ℝ) ^ N) ^ 2 = 4 ^ N := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      have hsq : (2 ^ N * ((1 / 2 + ε) ^ k * (1 / 2 - ε) ^ (k + d))) ^ 2 ≤
          Real.exp (-2 * N * ε ^ 2) ^ 2 := by
        calc (2 ^ N * ((1 / 2 + ε) ^ k * (1 / 2 - ε) ^ (k + d))) ^ 2
            = 4 ^ N * ((1 / 2 + ε) ^ k * (1 / 2 - ε) ^ (k + d)) ^ 2 := by rw [mul_pow, h4]
          _ ≤ 4 ^ N * ((1 / 2 + ε) * (1 / 2 - ε)) ^ (2 * k + d) :=
              mul_le_mul_of_nonneg_left hw2 (by positivity)
          _ = (1 - 4 * ε ^ 2) ^ N := by rw [← hN, ← mul_pow, hpq]
          _ ≤ Real.exp (-(4 * ε ^ 2)) ^ N := pow_le_pow_left₀ hbase0 hexp N
          _ = Real.exp (-2 * N * ε ^ 2) ^ 2 := hE2.symm
      have hle : 2 ^ N * ((1 / 2 + ε) ^ k * (1 / 2 - ε) ^ (k + d)) ≤
          Real.exp (-2 * N * ε ^ 2) := le_of_sq_le_sq hsq hEpos.le
      rw [hprod, le_div_iff₀ h2N]
      linarith
    · exact (div_pos hEpos h2N).le
  calc (∑ ys : Fin N → Bool,
        if 2 * (Finset.univ.filter (fun i => ys i = b)).card < N then
          ∏ i, (if ys i = b then 1 / 2 + ε else 1 / 2 - ε)
        else 0)
      ≤ ∑ _ys : Fin N → Bool, Real.exp (-2 * N * ε ^ 2) / 2 ^ N :=
        Finset.sum_le_sum fun ys _ => hterm ys
    _ = Real.exp (-2 * N * ε ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi_const, Fintype.card_bool,
          nsmul_eq_mul]
        push_cast
        field_simp

/-! ## Proposition 5.3: the null record and the largest entropy -/

/-- The sizes of the classes of an observer of a finite type add to the size of the type. -/
theorem fiber_card_sum {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q] (q : X → Q) :
    ∑ y : Q, ((Finset.univ.filter (fun x => q x = y)).card : ℝ) = Fintype.card X := by
  have h := Finset.card_eq_sum_card_fiberwise (f := q) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ] at h
  exact_mod_cast h.symm

/--
Proposition 5.3(i).

Proves: under the uniform law on a nonempty finite type, the entropy of the state minus the
entropy of the record of `q` is the average over the classes of the logarithm of the class size.
Does not prove: the same for other laws on the states.
Relation: none. Trust: kernel-only.
-/
theorem condEntropy_uniform {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q] [Nonempty X]
    (q : X → Q) :
    entropy (fun _ : X => (1 : ℝ) / Fintype.card X) -
        entropy (fun y : Q =>
          ((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X) =
      ∑ y : Q, (((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X) *
        Real.log ((Finset.univ.filter (fun x => q x = y)).card) := by
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ y : Q,
      Real.negMulLog (((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X) =
        ((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X *
            Real.log (Fintype.card X) -
          ((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X *
            Real.log ((Finset.univ.filter (fun x => q x = y)).card) := by
    intro y
    rcases Nat.eq_zero_or_pos (Finset.univ.filter (fun x => q x = y)).card with hz | hpos
    · rw [hz, Nat.cast_zero, zero_div, Real.negMulLog_zero, zero_mul, zero_mul, sub_zero]
    · have hc : (0 : ℝ) < (Finset.univ.filter (fun x => q x = y)).card := by exact_mod_cast hpos
      rw [Real.negMulLog, Real.log_div hc.ne' hn.ne']
      ring
  rw [entropy_uniform]
  unfold entropy
  simp only [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, fiber_card_sum,
    div_self hn.ne', one_mul]
  ring

/--
Proposition 5.3(ii), the null record; Proposition 6.1(iii).

Proves: under the uniform law, the entropy left by `q` is the logarithm of the size of the type
if and only if `q` is constant.
Does not prove: the same for other laws on the states.
Relation: none. Trust: kernel-only.
-/
theorem condEntropy_uniform_eq_log_card_iff {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    [Nonempty X] (q : X → Q) :
    (∑ y : Q, (((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X) *
        Real.log ((Finset.univ.filter (fun x => q x = y)).card)) = Real.log (Fintype.card X) ↔
      ∀ x x', q x = q x' := by
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  constructor
  · intro h x x'
    have hle : ∀ y ∈ (Finset.univ : Finset Q),
        ((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X *
            Real.log ((Finset.univ.filter (fun x => q x = y)).card) ≤
          ((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X *
            Real.log (Fintype.card X) := by
      intro y _
      rcases Nat.eq_zero_or_pos (Finset.univ.filter (fun x => q x = y)).card with hz | hpos
      · rw [hz, Nat.cast_zero, zero_div, zero_mul, zero_mul]
      · have hc : (0 : ℝ) < (Finset.univ.filter (fun x => q x = y)).card := by
          exact_mod_cast hpos
        have hcn : ((Finset.univ.filter (fun x => q x = y)).card : ℝ) ≤ Fintype.card X := by
          exact_mod_cast Finset.card_le_univ _
        exact mul_le_mul_of_nonneg_left (Real.log_le_log hc hcn) (div_nonneg hc.le hn.le)
    have hsumR : ∑ y : Q, ((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X *
        Real.log (Fintype.card X) = Real.log (Fintype.card X) := by
      rw [← Finset.sum_mul, ← Finset.sum_div, fiber_card_sum, div_self hn.ne', one_mul]
    have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (h.trans hsumR.symm) (q x) (Finset.mem_univ _)
    have hxmem : x ∈ Finset.univ.filter (fun z => q z = q x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hpos : 0 < (Finset.univ.filter (fun z => q z = q x)).card :=
      Finset.card_pos.mpr ⟨x, hxmem⟩
    have hc : (0 : ℝ) < (Finset.univ.filter (fun z => q z = q x)).card := by exact_mod_cast hpos
    have hlog : Real.log ((Finset.univ.filter (fun z => q z = q x)).card) =
        Real.log (Fintype.card X) :=
      mul_left_cancel₀ (div_pos hc hn).ne' heq
    have hcard : ((Finset.univ.filter (fun z => q z = q x)).card : ℝ) = Fintype.card X :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr hc) (Set.mem_Ioi.mpr hn) hlog
    have hcard' : (Finset.univ.filter (fun z => q z = q x)).card = Fintype.card X := by
      exact_mod_cast hcard
    have huniv := Finset.eq_univ_of_card _ hcard'
    have hx' : x' ∈ Finset.univ.filter (fun z => q z = q x) := by
      rw [huniv]
      exact Finset.mem_univ _
    exact ((Finset.mem_filter.mp hx').2).symm
  · intro h
    obtain ⟨x₀⟩ := ‹Nonempty X›
    rw [Finset.sum_eq_single (q x₀)]
    · have hall : Finset.univ.filter (fun x => q x = q x₀) = Finset.univ :=
        Finset.filter_true_of_mem fun x _ => h x x₀
      rw [hall, Finset.card_univ, div_self hn.ne', one_mul]
    · intro y _ hy
      have hnone : Finset.univ.filter (fun x => q x = y) = ∅ :=
        Finset.filter_false_of_mem fun x _ hxy => hy (hxy.symm.trans (h x x₀))
      rw [hnone, Finset.card_empty, Nat.cast_zero, zero_div, zero_mul]
    · intro hne
      exact absurd (Finset.mem_univ _) hne

/-- Proposition 5.3(ii), the injective observer: under the uniform law, the entropy left by `q`
is zero if and only if `q` is injective. -/
theorem condEntropy_uniform_eq_zero_iff {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    [Nonempty X] (q : X → Q) :
    (∑ y : Q, (((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X) *
        Real.log ((Finset.univ.filter (fun x => q x = y)).card)) = 0 ↔
      Function.Injective q := by
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hnonneg : ∀ y ∈ (Finset.univ : Finset Q),
      0 ≤ ((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X *
        Real.log ((Finset.univ.filter (fun x => q x = y)).card) := by
    intro y _
    rcases Nat.eq_zero_or_pos (Finset.univ.filter (fun x => q x = y)).card with hz | hpos
    · rw [hz, Nat.cast_zero, zero_div, zero_mul]
    · have hc : (1 : ℝ) ≤ (Finset.univ.filter (fun x => q x = y)).card := by exact_mod_cast hpos
      exact mul_nonneg (div_nonneg (by linarith) hn.le) (Real.log_nonneg hc)
  rw [Finset.sum_eq_zero_iff_of_nonneg hnonneg]
  constructor
  · intro h x x' hxx'
    by_contra hne
    have hx : x ∈ Finset.univ.filter (fun z => q z = q x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hx' : x' ∈ Finset.univ.filter (fun z => q z = q x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxx'.symm⟩
    have hgt : 1 < (Finset.univ.filter (fun z => q z = q x)).card :=
      Finset.one_lt_card.mpr ⟨x, hx, x', hx', hne⟩
    have hc : (1 : ℝ) < (Finset.univ.filter (fun z => q z = q x)).card := by exact_mod_cast hgt
    have hposterm : 0 < ((Finset.univ.filter (fun z => q z = q x)).card : ℝ) / Fintype.card X *
        Real.log ((Finset.univ.filter (fun z => q z = q x)).card) :=
      mul_pos (div_pos (by linarith) hn) (Real.log_pos hc)
    exact hposterm.ne' (h (q x) (Finset.mem_univ _))
  · intro hinj y _
    have hle : (Finset.univ.filter (fun x => q x = y)).card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb =>
        hinj ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hz | ho
    · rw [hz, Nat.cast_zero, zero_div, zero_mul]
    · rw [ho, Nat.cast_one, Real.log_one, mul_zero]

/-- Proposition 5.3(ii), group form: every permutation keeps every record if and only if the
observer is constant. -/
theorem licenseStabilizer_eq_top_iff {X Q : Type*} (q : X → Q) :
    licenseStabilizer q = ⊤ ↔ ∀ x x', q x = q x' := by
  classical
  constructor
  · intro h x x'
    have hmem : Equiv.swap x x' ∈ licenseStabilizer q := by
      rw [h]
      exact Subgroup.mem_top _
    have hx := hmem x
    rw [Equiv.swap_apply_left] at hx
    exact hx.symm
  · intro h
    exact (Subgroup.eq_top_iff' _).2 fun σ x => h (σ x) x

/-- Proposition 5.3(ii), group form: only the identity keeps every record if and only if the
observer is injective. -/
theorem licenseStabilizer_eq_bot_iff {X Q : Type*} (q : X → Q) :
    licenseStabilizer q = ⊥ ↔ Function.Injective q := by
  classical
  constructor
  · intro h x y hxy
    have hmem : Equiv.swap x y ∈ licenseStabilizer q := by
      simpa only [observerSwap] using (swap_mem_licenseStabilizer_of_eq q hxy)
    rw [h, Subgroup.mem_bot] at hmem
    have hx := congrArg (fun σ : Equiv.Perm X => σ x) hmem
    simp only [Equiv.swap_apply_left, Equiv.Perm.coe_one, id_eq] at hx
    exact hx.symm
  · intro hinj
    refine (Subgroup.eq_bot_iff_forall _).2 fun σ hσ => Equiv.ext fun x => ?_
    exact hinj (hσ x)

/-- Proposition 5.3(iii): a law on a finite type that is invariant under every permutation is
the uniform law. -/
theorem invariant_law_uniform {X : Type*} [Fintype X] (p : X → ℝ) (hsum : ∑ x, p x = 1)
    (hinv : ∀ σ : Equiv.Perm X, ∀ x, p (σ x) = p x) (x : X) :
    p x = 1 / Fintype.card X := by
  classical
  have hconst : ∀ x', p x' = p x := by
    intro x'
    have h := hinv (Equiv.swap x x') x
    rw [Equiv.swap_apply_left] at h
    exact h
  have hn : (0 : ℝ) < Fintype.card X := by
    haveI : Nonempty X := ⟨x⟩
    exact_mod_cast Fintype.card_pos
  have hsum' : (Fintype.card X : ℝ) * p x = 1 := by
    rw [← hsum, Finset.sum_congr rfl fun x' _ => hconst x', Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  field_simp
  linarith

/--
Proposition 5.3(iii), the largest entropy.

Proves: a probability law on a nonempty finite type has entropy equal to the logarithm of the
size of the type if and only if it is the uniform law.
Does not prove: the inequality `entropy p ≤ log card`, which for types in `Type` is
`FiniteSupportEntropy.H_le_log_card`.
Relation: none. Trust: kernel-only. The direction from the entropy to the law is the equality
case of the inequality of Jensen for the strictly concave function `Real.negMulLog`.
-/
theorem entropy_eq_log_card_iff {X : Type*} [Fintype X] [Nonempty X] (p : X → ℝ)
    (hnn : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    entropy p = Real.log (Fintype.card X) ↔ ∀ x, p x = 1 / Fintype.card X := by
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  constructor
  · intro h
    have hw0 : ∀ i ∈ (Finset.univ : Finset X), (0 : ℝ) < 1 / Fintype.card X :=
      fun _ _ => one_div_pos.mpr hn
    have hw1 : ∑ _i ∈ (Finset.univ : Finset X), (1 : ℝ) / Fintype.card X = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    have hmem : ∀ i ∈ (Finset.univ : Finset X), p i ∈ Set.Ici (0 : ℝ) :=
      fun i _ => Set.mem_Ici.mpr (hnn i)
    have havg : ∑ i ∈ (Finset.univ : Finset X), ((1 : ℝ) / Fintype.card X) • p i =
        1 / Fintype.card X := by
      simp only [smul_eq_mul]
      rw [← Finset.mul_sum, hsum, mul_one]
    have hval : ∑ i ∈ (Finset.univ : Finset X),
        ((1 : ℝ) / Fintype.card X) • Real.negMulLog (p i) =
          Real.negMulLog (1 / Fintype.card X) := by
      simp only [smul_eq_mul]
      rw [← Finset.mul_sum]
      have hH : ∑ i, Real.negMulLog (p i) = Real.log (Fintype.card X) := h
      rw [hH, Real.negMulLog, one_div, Real.log_inv]
      ring
    have hall := Real.strictConcaveOn_negMulLog.eq_of_map_sum_eq
      (t := (Finset.univ : Finset X)) (w := fun _ => (1 : ℝ) / Fintype.card X) (p := p)
      hw0 hw1 hmem (by rw [havg, hval])
    intro x
    have hconst : ∀ x', p x' = p x := fun x' => hall (Finset.mem_univ x') (Finset.mem_univ x)
    have hsum' : (Fintype.card X : ℝ) * p x = 1 := by
      rw [← hsum, Finset.sum_congr rfl fun x' _ => hconst x', Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    field_simp
    linarith
  · intro h
    have hp : p = fun _ : X => (1 : ℝ) / Fintype.card X := funext h
    rw [hp, entropy_uniform]

/-- Proposition 5.3(iv): a system with one more place coordinate has largest entropy one bit
above the largest entropy of the system. -/
theorem pair_system_log_card (X : Type*) [Fintype X] [Nonempty X] :
    Real.log (Fintype.card (X × Bool)) = Real.log (Fintype.card X) + Real.log 2 := by
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [Fintype.card_prod, Fintype.card_bool]
  push_cast
  exact Real.log_mul hn.ne' two_ne_zero

/-- Theorem 4.1(7): under the uniform law on a pair, the entropy of the state minus the entropy
of a constant record is one bit, `log 2` in natural units. -/
theorem pair_condEntropy_one_bit :
    entropy (fun _ : Bool => (1 : ℝ) / 2) - entropy (fun _ : Unit => (1 : ℝ)) = Real.log 2 := by
  rw [entropy_const_half]
  unfold entropy
  simp

/-! ## Theorem 4.1(7): actual laws on a fair pair, with arbitrary ambient carriers -/

/-- The actual pushforward mass of a fair two-state label along a map into any
output type. The only possibly positive masses are at the two attained outputs.
No finiteness assumption is placed on the output type. -/
noncomputable def fairPairOutputMass {Z : Type*} (f : Bool → Z) (z : Z) : ℝ := by
  classical
  exact (if f true = z then (1 : ℝ) / 2 else 0) +
    (if f false = z then (1 : ℝ) / 2 else 0)

/-- The literal pushforward sum of the fair source label. The
classical equality decision is scoped inside the definition, rather than
imposed as a hypothesis on arbitrary output type Z. -/
noncomputable def fairPairPushforwardSum {Z : Type*} (f : Bool → Z) (z : Z) : ℝ := by
  classical
  exact ∑ b : Bool, if f b = z then (1 : ℝ) / 2 else 0

/-- The actual pushforward mass is precisely the two-point source-label sum. -/
theorem fairPairOutputMass_pushforward {Z : Type*} (f : Bool → Z) (z : Z) :
    fairPairOutputMass f z = fairPairPushforwardSum f z := by
  classical
  unfold fairPairOutputMass fairPairPushforwardSum
  rw [Fintype.sum_bool]

/-- The finite attained range of a fair label, even in an infinite output type. -/
noncomputable def fairPairAttainedSupport {Z : Type*} (f : Bool → Z) : Finset Z := by
  classical
  exact {f true, f false}

/-- The actual pushforward distribution has total mass one on its attained
support, including the singleton support of a merged record. -/
theorem fairPairOutputMass_total {Z : Type*} (f : Bool → Z) :
    (∑ z ∈ fairPairAttainedSupport f, fairPairOutputMass f z) = 1 := by
  classical
  by_cases h : f true = f false
  · have hm : fairPairOutputMass f (f false) = 1 := by
      simp [fairPairOutputMass, h]
      norm_num
    simpa [fairPairAttainedSupport, h] using hm
  · have hr : f false ≠ f true := Ne.symm h
    have ht : fairPairOutputMass f (f true) = 1 / 2 := by
      simp [fairPairOutputMass, hr]
    have hf : fairPairOutputMass f (f false) = 1 / 2 := by
      simp [fairPairOutputMass, h]
    calc
      (∑ z ∈ fairPairAttainedSupport f, fairPairOutputMass f z) =
          fairPairOutputMass f (f true) + fairPairOutputMass f (f false) := by
            simp [fairPairAttainedSupport, h]
      _ = 1 := by rw [ht, hf]; norm_num

/-- Entropy in nats of the actual pushforward of a fair two-state label.
Its finite sum ranges only over attained outputs, even if Z is infinite. -/
noncomputable def fairPairOutputEntropy {Z : Type*} (f : Bool → Z) : ℝ := by
  classical
  exact ∑ z ∈ fairPairAttainedSupport f, Real.negMulLog (fairPairOutputMass f z)

/-- A merged pair of outputs has one attained law value and entropy zero. -/
theorem fairPairOutputEntropy_constant {Z : Type*} (f : Bool → Z)
    (h : f true = f false) : fairPairOutputEntropy f = 0 := by
  classical
  have hm : fairPairOutputMass f (f false) = 1 := by
    simp [fairPairOutputMass, h]
    norm_num
  calc
    fairPairOutputEntropy f =
        Real.negMulLog (fairPairOutputMass f (f false)) := by
          simp [fairPairOutputEntropy, fairPairAttainedSupport, h]
    _ = 0 := by rw [hm, Real.negMulLog_one]

/-- Two distinct attained outputs under a fair label have entropy log 2 nats. -/
theorem fairPairOutputEntropy_distinct {Z : Type*} (f : Bool → Z)
    (h : f true ≠ f false) : fairPairOutputEntropy f = Real.log 2 := by
  classical
  have hr : f false ≠ f true := Ne.symm h
  have ht : fairPairOutputMass f (f true) = 1 / 2 := by
    simp [fairPairOutputMass, hr]
  have hf : fairPairOutputMass f (f false) = 1 / 2 := by
    simp [fairPairOutputMass, h]
  calc
    fairPairOutputEntropy f =
        Real.negMulLog (fairPairOutputMass f (f true)) +
        Real.negMulLog (fairPairOutputMass f (f false)) := by
          simp [fairPairOutputEntropy, fairPairAttainedSupport, h]
    _ = Real.log 2 := by rw [ht, hf, negMulLog_half]; ring

/-- The actual state selected by the fair binary label. -/
def fairPairState {X : Type*} (x₀ x₁ : X) (b : Bool) : X :=
  if b then x₀ else x₁

/-- The actual joint pushforward of (state, deterministic record) has
the entropy of the actual state law, for equal or distinct chosen points.
This identity needs no finiteness of the ambient state or record type. -/
theorem fairPairJointEntropy_eq_state {X Q : Type*} (x₀ x₁ : X) (q : X → Q) :
    fairPairOutputEntropy
        (fun b : Bool => (fairPairState x₀ x₁ b, q (fairPairState x₀ x₁ b))) =
      fairPairOutputEntropy (fairPairState x₀ x₁) := by
  by_cases h : x₀ = x₁
  · subst x₁
    have hj :
        fairPairOutputEntropy
          (fun b : Bool => (fairPairState x₀ x₀ b, q (fairPairState x₀ x₀ b))) = 0 :=
      fairPairOutputEntropy_constant _ (by simp [fairPairState])
    have hs : fairPairOutputEntropy (fairPairState x₀ x₀) = 0 :=
      fairPairOutputEntropy_constant _ (by simp [fairPairState])
    exact hj.trans hs.symm
  · have hs : fairPairState x₀ x₁ true ≠ fairPairState x₀ x₁ false := by
      simpa [fairPairState] using h
    have hj :
        (fairPairState x₀ x₁ true, q (fairPairState x₀ x₁ true)) ≠
          (fairPairState x₀ x₁ false, q (fairPairState x₀ x₁ false)) := by
      intro he
      exact hs (congrArg Prod.fst he)
    exact (fairPairOutputEntropy_distinct _ hj).trans
      (fairPairOutputEntropy_distinct _ hs).symm

/-- Shannon conditional entropy in natural units for the actual fair pair.
The first term is the entropy of the joint pushforward (state, record);
the second is the entropy of the actual record marginal. A deterministic
record makes the joint entropy equal to state entropy by the theorem above.
Both alphabets are replaced by their at-most-two-point attained supports. -/
noncomputable def fairPairConditionalEntropy {X Q : Type*}
    (x₀ x₁ : X) (q : X → Q) : ℝ :=
  fairPairOutputEntropy
      (fun b : Bool => (fairPairState x₀ x₁ b, q (fairPairState x₀ x₁ b))) -
    fairPairOutputEntropy (fun b : Bool => q (fairPairState x₀ x₁ b))

/-- For every genuinely merged pair, the actual fair state has one bit of
conditional entropy after observing q, without finite X or Q. -/
theorem fairMergedPair_condEntropy_log_two {X Q : Type*} (q : X → Q)
    {x₀ x₁ : X} (h : MergedPair.IsMergedPair q x₀ x₁) :
    fairPairConditionalEntropy x₀ x₁ q = Real.log 2 := by
  have hstate : fairPairOutputEntropy (fairPairState x₀ x₁) = Real.log 2 :=
    fairPairOutputEntropy_distinct _ (by simpa [fairPairState] using h.1)
  have hrecord :
      fairPairOutputEntropy (fun b : Bool => q (fairPairState x₀ x₁ b)) = 0 :=
    fairPairOutputEntropy_constant _ (by simpa [fairPairState] using h.2)
  simp [fairPairConditionalEntropy, fairPairJointEntropy_eq_state, hstate, hrecord]

/-- Any side map that separates the two states makes the actual joint
record (q,s) injective on the pair and its conditional entropy zero.
No finiteness assumption on X, Q or the side-symbol type S. -/
theorem fairPair_condEntropy_side_zero {X Q S : Type*} (q : X → Q)
    (s : X → S) {x₀ x₁ : X} (hne : x₀ ≠ x₁) (hs : s x₀ ≠ s x₁) :
    fairPairConditionalEntropy x₀ x₁ (fun x => (q x, s x)) = 0 := by
  have hstate : fairPairOutputEntropy (fairPairState x₀ x₁) = Real.log 2 :=
    fairPairOutputEntropy_distinct _ (by simpa [fairPairState] using hne)
  have hsplit :
      (fun b : Bool => (q (fairPairState x₀ x₁ b), s (fairPairState x₀ x₁ b))) true ≠
        (fun b : Bool => (q (fairPairState x₀ x₁ b), s (fairPairState x₀ x₁ b))) false := by
    simpa [fairPairState] using
      (fun hp : (q x₀, s x₀) = (q x₁, s x₁) => hs (congrArg Prod.snd hp))
  have hrecord :
      fairPairOutputEntropy
        (fun b : Bool => (q (fairPairState x₀ x₁ b), s (fairPairState x₀ x₁ b))) =
          Real.log 2 :=
    fairPairOutputEntropy_distinct _ hsplit
  have hjoint :
      fairPairOutputEntropy
        (fun b : Bool =>
          (fairPairState x₀ x₁ b,
            (q (fairPairState x₀ x₁ b), s (fairPairState x₀ x₁ b)))) =
          Real.log 2 :=
    (fairPairJointEntropy_eq_state x₀ x₁ (fun x : X => (q x, s x))).trans hstate
  change
    fairPairOutputEntropy
        (fun b : Bool =>
          (fairPairState x₀ x₁ b,
            (q (fairPairState x₀ x₁ b), s (fairPairState x₀ x₁ b)))) -
      fairPairOutputEntropy
        (fun b : Bool =>
          (q (fairPairState x₀ x₁ b), s (fairPairState x₀ x₁ b))) = 0
  rw [hjoint, hrecord]
  ring

/-- The full arbitrary-carrier merged-pair result in bits: one bit remains
after q, while the actual augmented record with any separating s leaves zero. -/
theorem fairMergedPair_entropy_recovered_bits {X Q S : Type*} (q : X → Q)
    (s : X → S) {x₀ x₁ : X}
    (h : MergedPair.IsMergedPair q x₀ x₁) (hs : s x₀ ≠ s x₁) :
    fairPairConditionalEntropy x₀ x₁ q / Real.log 2 = 1 ∧
      fairPairConditionalEntropy x₀ x₁ (fun x => (q x, s x)) / Real.log 2 = 0 := by
  have hlog : Real.log 2 ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [fairMergedPair_condEntropy_log_two q h,
    fairPair_condEntropy_side_zero q s h.1 hs]
  simp [hlog]

/-- The indicator of one point among `n ≥ 2` has entropy `log n` nats precisely for `n = 2`. -/
theorem selfTest_entropy_eq_log_iff (n : ℕ) (hn : 2 ≤ n) :
    Real.binEntropy (1 / (n : ℝ)) = Real.log n ↔ n = 2 := by
  constructor
  · intro h
    by_contra hne
    have hn3 : 3 ≤ n := by omega
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have hprod : 0 < (((n : ℝ) - 1) / n) * Real.log ((n : ℝ) - 1) :=
      mul_pos (div_pos (by linarith) (by linarith)) (Real.log_pos (by linarith))
    have hdecomp := log_eq_binEntropy_add n hn
    linarith
  · intro h
    subst n
    exact (selfTest_one_bit_iff 2).mpr rfl

/-- The indicator among `n ≥ 2` states carries `logb 2 n` bits precisely for a pair. -/
theorem selfTest_bits_eq_logb_iff (n : ℕ) (hn : 2 ≤ n) :
    Real.binEntropy (1 / (n : ℝ)) / Real.log 2 = Real.logb 2 n ↔ n = 2 := by
  change (Real.binEntropy (1 / (n : ℝ)) / Real.log 2 =
    Real.log n / Real.log 2) ↔ n = 2
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  constructor
  · intro h
    have hmul := congrArg (fun z : ℝ => z * Real.log 2) h
    have heq : Real.binEntropy (1 / (n : ℝ)) = Real.log n := by
      field_simp [hlog2] at hmul
      exact hmul
    exact (selfTest_entropy_eq_log_iff n hn).mp heq
  · intro h
    exact congrArg (fun z : ℝ => z / Real.log 2)
      ((selfTest_entropy_eq_log_iff n hn).mpr h)

/-! ## Proposition 5.3 at the attained range, for arbitrary output carriers -/

/-- The actual attained record, as a point in the image subtype.
Unlike the ambient type Q, this subtype is finite whenever X is finite. -/
def attainedObserver {X Q : Type*} (q : X → Q) (x : X) : Set.range q :=
  ⟨q x, ⟨x, rfl⟩⟩

/-- Canonical finite enumeration of the attained range of a finite-domain
observer. No finite or decidable structure on its ambient record type Q. -/
noncomputable def attainedRangeFintype {X Q : Type*} [Fintype X]
    (q : X → Q) : Fintype (Set.range q) := by
  classical
  have hsurj : Function.Surjective (attainedObserver q) := by
    rintro ⟨y, ⟨x, hx⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  exact Fintype.ofSurjective (attainedObserver q) hsurj

/-- The actual uniform-state pushforward probability of an attained record.
The preimage count is a finite sum over X, irrespective of Q. -/
noncomputable def attainedUniformRecordMass {X Q : Type*} [Fintype X]
    (q : X → Q) (y : Set.range q) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun x : X => attainedObserver q x = y)).card : ℝ) /
    Fintype.card X

/-- Shannon entropy in nats of the actual pushforward uniform-state law,
restricted to the finite attained output range. -/
noncomputable def attainedUniformRecordEntropy {X Q : Type*} [Fintype X]
    (q : X → Q) : ℝ := by
  classical
  letI : Fintype (Set.range q) := attainedRangeFintype q
  exact entropy (attainedUniformRecordMass q)

/-- The actual average of the logarithmic fiber sizes over attained
records; empty ambient outputs never contribute and Q need not be finite. -/
noncomputable def attainedUniformMeanLogFiber {X Q : Type*} [Fintype X]
    (q : X → Q) : ℝ := by
  classical
  letI : Fintype (Set.range q) := attainedRangeFintype q
  exact ∑ y : Set.range q, attainedUniformRecordMass q y *
    Real.log ((Finset.univ.filter (fun x : X => attainedObserver q x = y)).card)

/-- The entropy of the actual uniform state law conditional on its
deterministic record. This is joint entropy minus record entropy because
(state,q(state)) is a one-to-one encoding of the state. -/
noncomputable def attainedUniformConditionalEntropy {X Q : Type*}
    [Fintype X] (q : X → Q) : ℝ :=
  entropy (fun _ : X => (1 : ℝ) / Fintype.card X) -
    attainedUniformRecordEntropy q

/-- Exact generic form of Proposition 5.3(i). The only finiteness
assumption is on X, and the right-hand sum uses precisely range(q). -/
theorem attainedUniformConditionalEntropy_eq_meanLog {X Q : Type*}
    [Fintype X] [Nonempty X] (q : X → Q) :
    attainedUniformConditionalEntropy q = attainedUniformMeanLogFiber q := by
  classical
  letI : Fintype (Set.range q) := attainedRangeFintype q
  change
    entropy (fun _ : X => (1 : ℝ) / Fintype.card X) -
      entropy (fun y : Set.range q =>
        ((Finset.univ.filter (fun x : X => attainedObserver q x = y)).card : ℝ) /
          Fintype.card X) =
      ∑ y : Set.range q,
        (((Finset.univ.filter (fun x : X => attainedObserver q x = y)).card : ℝ) /
          Fintype.card X) *
        Real.log ((Finset.univ.filter (fun x : X => attainedObserver q x = y)).card)
  exact condEntropy_uniform (attainedObserver q)

/-- Full null-record equality case on an arbitrary record type: the
conditional entropy is the entire uniform state entropy iff q is constant. -/
theorem attainedUniformConditionalEntropy_eq_log_card_iff {X Q : Type*}
    [Fintype X] [Nonempty X] (q : X → Q) :
    attainedUniformConditionalEntropy q = Real.log (Fintype.card X) ↔
      ∀ x x' : X, q x = q x' := by
  classical
  letI : Fintype (Set.range q) := attainedRangeFintype q
  have heq := condEntropy_uniform_eq_log_card_iff (attainedObserver q)
  rw [attainedUniformConditionalEntropy_eq_meanLog]
  constructor
  · intro h x x'
    have hsum :
        (∑ y : Set.range q,
          (((Finset.univ.filter (fun z : X => attainedObserver q z = y)).card : ℝ) /
            Fintype.card X) *
          Real.log ((Finset.univ.filter
            (fun z : X => attainedObserver q z = y)).card)) =
          Real.log (Fintype.card X) := by
      simpa [attainedUniformMeanLogFiber, attainedUniformRecordMass] using h
    exact congrArg Subtype.val ((heq.mp hsum) x x')
  · intro h
    have hh : ∀ x x' : X, attainedObserver q x = attainedObserver q x' := by
      intro x x'
      exact Subtype.ext (h x x')
    have hsum := heq.mpr hh
    simpa [attainedUniformMeanLogFiber, attainedUniformRecordMass] using hsum

/-- Full injective-record equality case on arbitrary Q, with no
Fintype Q hypothesis: conditional entropy is zero iff q is injective. -/
theorem attainedUniformConditionalEntropy_eq_zero_iff {X Q : Type*}
    [Fintype X] [Nonempty X] (q : X → Q) :
    attainedUniformConditionalEntropy q = 0 ↔ Function.Injective q := by
  classical
  letI : Fintype (Set.range q) := attainedRangeFintype q
  have heq := condEntropy_uniform_eq_zero_iff (attainedObserver q)
  rw [attainedUniformConditionalEntropy_eq_meanLog]
  constructor
  · intro h
    have hsum :
        (∑ y : Set.range q,
          (((Finset.univ.filter (fun z : X => attainedObserver q z = y)).card : ℝ) /
            Fintype.card X) *
          Real.log ((Finset.univ.filter
            (fun z : X => attainedObserver q z = y)).card)) = 0 := by
      simpa [attainedUniformMeanLogFiber, attainedUniformRecordMass] using h
    have hinj := heq.mp hsum
    intro x x' hxx'
    exact hinj (Subtype.ext hxx')
  · intro hinj
    have hsub : Function.Injective (attainedObserver q) := by
      intro x x' hxx'
      exact hinj (congrArg Subtype.val hxx')
    have hsum := heq.mpr hsub
    simpa [attainedUniformMeanLogFiber, attainedUniformRecordMass] using hsum

/-- Every attained record has nonnegative pushforward probability,
without requiring decidable equality on the ambient record type. -/
theorem attainedUniformRecordMass_nonneg {X Q : Type*} [Fintype X]
    (q : X → Q) (y : Set.range q) :
    0 ≤ attainedUniformRecordMass q y := by
  classical
  unfold attainedUniformRecordMass
  positivity

/-- The actual joint observation (state,q(state)) is injective. Thus its
attained-range pushforward entropy agrees with the entropy of the state.
This proof reuses the full generic zero-conditional-entropy characterization. -/
theorem attainedUniformJointEntropy_eq_state {X Q : Type*}
    [Fintype X] [Nonempty X] (q : X → Q) :
    attainedUniformRecordEntropy (fun x : X => (x, q x)) =
      entropy (fun _ : X => (1 : ℝ) / Fintype.card X) := by
  have hcompat : Function.Injective (fun x : X => (x, q x)) := by
    intro x x' h
    exact congrArg Prod.fst h
  have hzero :=
    (attainedUniformConditionalEntropy_eq_zero_iff
      (fun x : X => (x, q x))).mpr hcompat
  unfold attainedUniformConditionalEntropy at hzero
  linarith

/-- The true Shannon conditional entropy H(state | record) is the entropy
of the actual joint pushforward minus that of the actual record marginal.
In particular, the original uniform-entropy-minus-record definition is
not a surrogate or an assumption about an unconstructed joint law. -/
theorem attainedUniformConditionalEntropy_eq_joint_sub_record {X Q : Type*}
    [Fintype X] [Nonempty X] (q : X → Q) :
    attainedUniformConditionalEntropy q =
      attainedUniformRecordEntropy (fun x : X => (x, q x)) -
        attainedUniformRecordEntropy q := by
  rw [attainedUniformJointEntropy_eq_state]
  rfl

/-- The total probability mass of all actually attained outputs of a
finite-domain observer. This sum is taken over the finite attained subtype. -/
noncomputable def attainedUniformRecordTotal {X Q : Type*} [Fintype X]
    (q : X → Q) : ℝ := by
  classical
  letI : Fintype (Set.range q) := attainedRangeFintype q
  exact ∑ y : Set.range q, attainedUniformRecordMass q y

/-- The attained-range record distribution really is a probability law.
No finiteness or decidability hypothesis on the ambient record type Q. -/
theorem attainedUniformRecordTotal_eq_one {X Q : Type*}
    [Fintype X] [Nonempty X] (q : X → Q) :
    attainedUniformRecordTotal q = 1 := by
  classical
  letI : Fintype (Set.range q) := attainedRangeFintype q
  have hn : (Fintype.card X : ℝ) ≠ 0 := by
    have hp : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
    exact hp.ne'
  change
    (∑ y : Set.range q,
      (((Finset.univ.filter (fun x : X => attainedObserver q x = y)).card : ℝ) /
        Fintype.card X)) = 1
  rw [← Finset.sum_div, fiber_card_sum (attainedObserver q), div_self hn]

/-! ## Uniform laws on isolated finite fibers, without finite ambient X or Q -/

/-- The conditional entropy on the actual finite state support C under
the uniform law, with outputs restricted to those attained by its states.
The ambient state and record carriers can both be infinite. -/
noncomputable def isolatedFiberUniformConditionalEntropy {X Q : Type*}
    (q : X → Q) (C : Finset X) (_hC : C.Nonempty) : ℝ := by
  classical
  exact attainedUniformConditionalEntropy (fun x : ↥C => q x.val)

/-- A uniform finite nonempty fiber leaves log(card C) nats of state
entropy. The finite support C alone is required, not Fintype X or Q. -/
theorem isolatedFiberUniformConditionalEntropy_eq_log_card {X Q : Type*}
    (q : X → Q) (C : Finset X) (hC : C.Nonempty)
    (hconstant : ∀ x ∈ C, ∀ x' ∈ C, q x = q x') :
    isolatedFiberUniformConditionalEntropy q C hC = Real.log C.card := by
  classical
  letI : Nonempty (↥C) := ⟨⟨hC.choose, hC.choose_spec⟩⟩
  have hc : ∀ x x' : ↥C, q x.val = q x'.val := by
    intro x x'
    exact hconstant x.val x.property x'.val x'.property
  have heq :
      attainedUniformConditionalEntropy (fun x : ↥C => q x.val) =
        Real.log (Fintype.card (↥C)) :=
    (attainedUniformConditionalEntropy_eq_log_card_iff
      (fun x : ↥C => q x.val)).mpr hc
  change attainedUniformConditionalEntropy (fun x : ↥C => q x.val) =
    Real.log C.card
  simpa only [Fintype.card_coe] using heq

/-- The same arbitrary-carrier uniform-fiber theorem expressed in bits. -/
theorem isolatedFiberUniformConditionalEntropy_bits {X Q : Type*}
    (q : X → Q) (C : Finset X) (hC : C.Nonempty)
    (hconstant : ∀ x ∈ C, ∀ x' ∈ C, q x = q x') :
    isolatedFiberUniformConditionalEntropy q C hC / Real.log 2 =
      Real.logb 2 C.card := by
  rw [isolatedFiberUniformConditionalEntropy_eq_log_card q C hC hconstant]
  rfl

/-! ## Proposition 5.3(iv): an actual uniform product and its projection -/

/-- The actual probability mass of the first-coordinate record under the
uniform law on X × Bool. Equality decisions are classical inside this
noncomputable definition, not required of the caller or theorem header. -/
noncomputable def uniformProductProjectionMass (X : Type*)
    [Fintype X] (x : X) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun z : X × Bool => z.1 = x)).card : ℝ) /
    Fintype.card (X × Bool)

/-- The first-coordinate projection of X × Bool leaves exactly one bit in
the actual conditional entropy, with the uniform product-state law.
This is more than the logarithmic-cardinality identity
pair_system_log_card: both the pushed-forward record law and entropy
difference are explicitly present. -/
theorem uniformProductProjection_condEntropy_one_bit (X : Type*)
    [Fintype X] [Nonempty X] :
    entropy (fun _ : X × Bool => (1 : ℝ) / Fintype.card (X × Bool)) -
      entropy (uniformProductProjectionMass X) = Real.log 2 := by
  classical
  have hcount (x : X) :
      (Finset.univ.filter (fun z : X × Bool => z.1 = x)).card = 2 := by
    have hset :
        (Finset.univ.filter (fun z : X × Bool => z.1 = x)) =
          ({(x, true), (x, false)} : Finset (X × Bool)) := by
      ext z
      rcases z with ⟨y, b⟩
      cases b <;> simp
    rw [hset]
    simp
  have hn : (0 : ℝ) < Fintype.card X := by
    exact_mod_cast Fintype.card_pos
  have hmass (x : X) :
      uniformProductProjectionMass X x =
        (1 : ℝ) / Fintype.card X := by
    unfold uniformProductProjectionMass
    rw [hcount x, Fintype.card_prod, Fintype.card_bool]
    push_cast
    field_simp [hn.ne']
    ring
  have hrecord :
      uniformProductProjectionMass X =
      (fun _ : X => (1 : ℝ) / Fintype.card X) :=
    funext hmass
  calc
    entropy (fun _ : X × Bool => (1 : ℝ) / Fintype.card (X × Bool)) -
        entropy (uniformProductProjectionMass X) =
      Real.log (Fintype.card (X × Bool)) - Real.log (Fintype.card X) := by
        rw [entropy_uniform (X × Bool), hrecord, entropy_uniform X]
    _ = Real.log 2 := by
      rw [pair_system_log_card X]
      ring

/-- Base-two normalization of the actual product projection theorem. -/
theorem uniformProductProjection_condEntropy_bits (X : Type*)
    [Fintype X] [Nonempty X] :
    (entropy (fun _ : X × Bool => (1 : ℝ) / Fintype.card (X × Bool)) -
      entropy (uniformProductProjectionMass X)) / Real.log 2 = 1 := by
  rw [uniformProductProjection_condEntropy_one_bit X]
  exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

/-- The product-projection entropy law, localized to any nonempty finite
support C in a possibly infinite ambient state carrier X. -/
noncomputable def isolatedSupportProductConditionalEntropy {X : Type*}
    (C : Finset X) (_hC : C.Nonempty) : ℝ := by
  classical
  exact
    entropy (fun _ : ↥C × Bool => (1 : ℝ) / Fintype.card (↥C × Bool)) -
      entropy (uniformProductProjectionMass (↥C))

/-- The conditional entropy of the unobserved Boolean coordinate is one
bit even when the ambient state type X has infinitely many states.
Only the actual finite support C is counted. -/
theorem isolatedSupportProductConditionalEntropy_eq_log_two {X : Type*}
    (C : Finset X) (hC : C.Nonempty) :
    isolatedSupportProductConditionalEntropy C hC = Real.log 2 := by
  classical
  letI : Nonempty (↥C) := ⟨⟨hC.choose, hC.choose_spec⟩⟩
  change
    entropy (fun _ : ↥C × Bool => (1 : ℝ) / Fintype.card (↥C × Bool)) -
      entropy (uniformProductProjectionMass (↥C)) = Real.log 2
  exact uniformProductProjection_condEntropy_one_bit (↥C)

end OperatorKO7.Meta.BoundaryObserver.BitDivision
