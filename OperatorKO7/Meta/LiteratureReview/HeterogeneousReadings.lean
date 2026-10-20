import Mathlib

namespace OperatorKO7.Meta.LiteratureReview

/-!
The manuscript label cor:heterogeneous-readings bounds acquired conditional
information by expected discrimination and adaptive squared-bias sums,
bounds the error and information of independent readings, and characterizes
equality in the comparison of squared biases with their mean.
Finite stopped protocols are represented by finite decision trees; every
random choice and reading outcome is retained. Initial records carry
arbitrary conditional priors. All probabilities are finite real mass functions.
Clause (iii) requires a fair label, independence conditional on that label,
and 0 < eta <= 1/2. Clause (iv) uses a positive number of readings.
-/

noncomputable section
open scoped BigOperators
open Set

namespace HeterogeneousReadings

@[ext]
structure Row (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

instance {α : Type*} [Fintype α] :
    CoeFun (Row α) (fun _ => α → ℝ) := ⟨Row.mass⟩

variable {α : Type*} [Fintype α]

def hb (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2
lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

def cell (a b : ℝ) : ℝ :=
  (Real.negMulLog a + Real.negMulLog b - Real.negMulLog (a + b)) / Real.log 2

def gap (θ a b : ℝ) : ℝ :=
  Real.negMulLog (θ * a + (1 - θ) * b) -
    θ * Real.negMulLog a - (1 - θ) * Real.negMulLog b

def information (θ : ℝ) (P Q : Row α) : ℝ :=
  (∑ y, gap θ (P y) (Q y)) / Real.log 2

def discrimination (P Q : Row α) : ℝ :=
  ∑ y, (P y - Q y) ^ 2 / (P y + Q y)

lemma cell_scale (a b r : ℝ) : cell (a * r) (b * r) = r * cell a b := by
  unfold cell
  rw [← add_mul]
  simp only [Real.negMulLog_mul]
  ring

lemma cell_normalized (θ : ℝ) : cell θ (1 - θ) = hb θ := by
  unfold cell hb
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    show θ + (1 - θ) = 1 by ring]
  simp

lemma cell_symm (a b : ℝ) : cell a b = cell b a := by
  simp [cell, add_comm]

lemma cell_split (θ : ℝ) (P Q : Row α) :
    cell θ (1 - θ) - ∑ y, cell (θ * P y) ((1 - θ) * Q y) =
      information θ P Q := by
  unfold cell information gap
  rw [← Finset.sum_div, ← sub_div]
  congr 1
  rw [show θ + (1 - θ) = 1 by ring]
  simp only [Real.negMulLog_one, sub_zero]
  simp only [Real.negMulLog_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, P.total, Q.total, one_mul]
  ring

lemma cell_posterior {a b : ℝ} (ha : 0 ≤ a) (hb' : 0 ≤ b) :
    cell a b = (a + b) * hb (a / (a + b)) := by
  by_cases hz : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, cell]
  let θ := a / (a + b)
  have ha1 : θ * (a + b) = a := by dsimp [θ]; field_simp [hz]
  have hb1 : (1 - θ) * (a + b) = b := by
    dsimp [θ]
    field_simp [hz]
  calc
    cell a b = cell (θ * (a + b)) ((1 - θ) * (a + b)) := by rw [ha1, hb1]
    _ = (a + b) * cell θ (1 - θ) := cell_scale _ _ _
    _ = _ := by rw [cell_normalized]

lemma posterior_mem {a b : ℝ} (ha : 0 ≤ a) (hb' : 0 ≤ b)
    (hs : 0 < a + b) : a / (a + b) ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg ha hs.le
  · apply (div_le_iff₀ hs).2
    linarith

lemma scaled_gain {a b : ℝ} (ha : 0 ≤ a) (hb' : 0 ≤ b)
    (hs : 0 < a + b) (P Q : Row α) :
    cell a b - ∑ y, cell (a * P y) (b * Q y) =
      (a + b) * information (a / (a + b)) P Q := by
  let θ := a / (a + b)
  have ha1 : θ * (a + b) = a := by
    dsimp [θ]
    exact div_mul_cancel₀ a hs.ne'
  have hb1 : (1 - θ) * (a + b) = b := by
    dsimp [θ]
    field_simp [hs.ne']
  have hc (y : α) :
      cell (a * P y) (b * Q y) =
        (a + b) * cell (θ * P y) ((1 - θ) * Q y) := by
    have hP : (θ * P y) * (a + b) = a * P y := by
      calc
        _ = (θ * (a + b)) * P y := by ring
        _ = _ := by rw [ha1]
    have hQ : ((1 - θ) * Q y) * (a + b) = b * Q y := by
      calc
        _ = ((1 - θ) * (a + b)) * Q y := by ring
        _ = _ := by rw [hb1]
    simpa only [hP, hQ] using cell_scale (θ * P y) ((1 - θ) * Q y) (a + b)
  rw [cell_posterior ha hb']
  simp_rw [hc]
  rw [← Finset.mul_sum, ← mul_sub, ← cell_normalized, cell_split]

lemma xlog_bound {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) :
    a * Real.log a - a * Real.log m ≤ a * (a - m) / m := by
  by_cases hz : a = 0
  · simp [hz]
  have hap : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hz)
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hap hm)) ha
  rw [Real.log_div hz hm.ne'] at h
  have he : a * (a / m - 1) = a * (a - m) / m := by
    field_simp [hm.ne']
  rw [he] at h
  nlinarith

lemma gap_le_discrimination {θ a b : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (ha : 0 ≤ a) (hb' : 0 ≤ b) :
    gap θ a b ≤ (a - b) ^ 2 / (a + b) := by
  have hd := div_nonneg (sq_nonneg (a - b)) (add_nonneg ha hb')
  by_cases h0 : θ = 0
  · simpa [gap, h0] using hd
  by_cases h1 : θ = 1
  · simpa [gap, h1] using hd
  have ht : 0 < θ := lt_of_le_of_ne hθ.1 (by simpa [eq_comm] using h0)
  have hu : 0 < 1 - θ := by rcases hθ with ⟨_, h⟩; linarith +splitNe
  by_cases hz : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, gap]
  have hs : 0 < a + b :=
    lt_of_le_of_ne (add_nonneg ha hb') (by simpa [eq_comm] using hz)
  let m := θ * a + (1 - θ) * b
  have hm : 0 < m := by
    by_cases ha0 : a = 0
    · have bp : 0 < b := by linarith
      dsimp [m]
      positivity
    · have ap : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
      dsimp [m]
      positivity
  have hc : θ * (1 - θ) * (a + b) ≤ m := by
    have hA := mul_nonneg (sq_nonneg θ) ha
    have hB := mul_nonneg (sq_nonneg (1 - θ)) hb'
    dsimp [m]
    nlinarith
  calc
    gap θ a b =
        θ * (a * Real.log a - a * Real.log m) +
        (1 - θ) * (b * Real.log b - b * Real.log m) := by
      simp only [gap, Real.negMulLog]
      dsimp [m]
      ring
    _ ≤ θ * (a * (a - m) / m) + (1 - θ) * (b * (b - m) / m) :=
      add_le_add (mul_le_mul_of_nonneg_left (xlog_bound ha hm) ht.le)
        (mul_le_mul_of_nonneg_left (xlog_bound hb' hm) hu.le)
    _ = θ * (1 - θ) * (a - b) ^ 2 / m := by
      field_simp [hm.ne']
      dsimp [m]
      ring
    _ ≤ (a - b) ^ 2 / (a + b) := by
      apply (div_le_div_iff₀ hm hs).2
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (a - b))]

lemma information_le_discrimination (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (P Q : Row α) :
    information θ P Q ≤ discrimination P Q / Real.log 2 := by
  apply div_le_div_of_nonneg_right _ log_two_pos.le
  exact Finset.sum_le_sum (fun y _ =>
    gap_le_discrimination hθ (P.nonneg y) (Q.nonneg y))

def entropyAux (x : ℝ) : ℝ :=
  x * Real.negMulLog x - (1 - x) * Real.negMulLog (1 - x)

lemma entropyAux_deriv {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt entropyAux (2 * Real.binEntropy x - 1) x := by
  have hi := hasDerivAt_id x
  have hq := hi.const_sub 1
  have hn := (Real.hasDerivAt_negMulLog (sub_ne_zero.mpr h1.symm)).comp x hq
  convert (hi.mul (Real.hasDerivAt_negMulLog h0)).sub (hq.mul hn) using 1 ;
    simp only [Real.binEntropy, Real.log_inv, Real.negMulLog,
      Function.comp_def, id] ; ring

lemma entropyAux_nonpos {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    entropyAux x ≤ 0 := by
  have hc : Continuous entropyAux := by unfold entropyAux; fun_prop
  have hv : ConvexOn ℝ (Icc (0 : ℝ) (1 / 2)) entropyAux := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _) hc.continuousOn
    · intro z hz
      simp only [interior_Icc, mem_Ioo] at hz
      exact (entropyAux_deriv (by linarith) (by linarith)).differentiableAt.differentiableWithinAt
    · intro z hz w hw hzw
      simp only [interior_Icc, mem_Ioo] at hz hw
      rw [(entropyAux_deriv (by linarith : z ≠ 0) (by linarith : z ≠ 1)).deriv,
        (entropyAux_deriv (by linarith : w ≠ 0) (by linarith : w ≠ 1)).deriv]
      have h := Real.binEntropy_strictMonoOn.monotoneOn
        (show z ∈ Icc (0 : ℝ) 2⁻¹ by constructor <;> norm_num at * <;> linarith)
        (show w ∈ Icc (0 : ℝ) 2⁻¹ by constructor <;> norm_num at * <;> linarith) hzw
      linarith
  have h := hv.2
    (show (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) by norm_num)
    (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) by norm_num)
    (show 0 ≤ 1 - 2 * x by linarith [hx.2])
    (show 0 ≤ 2 * x by linarith [hx.1])
    (show (1 - 2 * x) + 2 * x = 1 by ring)
  have h0 : entropyAux 0 = 0 := by simp [entropyAux]
  have hhalf : entropyAux (1 / 2) = 0 := by norm_num [entropyAux]
  simp only [smul_eq_mul] at h
  rw [show (1 - 2 * x) * 0 + (2 * x) * (1 / 2) = x by ring, h0, hhalf] at h
  simpa only [mul_zero, add_zero] using h

def entropyRatio (x : ℝ) : ℝ := Real.binEntropy x / (x * (1 - x))

lemma entropyRatio_deriv {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    HasDerivAt entropyRatio (entropyAux x / (x * (1 - x)) ^ 2) x := by
  have hi := hasDerivAt_id x
  have hd := hi.mul (hi.const_sub 1)
  have hden : x * (1 - x) ≠ 0 :=
    ne_of_gt (mul_pos h0 (sub_pos.mpr h1))
  convert (Real.hasDerivAt_binEntropy h0.ne' h1.ne).div hd hden using 1 ;
    simp only [entropyAux, Real.binEntropy, Real.log_inv,
      Real.negMulLog, id, Pi.mul_def] ; ring

lemma entropy_lower_half {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    4 * Real.log 2 * x * (1 - x) ≤ Real.binEntropy x := by
  by_cases hz : x = 0
  · simp [hz]
  have hp : 0 < x := lt_of_le_of_ne hx.1 (by simpa [eq_comm] using hz)
  have hm : AntitoneOn entropyRatio (Icc x (1 / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro z hz'
      exact (entropyRatio_deriv (by linarith [hz'.1])
        (by linarith [hz'.2])).continuousAt.continuousWithinAt
    · intro z hz'
      simp only [interior_Icc, mem_Ioo] at hz'
      exact (entropyRatio_deriv (by linarith) (by linarith)).differentiableAt.differentiableWithinAt
    · intro z hz'
      simp only [interior_Icc, mem_Ioo] at hz'
      rw [(entropyRatio_deriv (by linarith : 0 < z) (by linarith : z < 1)).deriv]
      exact div_nonpos_of_nonpos_of_nonneg
        (entropyAux_nonpos ⟨by linarith, by linarith⟩) (sq_nonneg _)
  have h := hm (show x ∈ Icc x (1 / 2) from ⟨le_rfl, hx.2⟩)
    (show (1 / 2 : ℝ) ∈ Icc x (1 / 2) from ⟨hx.2, le_rfl⟩) hx.2
  have hh : entropyRatio (1 / 2) = 4 * Real.log 2 := by
    have hhalf : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
      simpa only [one_div] using Real.binEntropy_two_inv
    rw [entropyRatio, hhalf]
    norm_num ; ring
  rw [hh] at h
  have hd : 0 < x * (1 - x) := mul_pos hp (by linarith [hx.2])
  have h' := (le_div_iff₀ hd).mp h
  nlinarith

lemma entropy_lower {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    4 * Real.log 2 * x * (1 - x) ≤ Real.binEntropy x := by
  by_cases h : x ≤ 1 / 2
  · exact entropy_lower_half ⟨hx.1, h⟩
  · have he := entropy_lower_half
      (x := 1 - x) ⟨by linarith [hx.2], by linarith⟩
    rw [Real.binEntropy_one_sub] at he
    nlinarith

abbrev Bias := {ε : ℝ // ε ∈ Icc (0 : ℝ) (1 / 2)}
def kappa (ε : Bias) : ℝ := 1 - hb (1 / 2 + ε.1)

lemma kappa_le_square (ε : Bias) : kappa ε ≤ 4 * ε.1 ^ 2 := by
  have h := entropy_lower
    (x := 1 / 2 + ε.1) ⟨by linarith [ε.2.1], by linarith [ε.2.2]⟩
  have h' : 1 - 4 * ε.1 ^ 2 ≤ Real.binEntropy (1 / 2 + ε.1) / Real.log 2 := by
    apply (le_div_iff₀ log_two_pos).2
    nlinarith
  unfold kappa hb
  linarith

def bernoulli (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) : Row (Fin 2) where
  mass i := if i = 0 then p else 1 - p
  nonneg i := by split <;> linarith [hp.1, hp.2]
  total := by norm_num [Fin.sum_univ_succ]

def bscP (ε : Bias) : Row (Fin 2) :=
  bernoulli (1 / 2 + ε.1) ⟨by linarith [ε.2.1], by linarith [ε.2.2]⟩
def bscQ (ε : Bias) : Row (Fin 2) :=
  bernoulli (1 / 2 - ε.1) ⟨by linarith [ε.2.2], by linarith [ε.2.1]⟩

lemma bernoulli_information (θ p q : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    information θ (bernoulli p hp) (bernoulli q hq) =
      (Real.binEntropy (θ * p + (1 - θ) * q) -
        θ * Real.binEntropy p - (1 - θ) * Real.binEntropy q) / Real.log 2 := by
  norm_num [information, gap, bernoulli, Fin.sum_univ_succ]
  rw [show θ * (1 - p) + (1 - θ) * (1 - q) =
    1 - (θ * p + (1 - θ) * q) by ring]
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

lemma bsc_capacity (θ : ℝ) (ε : Bias) :
    information θ (bscP ε) (bscQ ε) ≤ kappa ε := by
  rw [bscP, bscQ, bernoulli_information]
  have he : Real.binEntropy (1 / 2 - ε.1) =
      Real.binEntropy (1 / 2 + ε.1) := by
    rw [show 1 / 2 - ε.1 = 1 - (1 / 2 + ε.1) by ring,
      Real.binEntropy_one_sub]
  rw [he]
  have h := Real.binEntropy_le_log_two
    (p := θ * (1 / 2 + ε.1) + (1 - θ) * (1 / 2 - ε.1))
  unfold kappa hb
  apply (div_le_iff₀ log_two_pos).2
  have hr : (1 - Real.binEntropy (1 / 2 + ε.1) / Real.log 2) * Real.log 2 =
      Real.log 2 - Real.binEntropy (1 / 2 + ε.1) := by
    field_simp [log_two_pos.ne']
  rw [hr]
  nlinarith

def bayesError (P Q : Row α) : ℝ := ∑ y, min (P y / 2) (Q y / 2)
def likelihoodDecoder (P Q : Row α) (y : α) : Bool :=
  if Q y ≤ P y then true else false
def decoderError (P Q : Row α) (d : α → Bool) : ℝ :=
  ∑ y, if d y then Q y / 2 else P y / 2

lemma likelihood_error (P Q : Row α) :
    decoderError P Q (likelihoodDecoder P Q) = bayesError P Q := by
  unfold decoderError bayesError
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : Q y ≤ P y
  · have h' : Q y / 2 ≤ P y / 2 := by linarith
    simp [likelihoodDecoder, h, min_eq_right h']
  · have h' : P y / 2 ≤ Q y / 2 := by linarith
    simp [likelihoodDecoder, h, min_eq_left h']

lemma bayesError_nonneg (P Q : Row α) : 0 ≤ bayesError P Q :=
  Finset.sum_nonneg (fun y _ => le_min
    (div_nonneg (P.nonneg y) (by norm_num)) (div_nonneg (Q.nonneg y) (by norm_num)))

lemma cell_min {a b : ℝ} (ha : 0 ≤ a) (hb' : 0 ≤ b) :
    cell a b = (a + b) * hb (min a b / (a + b)) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h]
    exact cell_posterior ha hb'
  · rw [min_eq_right (le_of_not_ge h), cell_symm a b]
    simpa only [add_comm] using cell_posterior hb' ha

lemma fano_cells (a b : α → ℝ) (ha : ∀ y, 0 ≤ a y) (hb' : ∀ y, 0 ≤ b y)
    (ht : ∑ y, (a y + b y) = 1) :
    (∑ y, cell (a y) (b y)) ≤ hb (∑ y, min (a y) (b y)) := by
  let w := fun y => a y + b y
  let e := fun y => min (a y) (b y) / w y
  have hw (y) : 0 ≤ w y := add_nonneg (ha y) (hb' y)
  have he (y) : e y ∈ Icc (0 : ℝ) 1 := by
    by_cases hz : w y = 0
    · simp [e, hz]
    · have hp : 0 < w y := lt_of_le_of_ne (hw y) (by simpa [eq_comm] using hz)
      constructor
      · exact div_nonneg (le_min (ha y) (hb' y)) (hw y)
      · apply (div_le_iff₀ hp).2
        dsimp [w]
        linarith [min_le_left (a y) (b y), hb' y]
  have hew (y) : w y * e y = min (a y) (b y) := by
    by_cases hz : w y = 0
    · have ha0 : a y = 0 := by dsimp [w] at hz; linarith [ha y, hb' y]
      have hb0 : b y = 0 := by dsimp [w] at hz; linarith [ha y, hb' y]
      simp [w, e, ha0, hb0]
    · dsimp [e]
      field_simp [hz]
  have hj := Real.strictConcave_binEntropy.concaveOn.le_map_sum
    (t := Finset.univ) (w := w) (p := e)
    (fun y _ => hw y) ht (fun y _ => he y)
  have hj' : (∑ y, w y * Real.binEntropy (e y)) ≤
      Real.binEntropy (∑ y, min (a y) (b y)) := by
    simpa only [smul_eq_mul, hew] using hj
  calc
    (∑ y, cell (a y) (b y)) =
        (∑ y, w y * Real.binEntropy (e y)) / Real.log 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y _
      rw [cell_min (ha y) (hb' y)]
      dsimp [w, e, hb]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hj' log_two_pos.le

lemma fair_information (P Q : Row α) :
    information (1 / 2) P Q = 1 - ∑ y, cell (P y / 2) (Q y / 2) := by
  have hhalf : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
    simpa only [one_div] using Real.binEntropy_two_inv
  rw [← cell_split, cell_normalized, hb, hhalf, div_self log_two_pos.ne']
  norm_num [div_eq_mul_inv, mul_comm]

lemma fair_fano (P Q : Row α) :
    1 - hb (bayesError P Q) ≤ information (1 / 2) P Q := by
  have h := fano_cells (fun y => P y / 2) (fun y => Q y / 2)
    (fun y => div_nonneg (P.nonneg y) (by norm_num))
    (fun y => div_nonneg (Q.nonneg y) (by norm_num))
    (by rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
      P.total, Q.total]; norm_num)
  rw [fair_information]
  exact sub_le_sub_left h 1

lemma information_of_error (P Q : Row α) {η : ℝ}
    (hη : 0 < η) (hhalf : η ≤ 1 / 2) (he : bayesError P Q ≤ η) :
    1 - hb η ≤ information (1 / 2) P Q := by
  have h := Real.binEntropy_strictMonoOn.monotoneOn
    ⟨bayesError_nonneg P Q, by simpa only [one_div] using he.trans hhalf⟩
    ⟨hη.le, by simpa only [one_div] using hhalf⟩ he
  have hb' : hb (bayesError P Q) ≤ hb η :=
    div_le_div_of_nonneg_right h log_two_pos.le
  exact (sub_le_sub_left hb' 1).trans (fair_fano P Q)

def BC (P Q : Row α) : ℝ := ∑ y, Real.sqrt (P y * Q y)

lemma BC_nonneg (P Q : Row α) : 0 ≤ BC P Q :=
  Finset.sum_nonneg (fun _y _ => Real.sqrt_nonneg _)

lemma min_half (a b : ℝ) : min (a / 2) (b / 2) = min a b / 2 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (by linarith : a / 2 ≤ b / 2)]
  · rw [min_eq_right h, min_eq_right (by linarith : b / 2 ≤ a / 2)]

lemma error_le_BC (P Q : Row α) : bayesError P Q ≤ BC P Q / 2 := by
  unfold bayesError BC
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro y _
  rw [min_half]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hm : 0 ≤ min (P y) (Q y) := le_min (P.nonneg y) (Q.nonneg y)
  have hs : (min (P y) (Q y)) ^ 2 ≤ P y * Q y := by
    simpa only [sq] using
      mul_le_mul (min_le_left (P y) (Q y)) (min_le_right (P y) (Q y)) hm (P.nonneg y)
  simpa only [Real.sqrt_sq hm] using Real.sqrt_le_sqrt hs

lemma triangular_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb' : 0 ≤ b) :
    (a - b) ^ 2 / (a + b) ≤ 2 * (Real.sqrt a - Real.sqrt b) ^ 2 := by
  by_cases hz : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  have hp : 0 < a + b :=
    lt_of_le_of_ne (add_nonneg ha hb') (by simpa [eq_comm] using hz)
  let s := Real.sqrt a
  let t := Real.sqrt b
  have hs : s ^ 2 = a := Real.sq_sqrt ha
  have ht : t ^ 2 = b := Real.sq_sqrt hb'
  have he : (a - b) ^ 2 = (s - t) ^ 2 * (s + t) ^ 2 := by rw [← hs, ← ht]; ring
  have hu : (s + t) ^ 2 ≤ 2 * (a + b) := by nlinarith [sq_nonneg (s - t)]
  rw [he]
  calc
    _ ≤ ((s - t) ^ 2 * (2 * (a + b))) / (a + b) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hu (sq_nonneg (s - t))) hp.le
    _ = _ := by field_simp [hz] ; ring

lemma BC_le_exp (P Q : Row α) :
    BC P Q ≤ Real.exp (-discrimination P Q / 4) := by
  have hs : (∑ y, (Real.sqrt (P y) - Real.sqrt (Q y)) ^ 2) = 2 - 2 * BC P Q := by
    calc
      _ = ∑ y, (P y + Q y - 2 * Real.sqrt (P y * Q y)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Real.sqrt_mul (P.nonneg y)]
        nlinarith [Real.sq_sqrt (P.nonneg y), Real.sq_sqrt (Q.nonneg y)]
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          P.total, Q.total]
        unfold BC
        ring
  have hd : discrimination P Q ≤ 2 * ∑ y, (Real.sqrt (P y) - Real.sqrt (Q y)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun y _ => triangular_sqrt (P.nonneg y) (Q.nonneg y))
  rw [hs] at hd
  have he := Real.add_one_le_exp (-discrimination P Q / 4)
  linarith

inductive Experiment (C : Type*) (arity : C → ℕ) where
  | stop : Experiment C arity
  | random {k : ℕ} (r : Row (Fin k)) (next : Fin k → Experiment C arity) :
      Experiment C arity
  | read (c : C) (next : Fin (arity c) → Experiment C arity) :
      Experiment C arity

variable {C : Type*} {arity : C → ℕ}

def uncertainty (P Q : ∀ c, Row (Fin (arity c))) :
    Experiment C arity → ℝ → ℝ → ℝ
  | .stop, a, b => cell a b
  | .random r next, a, b =>
      ∑ i, uncertainty P Q (next i) (a * r i) (b * r i)
  | .read c next, a, b =>
      ∑ i, uncertainty P Q (next i) (a * P c i) (b * Q c i)

def expected (P Q : ∀ c, Row (Fin (arity c))) (charge : C → ℝ) :
    Experiment C arity → ℝ → ℝ → ℝ
  | .stop, _, _ => 0
  | .random r next, a, b =>
      ∑ i, expected P Q charge (next i) (a * r i) (b * r i)
  | .read c next, a, b =>
      (a + b) * charge c + ∑ i, expected P Q charge (next i) (a * P c i) (b * Q c i)

def leafMass (P Q : ∀ c, Row (Fin (arity c))) :
    Experiment C arity → ℝ → ℝ → ℝ
  | .stop, a, b => a + b
  | .random r next, a, b =>
      ∑ i, leafMass P Q (next i) (a * r i) (b * r i)
  | .read c next, a, b =>
      ∑ i, leafMass P Q (next i) (a * P c i) (b * Q c i)

lemma leafMass_eq (P Q : ∀ c, Row (Fin (arity c)))
    (T : Experiment C arity) (a b : ℝ) : leafMass P Q T a b = a + b := by
  induction T generalizing a b with
  | stop => rfl
  | @random k r next ih =>
      simp only [leafMass, ih, Finset.sum_add_distrib, ← Finset.mul_sum, r.total, mul_one]
  | read c next ih =>
      simp only [leafMass, ih, Finset.sum_add_distrib, ← Finset.mul_sum,
        (P c).total, (Q c).total, mul_one]

lemma local_gain_bound (P Q : Row α) (K : ℝ)
    (hK : ∀ θ ∈ Icc (0 : ℝ) 1, information θ P Q ≤ K)
    {a b : ℝ} (ha : 0 ≤ a) (hb' : 0 ≤ b) :
    cell a b - ∑ y, cell (a * P y) (b * Q y) ≤ (a + b) * K := by
  by_cases hz : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, cell]
  have hs : 0 < a + b :=
    lt_of_le_of_ne (add_nonneg ha hb') (by simpa [eq_comm] using hz)
  rw [scaled_gain ha hb' hs]
  exact mul_le_mul_of_nonneg_left (hK _ (posterior_mem ha hb' hs)) hs.le

lemma tree_bound (P Q : ∀ c, Row (Fin (arity c))) (K : C → ℝ)
    (hK : ∀ c θ, θ ∈ Icc (0 : ℝ) 1 → information θ (P c) (Q c) ≤ K c)
    (T : Experiment C arity) (a b : ℝ) (ha : 0 ≤ a) (hb' : 0 ≤ b) :
    cell a b - uncertainty P Q T a b ≤ expected P Q K T a b := by
  induction T generalizing a b with
  | stop => simp [uncertainty, expected]
  | @random k r next ih =>
      change cell a b - ∑ i, uncertainty P Q (next i) (a * r i) (b * r i) ≤ _
      calc
        _ = ∑ i, (cell (a * r i) (b * r i) -
            uncertainty P Q (next i) (a * r i) (b * r i)) := by
          rw [Finset.sum_sub_distrib]
          simp_rw [cell_scale]
          rw [← Finset.sum_mul, r.total, one_mul]
        _ ≤ _ := Finset.sum_le_sum (fun i _ =>
          ih i _ _ (mul_nonneg ha (r.nonneg i)) (mul_nonneg hb' (r.nonneg i)))
  | read c next ih =>
      have hl := local_gain_bound (P c) (Q c) (K c) (hK c) ha hb'
      have hr := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
        ih i _ _ (mul_nonneg ha ((P c).nonneg i)) (mul_nonneg hb' ((Q c).nonneg i)))
      change cell a b - ∑ i, uncertainty P Q (next i) (a * P c i) (b * Q c i) ≤
        (a + b) * K c + ∑ i, expected P Q K (next i) (a * P c i) (b * Q c i)
      rw [Finset.sum_sub_distrib] at hr
      linarith

lemma expected_scale (P Q : ∀ c, Row (Fin (arity c))) (charge : C → ℝ)
    (r : ℝ) (T : Experiment C arity) (a b : ℝ) :
    expected P Q (fun c => r * charge c) T a b = r * expected P Q charge T a b := by
  induction T generalizing a b with
  | stop => simp [expected]
  | @random k w next ih =>
      simp only [expected, ih, Finset.mul_sum]
  | read c next ih =>
      simp only [expected, ih, mul_add, Finset.mul_sum]
      ring

lemma expected_mono (P Q : ∀ c, Row (Fin (arity c))) (f g : C → ℝ)
    (hfg : ∀ c, f c ≤ g c) (T : Experiment C arity)
    (a b : ℝ) (ha : 0 ≤ a) (hb' : 0 ≤ b) :
    expected P Q f T a b ≤ expected P Q g T a b := by
  induction T generalizing a b with
  | stop => simp [expected]
  | @random k r next ih =>
      exact Finset.sum_le_sum (fun i _ =>
        ih i _ _ (mul_nonneg ha (r.nonneg i)) (mul_nonneg hb' (r.nonneg i)))
  | read c next ih =>
      exact add_le_add (mul_le_mul_of_nonneg_left (hfg c) (add_nonneg ha hb'))
        (Finset.sum_le_sum (fun i _ =>
          ih i _ _ (mul_nonneg ha ((P c).nonneg i)) (mul_nonneg hb' ((Q c).nonneg i))))

structure Protocol (C : Type*) (arity : C → ℕ) (u : ℕ) where
  initial : Row (Fin u)
  prior : Fin u → ℝ
  prior_mem : ∀ i, prior i ∈ Icc (0 : ℝ) 1
  tree : Fin u → Experiment C arity

def acquired {u : ℕ} (P Q : ∀ c, Row (Fin (arity c))) (s : Protocol C arity u) : ℝ :=
  ∑ i, s.initial i * (cell (s.prior i) (1 - s.prior i) -
    uncertainty P Q (s.tree i) (s.prior i) (1 - s.prior i))

def totalCost {u : ℕ} (P Q : ∀ c, Row (Fin (arity c)))
    (s : Protocol C arity u) (charge : C → ℝ) : ℝ :=
  ∑ i, s.initial i * expected P Q charge (s.tree i) (s.prior i) (1 - s.prior i)

lemma protocol_bound {u : ℕ} (P Q : ∀ c, Row (Fin (arity c)))
    (s : Protocol C arity u) (K : C → ℝ)
    (hK : ∀ c θ, θ ∈ Icc (0 : ℝ) 1 → information θ (P c) (Q c) ≤ K c) :
    acquired P Q s ≤ totalCost P Q s K := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (tree_bound P Q K hK (s.tree i) _ _ (s.prior_mem i).1
      (by linarith [(s.prior_mem i).2])) (s.initial.nonneg i)

lemma totalCost_scale {u : ℕ} (P Q : ∀ c, Row (Fin (arity c)))
    (s : Protocol C arity u) (f : C → ℝ) (r : ℝ) :
    totalCost P Q s (fun c => r * f c) = r * totalCost P Q s f := by
  unfold totalCost
  simp only [expected_scale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma totalCost_mono {u : ℕ} (P Q : ∀ c, Row (Fin (arity c)))
    (s : Protocol C arity u) (f g : C → ℝ) (hfg : ∀ c, f c ≤ g c) :
    totalCost P Q s f ≤ totalCost P Q s g := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (expected_mono P Q f g hfg (s.tree i) _ _ (s.prior_mem i).1
      (by linarith [(s.prior_mem i).2])) (s.initial.nonneg i)

lemma discrimination_sum {u : ℕ} (P Q : ∀ c, Row (Fin (arity c)))
    (s : Protocol C arity u) :
    acquired P Q s ≤ totalCost P Q s (fun c => discrimination (P c) (Q c)) / Real.log 2 := by
  have h := protocol_bound P Q s (fun c => discrimination (P c) (Q c) / Real.log 2)
    (fun c θ hθ => information_le_discrimination θ hθ (P c) (Q c))
  have he := totalCost_scale P Q s (fun c => discrimination (P c) (Q c)) (Real.log 2)⁻¹
  have he' : totalCost P Q s (fun c => discrimination (P c) (Q c) / Real.log 2) =
      totalCost P Q s (fun c => discrimination (P c) (Q c)) / Real.log 2 := by
    simpa only [div_eq_mul_inv, mul_comm] using he
  rwa [he'] at h

lemma discrimination_target {u : ℕ} (P Q : ∀ c, Row (Fin (arity c)))
    (s : Protocol C arity u) (c : ℝ) (hc : c ≤ acquired P Q s) :
    c * Real.log 2 ≤ totalCost P Q s (fun a => discrimination (P a) (Q a)) :=
  (le_div_iff₀ log_two_pos).mp (hc.trans (discrimination_sum P Q s))

lemma adaptive_biases {u : ℕ} (s : Protocol Bias (fun _ => 2) u) :
    acquired bscP bscQ s ≤ totalCost bscP bscQ s kappa ∧
    totalCost bscP bscQ s kappa ≤ 4 * totalCost bscP bscQ s (fun ε => ε.1 ^ 2) := by
  constructor
  · exact protocol_bound bscP bscQ s kappa (fun ε θ _ => bsc_capacity θ ε)
  · have h := totalCost_mono bscP bscQ s kappa (fun ε => 4 * ε.1 ^ 2) kappa_le_square
    rwa [totalCost_scale] at h

def productRows {N : ℕ} (m : Fin N → ℕ) (P : ∀ i, Row (Fin (m i))) :
    Row (∀ i, Fin (m i)) where
  mass y := ∏ i, P i (y i)
  nonneg y := Finset.prod_nonneg (fun i _ => (P i).nonneg (y i))
  total := by
    rw [← Fintype.prod_sum]
    have h (i) : (∑ y, P i y) = 1 := (P i).total
    simp only [h, Finset.prod_const_one]

lemma sqrt_product (f : α → ℝ) (hf : ∀ i, 0 ≤ f i) :
    Real.sqrt (∏ i, f i) = ∏ i, Real.sqrt (f i) := by
  classical
  have h : ∀ s : Finset α, Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Real.sqrt_mul (hf i), ih, Finset.prod_insert hi]
  exact h Finset.univ

lemma BC_product {N : ℕ} (m : Fin N → ℕ) (P Q : ∀ i, Row (Fin (m i))) :
    BC (productRows m P) (productRows m Q) = ∏ i, BC (P i) (Q i) := by
  change (∑ y : (∀ i, Fin (m i)),
      Real.sqrt ((∏ i, P i (y i)) * (∏ i, Q i (y i)))) =
    ∏ i, ∑ z, Real.sqrt (P i z * Q i z)
  calc
    _ = ∑ y : (∀ i, Fin (m i)), ∏ i, Real.sqrt (P i (y i) * Q i (y i)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.prod_mul_distrib]
      exact sqrt_product _ (fun i => mul_nonneg ((P i).nonneg _) ((Q i).nonneg _))
    _ = _ := (Fintype.prod_sum (fun i z => Real.sqrt (P i z * Q i z))).symm

lemma independent_error {N : ℕ} (m : Fin N → ℕ) (P Q : ∀ i, Row (Fin (m i))) :
    decoderError (productRows m P) (productRows m Q)
      (likelihoodDecoder (productRows m P) (productRows m Q)) ≤ (∏ i, BC (P i) (Q i)) / 2 ∧
    (∏ i, BC (P i) (Q i)) / 2 ≤
      Real.exp (-(∑ i, discrimination (P i) (Q i)) / 4) / 2 := by
  constructor
  · rw [likelihood_error, ← BC_product]
    exact error_le_BC _ _
  · have h : (∏ i, BC (P i) (Q i)) ≤
        ∏ i, Real.exp (-discrimination (P i) (Q i) / 4) :=
      Finset.prod_le_prod (fun i _ => BC_nonneg (P i) (Q i))
        (fun i _ => BC_le_exp (P i) (Q i))
    calc
      _ ≤ (∏ i, Real.exp (-discrimination (P i) (Q i) / 4)) / 2 :=
        div_le_div_of_nonneg_right h (by norm_num)
      _ = _ := by
        rw [← Real.exp_sum]
        simp only [← Finset.sum_div, Finset.sum_neg_distrib]

lemma independent_information {N : ℕ} (m : Fin N → ℕ)
    (P Q : ∀ i, Row (Fin (m i))) {η : ℝ} (hη : 0 < η) (hhalf : η ≤ 1 / 2)
    (hD : 4 * Real.log (1 / (2 * η)) ≤ ∑ i, discrimination (P i) (Q i)) :
    1 - hb η ≤ information (1 / 2) (productRows m P) (productRows m Q) := by
  have he := independent_error m P Q
  have hl : Real.log (1 / (2 * η)) = -Real.log (2 * η) := by
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one, zero_sub]
  rw [hl] at hD
  have hx : Real.exp (-(∑ i, discrimination (P i) (Q i)) / 4) / 2 ≤ η := by
    calc
      _ ≤ Real.exp (Real.log (2 * η)) / 2 :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
      _ = _ := by rw [Real.exp_log (by positivity)]; ring
  apply information_of_error _ _ hη hhalf
  rw [← likelihood_error]
  exact he.1.trans (he.2.trans hx)

lemma information_self (θ : ℝ) (P : Row α) : information θ P P = 0 := by
  have hg (y) : gap θ (P y) (P y) = 0 := by
    unfold gap
    rw [show θ * P y + (1 - θ) * P y = P y by ring]
    ring
  simp only [information, hg, Finset.sum_const_zero, zero_div]

lemma eta_one_counterexample (P : Row α) :
    4 * Real.log (1 / (2 * (1 : ℝ))) ≤ discrimination P P ∧
    information (1 / 2) P P < 1 - hb 1 := by
  constructor
  · have hl : Real.log (1 / (2 * (1 : ℝ))) = -Real.log 2 := by
      norm_num [Real.log_div]
    rw [hl]
    simp only [discrimination, sub_self, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, Finset.sum_const_zero]
    linarith [log_two_pos]
  · rw [information_self]
    norm_num [hb]

def mean {N : ℕ} (ε : Fin N → ℝ) : ℝ := (∑ i, ε i) / N

lemma variance_identity {N : ℕ} (hN : 0 < N) (ε : Fin N → ℝ) :
    (∑ i, (ε i - mean ε) ^ 2) = (∑ i, ε i ^ 2) - N * (mean ε) ^ 2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hm : (N : ℝ) * mean ε = ∑ i, ε i := by
    unfold mean
    field_simp [hn]
  calc
    _ = ∑ i, (ε i ^ 2 - (2 * mean ε) * ε i + (mean ε) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, ε i ^ 2) - (2 * mean ε) * (∑ i, ε i) + N * (mean ε) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := by rw [← hm]; ring

lemma sum_mean {N : ℕ} (hN : 0 < N) (ε : Fin N → ℝ) :
    (N : ℝ) * (mean ε) ^ 2 ≤ ∑ i, ε i ^ 2 ∧
    ((N : ℝ) * (mean ε) ^ 2 = ∑ i, ε i ^ 2 ↔ ∃ c : ℝ, ∀ i, ε i = c) := by
  have hv := variance_identity hN ε
  have hn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    sq_nonneg (ε i - mean ε))
  constructor
  · linarith
  · constructor
    · intro he
      have hz : (∑ i, (ε i - mean ε) ^ 2) = 0 := by linarith
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i (_ : i ∈ Finset.univ) => sq_nonneg (ε i - mean ε))).mp hz
      refine ⟨mean ε, fun i => ?_⟩
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hall i (Finset.mem_univ i)))
    · rintro ⟨c, hc⟩
      have hn' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      simp only [mean, hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [hn']

def exampleBias : Fin 2 → ℝ := ![1 / 2, 0]

lemma sum_mean_example :
    (∑ i, exampleBias i ^ 2) = 1 / 4 ∧
    2 * (mean exampleBias) ^ 2 = 1 / 8 ∧
    ∀ threshold : ℝ, 1 / 8 < threshold → threshold < 1 / 4 →
      2 * (mean exampleBias) ^ 2 < threshold ∧ threshold < ∑ i, exampleBias i ^ 2 := by
  have hs : (∑ i, exampleBias i ^ 2) = 1 / 4 := by
    norm_num [exampleBias, Fin.sum_univ_succ]
  have hm : 2 * (mean exampleBias) ^ 2 = 1 / 8 := by
    norm_num [mean, exampleBias, Fin.sum_univ_succ]
  refine ⟨hs, hm, ?_⟩
  intro threshold hlow hhigh
  rw [hs, hm]
  exact ⟨hlow, hhigh⟩

end HeterogeneousReadings

open HeterogeneousReadings

theorem heterogeneous_readings
    {C : Type*} {arity : C → ℕ} {u v N M : ℕ}
    (P Q : ∀ c, Row (Fin (arity c))) (s : Protocol C arity u)
    (b : Protocol Bias (fun _ => 2) v)
    (m : Fin N → ℕ) (R S : ∀ i, Row (Fin (m i)))
    (hM : 0 < M) (ε : Fin M → ℝ) :
    (acquired P Q s ≤ totalCost P Q s (fun c => discrimination (P c) (Q c)) / Real.log 2 ∧
      ∀ c : ℝ, c ≤ acquired P Q s →
        c * Real.log 2 ≤ totalCost P Q s (fun a => discrimination (P a) (Q a))) ∧
    (acquired bscP bscQ b ≤ totalCost bscP bscQ b kappa ∧
      totalCost bscP bscQ b kappa ≤ 4 * totalCost bscP bscQ b (fun e => e.1 ^ 2)) ∧
    ((decoderError (productRows m R) (productRows m S)
        (likelihoodDecoder (productRows m R) (productRows m S)) ≤ (∏ i, BC (R i) (S i)) / 2 ∧
      (∏ i, BC (R i) (S i)) / 2 ≤ Real.exp (-(∑ i, discrimination (R i) (S i)) / 4) / 2) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
        4 * Real.log (1 / (2 * η)) ≤ ∑ i, discrimination (R i) (S i) →
        1 - hb η ≤ information (1 / 2) (productRows m R) (productRows m S)) ∧
    ((M : ℝ) * (mean ε) ^ 2 ≤ ∑ i, ε i ^ 2 ∧
      ((M : ℝ) * (mean ε) ^ 2 = ∑ i, ε i ^ 2 ↔ ∃ c : ℝ, ∀ i, ε i = c)) := by
  exact ⟨⟨discrimination_sum P Q s, fun c hc => discrimination_target P Q s c hc⟩,
    adaptive_biases b,
    ⟨independent_error m R S, fun η hη hhalf hD => independent_information m R S hη hhalf hD⟩,
    sum_mean hM ε⟩

end

end OperatorKO7.Meta.LiteratureReview
