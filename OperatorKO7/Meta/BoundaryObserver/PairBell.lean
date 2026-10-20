import OperatorKO7.Meta.BoundaryObserver.PairQubit
import OperatorKO7.Meta.BoundaryObserver.FourTestTables
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

set_option autoImplicit false

/-!
# Pair Bell correlations

The module states the Bell correlation table of two pairs at angle π/4, the CHSH score attained
by the pure Schmidt states, and the mixed-state score bound from anticommuting tests.
`PureExcessGoal` is proved below by `pureExcess` and `MixedExcessGoal` by `mixedExcess`.
The two-sided mixed-state bound on the absolute score is `PairPurification.mixedExcess_abs`;
it applies `mixedExcess` to both signs of the first-party tests.
-/

namespace OperatorKO7.Meta.BoundaryObserver.PairBell

open scoped BigOperators Kronecker ComplexOrder
open OperatorKO7.Meta.BoundaryObserver
open OperatorKO7.Meta.BoundaryObserver.PairQubit

noncomputable section

/-- Alice's two tests: the label test and the transposition. -/
def aliceTest (x : Bool) : Matrix Bool Bool ℂ := if x then pairX else pairZ

/-- Bob's two tests at the angle θ from the label test. -/
def bobTest (θ : ℝ) (y : Bool) : Matrix Bool Bool ℂ :=
  (Real.cos θ : ℂ) • pairZ + ((if y then -Real.sin θ else Real.sin θ : ℝ) : ℂ) • pairX

/-- The correlation of Alice's test x and Bob's test y in a joint state. -/
def stateCorrelation (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ) (θ : ℝ) (x y : Bool) : ℝ :=
  (ρ * (aliceTest x ⊗ₖ bobTest θ y)).trace.re

/-- The score: three correlations added and the fourth subtracted. -/
def chshScore (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ) (θ : ℝ) : ℝ :=
  stateCorrelation ρ θ false false + stateCorrelation ρ θ false true +
    stateCorrelation ρ θ true false - stateCorrelation ρ θ true true

/-- At angle π/4, the correlation table of the Bell state equals the extreme four-test table. -/
def BellTableGoal : Prop :=
  ∀ x y : Bool, stateCorrelation bellState (Real.pi / 4) x y =
    FourTestTables.corr FourTestTables.extremeTable x y

/-- The pure state cos α |00⟩ + sin α |11⟩ of two pairs. -/
def schmidtState (α : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x y => if x.1 = x.2 ∧ y.1 = y.2 then
    (((if x.1 then Real.sin α else Real.cos α) * (if y.1 then Real.sin α else Real.cos α) : ℝ) : ℂ)
  else 0

/-- For every Schmidt angle α, some test angle gives the CHSH score `2 * √(2 - cos (2α) ^ 2)`,
and the local Bloch vector of the first pair is `(0, 0, cos (2α))`. -/
def PureExcessGoal : Prop :=
  ∀ α : ℝ, ∃ θ : ℝ,
    chshScore (schmidtState α) θ = 2 * Real.sqrt (2 - Real.cos (2 * α) ^ 2) ∧
    (BoundaryReconstruction.Thermal.marginalLeft (schmidtState α) * pairZ).trace.re =
      Real.cos (2 * α) ∧
    (BoundaryReconstruction.Thermal.marginalLeft (schmidtState α) * pairX).trace.re = 0 ∧
    (BoundaryReconstruction.Thermal.marginalLeft (schmidtState α) * pairY).trace.re = 0

/-- Squared local Bloch length of the first pair. -/
def localBlochSq (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ) : ℝ :=
  (BoundaryReconstruction.Thermal.marginalLeft ρ * pairX).trace.re ^ 2 +
    (BoundaryReconstruction.Thermal.marginalLeft ρ * pairY).trace.re ^ 2 +
    (BoundaryReconstruction.Thermal.marginalLeft ρ * pairZ).trace.re ^ 2

/-- A test with plus and minus one values. -/
def SignTest (a : Matrix Bool Bool ℂ) : Prop := a.IsHermitian ∧ a * a = 1

/-- For every positive semidefinite trace-one state of two pairs and every four sign tests, the
CHSH score is at most twice the square root of two minus the squared local Bloch length of the
first pair. -/
def MixedExcessGoal : Prop :=
  ∀ ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ, ρ.PosSemidef → ρ.trace = 1 →
    ∀ a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ, SignTest a₀ → SignTest a₁ → SignTest b₀ → SignTest b₁ →
      (ρ * (a₀ ⊗ₖ b₀ + a₀ ⊗ₖ b₁ + a₁ ⊗ₖ b₀ - a₁ ⊗ₖ b₁)).trace.re ≤
        2 * Real.sqrt (2 - localBlochSq ρ)

/-- Exact Bell-state trace contraction with arbitrary local matrices. -/
private theorem bell_tensor_trace (a b : Matrix Bool Bool ℂ) :
    (bellState * (a ⊗ₖ b)).trace =
      (1 / 2 : ℂ) * (a false false * b false false + a true true * b true true +
        a false true * b false true + a true false * b true false) := by
  simp [bellState, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  ring

private theorem aliceTest_false : aliceTest false = pairZ := rfl
private theorem aliceTest_true : aliceTest true = pairX := rfl

private theorem bobTest_false_apply (θ : ℝ) (i j : Bool) :
    bobTest θ false i j = (Real.cos θ : ℂ) * pairZ i j + (Real.sin θ : ℂ) * pairX i j := rfl

private theorem bobTest_true_apply (θ : ℝ) (i j : Bool) :
    bobTest θ true i j = (Real.cos θ : ℂ) * pairZ i j + ((-Real.sin θ : ℝ) : ℂ) * pairX i j :=
  rfl

private theorem pairZ_ff : pairZ false false = 1 := by simp [pairZ]
private theorem pairZ_ft : pairZ false true = 0 := by simp [pairZ]
private theorem pairZ_tf : pairZ true false = 0 := by simp [pairZ]
private theorem pairZ_tt : pairZ true true = -1 := by simp [pairZ]
private theorem pairX_ff : pairX false false = 0 := by simp [pairX]
private theorem pairX_ft : pairX false true = 1 := by simp [pairX]
private theorem pairX_tf : pairX true false = 1 := by simp [pairX]
private theorem pairX_tt : pairX true true = 0 := by simp [pairX]

/-- The four correlations are cos θ, cos θ, sin θ and negative sin θ. -/
private theorem bell_corr (θ : ℝ) (x y : Bool) :
    stateCorrelation bellState θ x y =
      if x then (if y then -Real.sin θ else Real.sin θ) else Real.cos θ := by
  unfold stateCorrelation
  cases x <;> cases y
  · have key : (bellState * (pairZ ⊗ₖ bobTest θ false)).trace = ((Real.cos θ : ℝ) : ℂ) := by
      rw [bell_tensor_trace]
      simp only [bobTest_false_apply, pairZ_ff, pairZ_ft, pairZ_tf, pairZ_tt,
        pairX_ff, pairX_ft, pairX_tf, pairX_tt]
      ring
    show (bellState * (pairZ ⊗ₖ bobTest θ false)).trace.re = Real.cos θ
    rw [key, Complex.ofReal_re]
  · have key : (bellState * (pairZ ⊗ₖ bobTest θ true)).trace = ((Real.cos θ : ℝ) : ℂ) := by
      rw [bell_tensor_trace]
      simp only [bobTest_true_apply, pairZ_ff, pairZ_ft, pairZ_tf, pairZ_tt,
        pairX_ff, pairX_ft, pairX_tf, pairX_tt]
      ring
    show (bellState * (pairZ ⊗ₖ bobTest θ true)).trace.re = Real.cos θ
    rw [key, Complex.ofReal_re]
  · have key : (bellState * (pairX ⊗ₖ bobTest θ false)).trace = ((Real.sin θ : ℝ) : ℂ) := by
      rw [bell_tensor_trace]
      simp only [bobTest_false_apply, pairZ_ff, pairZ_ft, pairZ_tf, pairZ_tt,
        pairX_ff, pairX_ft, pairX_tf, pairX_tt]
      ring
    show (bellState * (pairX ⊗ₖ bobTest θ false)).trace.re = Real.sin θ
    rw [key, Complex.ofReal_re]
  · have key : (bellState * (pairX ⊗ₖ bobTest θ true)).trace = ((-Real.sin θ : ℝ) : ℂ) := by
      rw [bell_tensor_trace]
      simp only [bobTest_true_apply, pairZ_ff, pairZ_ft, pairZ_tf, pairZ_tt,
        pairX_ff, pairX_ft, pairX_tf, pairX_tt]
      ring
    show (bellState * (pairX ⊗ₖ bobTest θ true)).trace.re = -Real.sin θ
    rw [key, Complex.ofReal_re]

/-- The four-entry Bell table of `BellTableGoal`. -/
theorem bellTable : BellTableGoal := by
  intro x y
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  cases x <;> cases y <;>
    simp [bell_corr, FourTestTables.corr, FourTestTables.extremeTable,
      Real.cos_pi_div_four, Real.sin_pi_div_four] <;>
    field_simp [hs] <;>
    nlinarith


/-! ## Pure Schmidt-state attainment. -/

/-- Contract the Schmidt rank-one state against arbitrary product tests. -/
private theorem schmidt_tensor_trace (α : ℝ) (a b : Matrix Bool Bool ℂ) :
    (schmidtState α * (a ⊗ₖ b)).trace =
      (Real.cos α : ℂ) ^ 2 * (a false false * b false false) +
      (Real.sin α : ℂ) ^ 2 * (a true true * b true true) +
      ((Real.cos α : ℂ) * (Real.sin α : ℂ)) *
        (a false true * b false true + a true false * b true false) := by
  simp [schmidtState, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  ring

/-- All four Schmidt correlations, with no sign restriction on sin(2α). -/
private theorem schmidt_corr (α θ : ℝ) (x y : Bool) :
    stateCorrelation (schmidtState α) θ x y =
      if x then
        (if y then -(Real.sin θ * Real.sin (2 * α))
         else Real.sin θ * Real.sin (2 * α))
      else Real.cos θ := by
  have hunit : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq α
  have hdouble : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := Real.sin_two_mul α
  have hunitC : ((Real.sin α : ℝ) : ℂ) ^ 2 + ((Real.cos α : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast hunit
  unfold stateCorrelation
  cases x <;> cases y
  · have key : (schmidtState α * (pairZ ⊗ₖ bobTest θ false)).trace =
        ((Real.cos θ : ℝ) : ℂ) := by
      rw [schmidt_tensor_trace]
      simp only [bobTest_false_apply, pairZ_ff, pairZ_ft, pairZ_tf, pairZ_tt,
        pairX_ff, pairX_ft, pairX_tf, pairX_tt]
      linear_combination ((Real.cos θ : ℝ) : ℂ) * hunitC
    show (schmidtState α * (pairZ ⊗ₖ bobTest θ false)).trace.re = Real.cos θ
    rw [key, Complex.ofReal_re]
  · have key : (schmidtState α * (pairZ ⊗ₖ bobTest θ true)).trace =
        ((Real.cos θ : ℝ) : ℂ) := by
      rw [schmidt_tensor_trace]
      simp only [bobTest_true_apply, pairZ_ff, pairZ_ft, pairZ_tf, pairZ_tt,
        pairX_ff, pairX_ft, pairX_tf, pairX_tt]
      linear_combination ((Real.cos θ : ℝ) : ℂ) * hunitC
    show (schmidtState α * (pairZ ⊗ₖ bobTest θ true)).trace.re = Real.cos θ
    rw [key, Complex.ofReal_re]
  · have key : (schmidtState α * (pairX ⊗ₖ bobTest θ false)).trace =
        ((Real.sin θ * Real.sin (2 * α) : ℝ) : ℂ) := by
      rw [schmidt_tensor_trace, hdouble]
      simp only [bobTest_false_apply, pairZ_ff, pairZ_ft, pairZ_tf, pairZ_tt,
        pairX_ff, pairX_ft, pairX_tf, pairX_tt]
      push_cast
      ring
    show (schmidtState α * (pairX ⊗ₖ bobTest θ false)).trace.re =
      Real.sin θ * Real.sin (2 * α)
    rw [key, Complex.ofReal_re]
  · have key : (schmidtState α * (pairX ⊗ₖ bobTest θ true)).trace =
        ((-(Real.sin θ * Real.sin (2 * α)) : ℝ) : ℂ) := by
      rw [schmidt_tensor_trace, hdouble]
      simp only [bobTest_true_apply, pairZ_ff, pairZ_ft, pairZ_tf, pairZ_tt,
        pairX_ff, pairX_ft, pairX_tf, pairX_tt]
      push_cast
      ring
    show (schmidtState α * (pairX ⊗ₖ bobTest θ true)).trace.re =
      -(Real.sin θ * Real.sin (2 * α))
    rw [key, Complex.ofReal_re]

private theorem schmidt_chsh (α θ : ℝ) :
    chshScore (schmidtState α) θ =
      2 * (Real.cos θ + Real.sin θ * Real.sin (2 * α)) := by
  simp [chshScore, schmidt_corr]
  ring

/-- The Schmidt marginal is diagonal in the place basis. -/
private theorem schmidt_left_marginal (α : ℝ) :
    BoundaryReconstruction.Thermal.marginalLeft (schmidtState α) =
      Matrix.diagonal (fun b : Bool =>
        if b then ((Real.sin α ^ 2 : ℝ) : ℂ)
        else ((Real.cos α ^ 2 : ℝ) : ℂ)) := by
  ext i j
  cases i <;> cases j <;>
    (simp [BoundaryReconstruction.Thermal.marginalLeft, schmidtState] <;>
      ring)

/-- The actual marginal supplies all three exact Bloch-vector coordinates. -/
private theorem schmidt_local_bloch (α : ℝ) :
    (BoundaryReconstruction.Thermal.marginalLeft (schmidtState α) * pairZ).trace.re =
      Real.cos (2 * α) ∧
    (BoundaryReconstruction.Thermal.marginalLeft (schmidtState α) * pairX).trace.re = 0 ∧
    (BoundaryReconstruction.Thermal.marginalLeft (schmidtState α) * pairY).trace.re = 0 := by
  have hz :
      (BoundaryReconstruction.Thermal.marginalLeft (schmidtState α) * pairZ).trace.re =
        Real.cos α ^ 2 - Real.sin α ^ 2 := by
    rw [schmidt_left_marginal]
    simp [pairZ, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]
    simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_pow,
      Complex.ofReal_re]
    ring
  have hx :
      (BoundaryReconstruction.Thermal.marginalLeft (schmidtState α) * pairX).trace.re = 0 := by
    rw [schmidt_left_marginal]
    simp [pairX, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]
  have hy :
      (BoundaryReconstruction.Thermal.marginalLeft (schmidtState α) * pairY).trace.re = 0 := by
    rw [schmidt_left_marginal]
    simp [pairY, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]
  refine ⟨?_, hx, hy⟩
  rw [hz, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq α]

/-- The exact global optimum is attained for every real α, including negative sin(2α). -/
theorem pureExcess : PureExcessGoal := by
  intro α
  let s : ℝ := Real.sin (2 * α)
  let d : ℝ := Real.sqrt (1 + s ^ 2)
  have hbase : 0 < 1 + s ^ 2 := by nlinarith [sq_nonneg s]
  have hdpos : 0 < d := Real.sqrt_pos.mpr hbase
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hdsq : d ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (le_of_lt hbase)
  have htrig : 2 - Real.cos (2 * α) ^ 2 = d ^ 2 := by
    rw [hdsq]
    dsimp [s]
    nlinarith [Real.sin_sq_add_cos_sq (2 * α)]
  have hroot : Real.sqrt (2 - Real.cos (2 * α) ^ 2) = d := by
    rw [htrig, Real.sqrt_sq (le_of_lt hdpos)]
  refine ⟨Real.arctan s, ?_, ?_⟩
  · rw [schmidt_chsh]
    change 2 * (Real.cos (Real.arctan s) +
      Real.sin (Real.arctan s) * s) =
        2 * Real.sqrt (2 - Real.cos (2 * α) ^ 2)
    rw [Real.cos_arctan, Real.sin_arctan, hroot]
    change 2 * (1 / d + s / d * s) = 2 * d
    field_simp [hdne]
    nlinarith [hdsq]
  · exact schmidt_local_bloch α

/-! ## The mixed-state bound from anticommuting tests -/

open scoped Matrix

/-- The trace of a positive semidefinite matrix has nonnegative real part. -/
private theorem psd_trace_re_nonneg {m : Type} [Fintype m] [DecidableEq m] {M : Matrix m m ℂ}
    (hM : M.PosSemidef) : 0 ≤ M.trace.re := by
  rw [Matrix.trace, Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  have h := hM.re_dotProduct_nonneg (Pi.single i 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

/-- A joint state gives a nonnegative mean to every operator of the form Mᴴ M. -/
private theorem mean_conj_nonneg {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hρ : ρ.PosSemidef) (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    0 ≤ (ρ * (Mᴴ * M)).trace.re := by
  have hcyc : (ρ * (Mᴴ * M)).trace = (M * ρ * Mᴴ).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (ρ * Mᴴ) M, Matrix.mul_assoc]
  rw [hcyc]
  exact psd_trace_re_nonneg (hρ.mul_mul_conjTranspose_same M)

/-- The mean of a sum is the sum of the means. -/
private theorem mean_add (ρ X Y : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    (ρ * (X + Y)).trace.re = (ρ * X).trace.re + (ρ * Y).trace.re := by
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

/-- The mean of a real multiple is the real multiple of the mean. -/
private theorem mean_smul (ρ X : Matrix (Bool × Bool) (Bool × Bool) ℂ) (t : ℝ) :
    (ρ * ((t : ℂ) • X)).trace.re = t * (ρ * X).trace.re := by
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- A Hermitian test with square k times the identity has squared mean at most k. -/
private theorem mean_sq_le {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) {Z : Matrix (Bool × Bool) (Bool × Bool) ℂ} (hZ : Zᴴ = Z) {k : ℝ}
    (hk : Z * Z = (k : ℂ) • 1) : (ρ * Z).trace.re ^ 2 ≤ k := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (ρ * Z).trace.re := ⟨_, rfl⟩
  have hMH : (Z + ((-t : ℝ) : ℂ) • 1)ᴴ = Z + ((-t : ℝ) : ℂ) • 1 := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      hZ, Complex.star_def, Complex.conj_ofReal]
  have hsq : (Z + ((-t : ℝ) : ℂ) • 1)ᴴ * (Z + ((-t : ℝ) : ℂ) • 1) =
      ((k + t ^ 2 : ℝ) : ℂ) • 1 + ((-2 * t : ℝ) : ℂ) • Z := by
    rw [hMH]
    simp only [add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, hk, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hpos := mean_conj_nonneg hρ (Z + ((-t : ℝ) : ℂ) • 1)
  rw [hsq, mean_add, mean_smul, mean_smul, Matrix.mul_one, htr, Complex.one_re, ← ht] at hpos
  rw [← ht]
  nlinarith [hpos]

/-- Two anticommuting Hermitian tests with scalar squares obey a weighted mean bound. -/
private theorem mean_pair_le {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) {Y₁ Y₂ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (h₁ : Y₁ᴴ = Y₁) (h₂ : Y₂ᴴ = Y₂) {k₁ k₂ : ℝ} (hk₁ : Y₁ * Y₁ = (k₁ : ℂ) • 1)
    (hk₂ : Y₂ * Y₂ = (k₂ : ℂ) • 1) (hac : Y₁ * Y₂ + Y₂ * Y₁ = 0) (t₁ t₂ : ℝ) :
    (t₁ * (ρ * Y₁).trace.re + t₂ * (ρ * Y₂).trace.re) ^ 2 ≤ t₁ ^ 2 * k₁ + t₂ ^ 2 * k₂ := by
  have hH : ((t₁ : ℂ) • Y₁ + (t₂ : ℂ) • Y₂)ᴴ = (t₁ : ℂ) • Y₁ + (t₂ : ℂ) • Y₂ := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, h₁, h₂, Complex.star_def,
      Complex.conj_ofReal]
  have h21 : Y₂ * Y₁ = -(Y₁ * Y₂) := eq_neg_of_add_eq_zero_right hac
  have hsq : ((t₁ : ℂ) • Y₁ + (t₂ : ℂ) • Y₂) * ((t₁ : ℂ) • Y₁ + (t₂ : ℂ) • Y₂) =
      ((t₁ ^ 2 * k₁ + t₂ ^ 2 * k₂ : ℝ) : ℂ) • 1 := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hk₁, hk₂, h21]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
    push_cast
    ring
  have h := mean_sq_le hρ htr hH hsq
  rwa [mean_add, mean_smul, mean_smul] at h

/-- The adjoint of a Kronecker product of two pair matrices. -/
private theorem kron_conjTranspose (a b : Matrix Bool Bool ℂ) : (a ⊗ₖ b)ᴴ = aᴴ ⊗ₖ bᴴ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kronecker_apply, StarMul.star_mul]
  exact mul_comm _ _

/-- A sign test of the pair with nonzero trace is plus or minus the identity. -/
private theorem signTest_scalar {a : Matrix Bool Bool ℂ} (ha : SignTest a)
    (htr : a.trace ≠ 0) : a = 1 ∨ a = -1 := by
  have h := ha.2
  have e00 := congrFun (congrFun h false) false
  have e01 := congrFun (congrFun h false) true
  have e10 := congrFun (congrFun h true) false
  have e11 := congrFun (congrFun h true) true
  simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true] at e00 e01 e10 e11
  have hs : a false false + a true true ≠ 0 := by
    intro h0
    apply htr
    rw [Matrix.trace, Fintype.sum_bool]
    simp only [Matrix.diag]
    linear_combination h0
  have h01 : a false true = 0 := by
    have hm : a false true * (a false false + a true true) = 0 := by linear_combination e01
    rcases mul_eq_zero.mp hm with h1 | h1
    · exact h1
    · exact absurd h1 hs
  have h10 : a true false = 0 := by
    have hm : a true false * (a false false + a true true) = 0 := by linear_combination e10
    rcases mul_eq_zero.mp hm with h1 | h1
    · exact h1
    · exact absurd h1 hs
  have hA : (a false false - 1) * (a false false + 1) = 0 := by
    linear_combination e00 - a true false * h01
  have hD : (a true true - 1) * (a true true + 1) = 0 := by
    linear_combination e11 - a false true * h10
  have hx : a false false = 1 ∨ a false false = -1 := by
    rcases mul_eq_zero.mp hA with h1 | h1
    · exact Or.inl (by linear_combination h1)
    · exact Or.inr (by linear_combination h1)
  have hd : a true true = 1 ∨ a true true = -1 := by
    rcases mul_eq_zero.mp hD with h1 | h1
    · exact Or.inl (by linear_combination h1)
    · exact Or.inr (by linear_combination h1)
  rcases hx with hx | hx <;> rcases hd with hd | hd
  · left
    ext i j
    cases i <;> cases j <;> simp [hx, hd, h01, h10]
  · exact absurd (by rw [hx, hd]; ring) hs
  · exact absurd (by rw [hx, hd]; ring) hs
  · right
    ext i j
    cases i <;> cases j <;> simp [hx, hd, h01, h10]

/-- Two traceless pair matrices anticommute up to the trace of their product. -/
private theorem traceless_anticomm {X Y : Matrix Bool Bool ℂ} (hX : X.trace = 0)
    (hY : Y.trace = 0) : X * Y + Y * X = (X * Y).trace • (1 : Matrix Bool Bool ℂ) := by
  have hX' : X true true = -X false false := by
    rw [Matrix.trace, Fintype.sum_bool] at hX
    simp only [Matrix.diag] at hX
    linear_combination hX
  have hY' : Y true true = -Y false false := by
    rw [Matrix.trace, Fintype.sum_bool] at hY
    simp only [Matrix.diag] at hY
    linear_combination hY
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, Matrix.trace, hX', hY'] <;> ring

/-- The trace of a product of two Hermitian pair matrices is real. -/
private theorem herm_trace_real {X Y : Matrix Bool Bool ℂ} (hX : Xᴴ = X) (hY : Yᴴ = Y) :
    (((X * Y).trace.re : ℝ) : ℂ) = (X * Y).trace := by
  rw [← Complex.conj_eq_iff_re, ← Complex.star_def, ← Matrix.trace_conjTranspose,
    Matrix.conjTranspose_mul, hX, hY, Matrix.trace_mul_comm]

/-- A traceless Hermitian pair matrix squares to a real multiple of the identity. -/
private theorem traceless_sq {X : Matrix Bool Bool ℂ} (hX : Xᴴ = X) (h0 : X.trace = 0) :
    X * X = (((X * X).trace.re / 2 : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  have h := traceless_anticomm h0 h0
  rw [← herm_trace_real hX hX] at h
  ext i j
  have e := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at e ⊢
  push_cast
  linear_combination e / 2

/-- Twice the first-pair marginal minus the identity: the local Bloch matrix of the first pair. -/
private def localBlochMatrix (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ) : Matrix Bool Bool ℂ :=
  (2 : ℂ) • BoundaryReconstruction.Thermal.marginalLeft ρ - 1

private theorem localBlochMatrix_herm {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hρ : ρ.PosSemidef) : (localBlochMatrix ρ)ᴴ = localBlochMatrix ρ := by
  have hA := (BoundaryReconstruction.Thermal.marginalLeft_posSemidef hρ).1.eq
  rw [localBlochMatrix, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hA]
  simp

private theorem localBlochMatrix_trace {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (htr : ρ.trace = 1) : (localBlochMatrix ρ).trace = 0 := by
  rw [localBlochMatrix, Matrix.trace_sub, Matrix.trace_smul,
    BoundaryReconstruction.Thermal.marginalLeft_trace, htr, Matrix.trace_one]
  norm_num

/-- The mean of a first-pair test is its trace against the first-pair marginal. -/
private theorem trace_kron_one (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (X : Matrix Bool Bool ℂ) :
    (ρ * (X ⊗ₖ (1 : Matrix Bool Bool ℂ))).trace =
      (BoundaryReconstruction.Thermal.marginalLeft ρ * X).trace := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type,
    BoundaryReconstruction.Thermal.marginalLeft]
  ring

/-- Twice the mean of a traceless first-pair test is its trace against the Bloch matrix. -/
private theorem mean_local {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (X : Matrix Bool Bool ℂ) (hX : X.trace = 0) :
    2 * (ρ * (X ⊗ₖ (1 : Matrix Bool Bool ℂ))).trace.re = (localBlochMatrix ρ * X).trace.re := by
  have h : (localBlochMatrix ρ * X).trace =
      2 * (ρ * (X ⊗ₖ (1 : Matrix Bool Bool ℂ))).trace := by
    rw [trace_kron_one, localBlochMatrix, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_sub, Matrix.trace_smul, hX, sub_zero, smul_eq_mul]
  rw [h, Complex.mul_re]
  norm_num

/-- The Bloch matrix squares to the squared local Bloch length times the identity. -/
private theorem localBlochMatrix_sq {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    localBlochMatrix ρ * localBlochMatrix ρ =
      (localBlochSq ρ : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  have hA := BoundaryReconstruction.Thermal.marginalLeft_posSemidef hρ
  have htrA : (BoundaryReconstruction.Thermal.marginalLeft ρ).trace = 1 :=
    (BoundaryReconstruction.Thermal.marginalLeft_trace ρ).trans htr
  have hL : localBlochSq ρ =
      2 * (BoundaryReconstruction.Thermal.marginalLeft ρ *
        BoundaryReconstruction.Thermal.marginalLeft ρ).trace.re - 1 :=
    (PairQubit.bitConservationGoal _ hA htrA).1
  have htrA' : BoundaryReconstruction.Thermal.marginalLeft ρ false false +
      BoundaryReconstruction.Thermal.marginalLeft ρ true true = 1 := by
    rw [Matrix.trace, Fintype.sum_bool] at htrA
    simp only [Matrix.diag] at htrA
    linear_combination htrA
  have hRR : (localBlochMatrix ρ * localBlochMatrix ρ).trace =
      4 * (BoundaryReconstruction.Thermal.marginalLeft ρ *
        BoundaryReconstruction.Thermal.marginalLeft ρ).trace - 2 := by
    simp [localBlochMatrix, Matrix.trace, Matrix.mul_apply, Matrix.one_apply]
    linear_combination (-4 : ℂ) * htrA'
  have hre : (4 * (BoundaryReconstruction.Thermal.marginalLeft ρ *
        BoundaryReconstruction.Thermal.marginalLeft ρ).trace - 2).re / 2 =
      2 * (BoundaryReconstruction.Thermal.marginalLeft ρ *
        BoundaryReconstruction.Thermal.marginalLeft ρ).trace.re - 1 := by
    simp [Complex.mul_re]
    ring
  rw [traceless_sq (localBlochMatrix_herm hρ) (localBlochMatrix_trace htr), hRR, hre, hL]

/-- The mean of the Bloch matrix on the first pair is the squared local Bloch length. -/
private theorem mean_localBloch {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (ρ * (localBlochMatrix ρ ⊗ₖ (1 : Matrix Bool Bool ℂ))).trace.re = localBlochSq ρ := by
  have h := mean_local (ρ := ρ) (localBlochMatrix ρ) (localBlochMatrix_trace htr)
  rw [localBlochMatrix_sq hρ htr, Matrix.trace_smul, Matrix.trace_one] at h
  simp at h
  linarith

/-- The squared local Bloch length of a joint state is at most one. -/
private theorem localBlochSq_le_one {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) : localBlochSq ρ ≤ 1 := by
  obtain ⟨h1, h2⟩ := PairQubit.bitConservationGoal _
    (BoundaryReconstruction.Thermal.marginalLeft_posSemidef hρ)
    ((BoundaryReconstruction.Thermal.marginalLeft_trace ρ).trans htr)
  calc localBlochSq ρ = _ := h1
    _ ≤ 1 := h2

/-- A Kronecker product of Hermitian pair matrices is Hermitian. -/
private theorem kron_herm {a b : Matrix Bool Bool ℂ} (ha : aᴴ = a) (hb : bᴴ = b) :
    (a ⊗ₖ b)ᴴ = a ⊗ₖ b := by
  rw [kron_conjTranspose, ha, hb]

/-- A Kronecker product of a scalar-square matrix and a sign test squares to a scalar. -/
private theorem kron_sq {a b : Matrix Bool Bool ℂ} {k : ℝ} (ha : a * a = (k : ℂ) • 1)
    (hb : b * b = 1) :
    (a ⊗ₖ b) * (a ⊗ₖ b) = (k : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  rw [← Matrix.mul_kronecker_mul, ha, hb, Matrix.smul_kronecker, Matrix.one_kronecker_one]

/-- Anticommuting first-pair factors give anticommuting joint tests. -/
private theorem kron_anticomm {a c b : Matrix Bool Bool ℂ} (h : a * c + c * a = 0) :
    (a ⊗ₖ b) * (c ⊗ₖ (1 : Matrix Bool Bool ℂ)) + (c ⊗ₖ (1 : Matrix Bool Bool ℂ)) * (a ⊗ₖ b) =
      0 := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
    ← Matrix.add_kronecker, h, Matrix.zero_kronecker]

/-- Commuting first-pair tests: the score operator squares to four times the identity. -/
private theorem chsh_comm_core {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) {F G b₀ b₁ : Matrix Bool Bool ℂ} (hF : Fᴴ = F) (hG : Gᴴ = G)
    (hFG : F * G = 0) (hGF : G * F = 0) (h4 : F * F + G * G = ((4 : ℝ) : ℂ) • 1)
    (hb₀ : SignTest b₀) (hb₁ : SignTest b₁) :
    (ρ * (F ⊗ₖ b₀ + G ⊗ₖ b₁)).trace.re ^ 2 ≤ 4 := by
  have hH : (F ⊗ₖ b₀ + G ⊗ₖ b₁)ᴴ = F ⊗ₖ b₀ + G ⊗ₖ b₁ := by
    rw [Matrix.conjTranspose_add, kron_herm hF hb₀.1.eq, kron_herm hG hb₁.1.eq]
  have hsq : (F ⊗ₖ b₀ + G ⊗ₖ b₁) * (F ⊗ₖ b₀ + G ⊗ₖ b₁) =
      ((4 : ℝ) : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
    rw [add_mul, mul_add, mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hFG, hGF, hb₀.2, hb₁.2,
      Matrix.zero_kronecker, Matrix.zero_kronecker, add_zero, zero_add, ← Matrix.add_kronecker,
      h4, Matrix.smul_kronecker, Matrix.one_kronecker_one]
  exact mean_sq_le hρ htr hH hsq

/-- Real combination step: the two pair bounds and Cauchy-Schwarz give the squared score bound. -/
private theorem chsh_arith {p q u L κp κm : ℝ} (hsum : κp + κm = 4) (hL : L ≤ 1)
    (B1 : p ^ 2 ≤ κp) (B3 : q ^ 2 ≤ κm)
    (AC1 : (p * p + 1 * (κp * L - u ^ 2)) ^ 2 ≤ p ^ 2 * κp + 1 ^ 2 * (κp * (κp * L - u ^ 2)))
    (AC2 : (κp * q * q + κm * u * u) ^ 2 ≤ (κp * q) ^ 2 * κm + (κm * u) ^ 2 * κp) :
    (p + q) ^ 2 ≤ 4 * (2 - L) := by
  have hp0 : 0 ≤ κp := le_trans (sq_nonneg p) B1
  have hm0 : 0 ≤ κm := le_trans (sq_nonneg q) B3
  rcases eq_or_lt_of_le hp0 with hp | hp
  · have hp2 : p ^ 2 = 0 := le_antisymm (by rw [← hp] at B1; exact B1) (sq_nonneg p)
    have hpz : p = 0 := (pow_eq_zero_iff two_ne_zero).mp hp2
    rw [hpz]
    nlinarith
  rcases eq_or_lt_of_le hm0 with hm | hm
  · have hq2 : q ^ 2 = 0 := le_antisymm (by rw [← hm] at B3; exact B3) (sq_nonneg q)
    have hqz : q = 0 := (pow_eq_zero_iff two_ne_zero).mp hq2
    rw [hqz]
    nlinarith
  have hK : 0 < κp * κm := mul_pos hp hm
  have X1 : p ^ 2 + (κp * L - u ^ 2) ≤ κp := by
    nlinarith [AC1, hp]
  have X2 : κp * q ^ 2 + κm * u ^ 2 ≤ κp * κm := by
    nlinarith [AC2, hK]
  have H1 : κm * (p ^ 2 + (κp * L - u ^ 2)) ≤ κm * κp := mul_le_mul_of_nonneg_left X1 hm0
  have hm' : κm = 4 - κp := by linarith
  have key : κp * κm * (p + q) ^ 2 ≤ κp * κm * (4 * (2 - L)) := by
    rw [hm'] at H1 X2 ⊢
    nlinarith [sq_nonneg ((4 - κp) * p - κp * q), H1, X2]
  exact le_of_mul_le_mul_left key hK

/-- Traceless first-pair tests: the squared score is at most four times two minus the squared
local Bloch length. -/
private theorem chsh_core {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) {F G b₀ b₁ : Matrix Bool Bool ℂ} (hF : Fᴴ = F) (hG : Gᴴ = G)
    (tF : F.trace = 0) {κp κm : ℝ} (hFF : F * F = (κp : ℂ) • 1)
    (hGG : G * G = (κm : ℂ) • 1) (hsum : κp + κm = 4) (hFG : F * G + G * F = 0)
    (hb₀ : SignTest b₀) (hb₁ : SignTest b₁) :
    (ρ * (F ⊗ₖ b₀ + G ⊗ₖ b₁)).trace.re ^ 2 ≤ 4 * (2 - localBlochSq ρ) := by
  have hRH := localBlochMatrix_herm hρ
  have hRt := localBlochMatrix_trace htr
  have hRR := localBlochMatrix_sq hρ htr
  have hRm := mean_localBloch hρ htr
  have hL1 := localBlochSq_le_one hρ htr
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (ρ * (F ⊗ₖ (1 : Matrix Bool Bool ℂ))).trace.re := ⟨_, rfl⟩
  have hRFtr : (localBlochMatrix ρ * F).trace = ((2 * u : ℝ) : ℂ) := by
    rw [← herm_trace_real hRH hF, ← mean_local (ρ := ρ) F tF, ← hu]
  have hRF : localBlochMatrix ρ * F + F * localBlochMatrix ρ = ((2 * u : ℝ) : ℂ) • 1 := by
    rw [traceless_anticomm hRt tF, hRFtr]
  have hFR : F * localBlochMatrix ρ = ((2 * u : ℝ) : ℂ) • 1 - localBlochMatrix ρ * F :=
    eq_sub_of_add_eq' hRF
  obtain ⟨Rp, hRp⟩ : ∃ Rp : Matrix Bool Bool ℂ,
      Rp = (κp : ℂ) • localBlochMatrix ρ + ((-u : ℝ) : ℂ) • F := ⟨_, rfl⟩
  have hRpH : Rpᴴ = Rp := by
    rw [hRp]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hRH, hF, Complex.star_def,
      Complex.conj_ofReal]
  have hRpsq : Rp * Rp = ((κp * (κp * localBlochSq ρ - u ^ 2) : ℝ) : ℂ) • 1 := by
    rw [hRp]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hRR, hFF, hFR]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hFRp : F * Rp + Rp * F = 0 := by
    rw [hRp]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, hFF, hFR]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply,
      smul_eq_mul]
    push_cast
    ring
  have hY1H := kron_herm hF hb₀.1.eq
  have hY1sq := kron_sq hFF hb₀.2
  have hY2H : (Rp ⊗ₖ (1 : Matrix Bool Bool ℂ))ᴴ = Rp ⊗ₖ (1 : Matrix Bool Bool ℂ) :=
    kron_herm hRpH Matrix.conjTranspose_one
  have hY2sq := kron_sq hRpsq (Matrix.mul_one (1 : Matrix Bool Bool ℂ))
  have hY12 := kron_anticomm (b := b₀) hFRp
  have hY2m : (ρ * (Rp ⊗ₖ (1 : Matrix Bool Bool ℂ))).trace.re =
      κp * localBlochSq ρ - u ^ 2 := by
    rw [hRp, Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.smul_kronecker, mean_add,
      mean_smul, mean_smul, hRm, ← hu]
    ring
  have AC1 := mean_pair_le hρ htr hY1H hY2H hY1sq hY2sq hY12 ((ρ * (F ⊗ₖ b₀)).trace.re) 1
  rw [hY2m] at AC1
  have hY3H := kron_herm hG hb₁.1.eq
  have hY3sq := kron_sq hGG hb₁.2
  have hY4H : (F ⊗ₖ (1 : Matrix Bool Bool ℂ))ᴴ = F ⊗ₖ (1 : Matrix Bool Bool ℂ) :=
    kron_herm hF Matrix.conjTranspose_one
  have hY4sq := kron_sq hFF (Matrix.mul_one (1 : Matrix Bool Bool ℂ))
  have hGF : G * F + F * G = 0 := by
    rw [add_comm]
    exact hFG
  have hY34 := kron_anticomm (b := b₁) hGF
  have AC2 := mean_pair_le hρ htr hY3H hY4H hY3sq hY4sq hY34
    (κp * (ρ * (G ⊗ₖ b₁)).trace.re) (κm * u)
  rw [← hu] at AC2
  have B1 := mean_sq_le hρ htr hY1H hY1sq
  have B3 := mean_sq_le hρ htr hY3H hY3sq
  rw [mean_add]
  exact chsh_arith hsum hL1 B1 B3 AC1 AC2

/-- Every positive semidefinite trace-one state of two pairs and every four
sign tests give a score at most twice the square root of two minus the squared local Bloch
length of the first pair. Traceless first-pair tests use two anticommuting pairs of joint tests;
a scalar first-pair test commutes with the other one and gives the score bound two. -/
theorem mixedExcess : MixedExcessGoal := by
  intro ρ hρ htr a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
  have hsplit : a₀ ⊗ₖ b₀ + a₀ ⊗ₖ b₁ + a₁ ⊗ₖ b₀ - a₁ ⊗ₖ b₁ =
      (a₀ + a₁) ⊗ₖ b₀ + (a₀ - a₁) ⊗ₖ b₁ := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.kronecker_apply]
    ring
  rw [hsplit]
  have hF : (a₀ + a₁)ᴴ = a₀ + a₁ := by
    rw [Matrix.conjTranspose_add, ha₀.1.eq, ha₁.1.eq]
  have hG : (a₀ - a₁)ᴴ = a₀ - a₁ := by
    rw [Matrix.conjTranspose_sub, ha₀.1.eq, ha₁.1.eq]
  have h4 : (a₀ + a₁) * (a₀ + a₁) + (a₀ - a₁) * (a₀ - a₁) =
      ((4 : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ) := by
    have e : (a₀ + a₁) * (a₀ + a₁) + (a₀ - a₁) * (a₀ - a₁) =
        a₀ * a₀ + a₀ * a₀ + (a₁ * a₁ + a₁ * a₁) := by
      noncomm_ring
    rw [e, ha₀.2, ha₁.2]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hsq : (ρ * ((a₀ + a₁) ⊗ₖ b₀ + (a₀ - a₁) ⊗ₖ b₁)).trace.re ^ 2 ≤
      4 * (2 - localBlochSq ρ) := by
    by_cases ht : a₀.trace = 0 ∧ a₁.trace = 0
    · obtain ⟨t₀, t₁⟩ := ht
      have tF : (a₀ + a₁).trace = 0 := by
        rw [Matrix.trace_add, t₀, t₁, add_zero]
      have tG : (a₀ - a₁).trace = 0 := by
        rw [Matrix.trace_sub, t₀, t₁, sub_zero]
      have hFF := traceless_sq hF tF
      have hGG := traceless_sq hG tG
      have hsum : ((a₀ + a₁) * (a₀ + a₁)).trace.re / 2 +
          ((a₀ - a₁) * (a₀ - a₁)).trace.re / 2 = 4 := by
        have h4' := h4
        rw [hFF, hGG] at h4'
        have e := congrFun (congrFun h4' false) false
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
          mul_one] at e
        exact_mod_cast e
      have hFG : (a₀ + a₁) * (a₀ - a₁) + (a₀ - a₁) * (a₀ + a₁) = 0 := by
        have e : (a₀ + a₁) * (a₀ - a₁) + (a₀ - a₁) * (a₀ + a₁) =
            a₀ * a₀ + a₀ * a₀ - (a₁ * a₁ + a₁ * a₁) := by
          noncomm_ring
        rw [e, ha₀.2, ha₁.2, sub_self]
      exact chsh_core hρ htr hF hG tF hFF hGG hsum hFG hb₀ hb₁
    · have hcomm : a₀ * a₁ = a₁ * a₀ := by
        rcases not_and_or.mp ht with h | h
        · rcases signTest_scalar ha₀ h with e | e <;> rw [e] <;> simp
        · rcases signTest_scalar ha₁ h with e | e <;> rw [e] <;> simp
      have hFG0 : (a₀ + a₁) * (a₀ - a₁) = 0 := by
        have e : (a₀ + a₁) * (a₀ - a₁) = a₀ * a₀ - a₁ * a₁ + (a₁ * a₀ - a₀ * a₁) := by
          noncomm_ring
        rw [e, ha₀.2, ha₁.2, hcomm, sub_self, sub_self, add_zero]
      have hGF0 : (a₀ - a₁) * (a₀ + a₁) = 0 := by
        have e : (a₀ - a₁) * (a₀ + a₁) = a₀ * a₀ - a₁ * a₁ + (a₀ * a₁ - a₁ * a₀) := by
          noncomm_ring
        rw [e, ha₀.2, ha₁.2, hcomm, sub_self, sub_self, add_zero]
      have h2 := chsh_comm_core hρ htr hF hG hFG0 hGF0 h4 hb₀ hb₁
      have hL := localBlochSq_le_one hρ htr
      linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (ρ * ((a₀ + a₁) ⊗ₖ b₀ + (a₀ - a₁) ⊗ₖ b₁)).trace.re :=
    ⟨_, rfl⟩
  rw [← hs] at hsq ⊢
  have h2 : (s / 2) ^ 2 ≤ 2 - localBlochSq ρ := by
    nlinarith [hsq]
  have h3 := Real.abs_le_sqrt h2
  have h5 := le_abs_self (s / 2)
  linarith

end
end OperatorKO7.Meta.BoundaryObserver.PairBell
