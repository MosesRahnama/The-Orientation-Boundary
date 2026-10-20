import OperatorKO7.Meta.UUET.FiniteAmplitudeEntanglement
import OperatorKO7.Meta.UUET.Quantum.TwoQubitEntanglement
import OperatorKO7.Meta.BoundaryObserver.PairBell
import OperatorKO7.Meta.UUET.Quantum.DensityMatrix
import OperatorKO7.Meta.UUET.Quantum.EntanglingChannel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

set_option autoImplicit false

/-!
# Purification of a two-branch law

The amplitude uses the existing two-qubit carrier and product-state predicate.
-/

namespace OperatorKO7.Meta.BoundaryObserver.PairPurification

open OperatorKO7.Meta.UUET
open OperatorKO7.Meta.UUET.Quantum
open scoped BigOperators Matrix Kronecker ComplexOrder

noncomputable section

/-- The diagonal amplitude with entries sqrt p and sqrt q. -/
def schmidtAmp (w : TwoBranchWeight) : TwoQubitAmplitude :=
  fun i j => if i = j then
    ((if i = 0 then Real.sqrt w.p else Real.sqrt w.q : ℝ) : ℂ)
  else 0

/-- The amplitude determinant is the square root of the weight product. -/
theorem amplitudeDet_schmidtAmp (w : TwoBranchWeight) :
    amplitudeDet (schmidtAmp w) = (Real.sqrt (amplitudeEntanglement w) : ℂ) := by
  simp [amplitudeDet, schmidtAmp, amplitudeEntanglement, Real.sqrt_mul w.nonneg]

/-- Product factorization holds exactly at a zero weight product. -/
theorem productAmplitude_schmidtAmp_iff (w : TwoBranchWeight) :
    ProductAmplitude (schmidtAmp w) ↔ amplitudeEntanglement w = 0 := by
  rw [productAmplitude_iff_det_zero, amplitudeDet_schmidtAmp]
  constructor
  · intro h
    have hz : Real.sqrt (amplitudeEntanglement w) = 0 := by
      exact_mod_cast h
    have hs := Real.sq_sqrt (amplitudeEntanglement_nonneg w)
    rw [hz] at hs
    nlinarith
  · intro h
    simp [h]

/-- The pure-state predicate holds exactly at positive weight product. -/
theorem quantumEntangled_schmidtAmp_iff (w : TwoBranchWeight) :
    QuantumEntangled (schmidtAmp w) ↔ 0 < amplitudeEntanglement w := by
  rw [QuantumEntangled, productAmplitude_schmidtAmp_iff]
  constructor
  · intro h
    by_contra hpos
    exact h (le_antisymm (le_of_not_gt hpos) (amplitudeEntanglement_nonneg w))
  · intro h
    exact ne_of_gt h

/-- The fair law is entangled; a certain branch is a product state. -/
theorem schmidtAmp_nonvacuous :
    QuantumEntangled (schmidtAmp balancedBranch) ∧
    ProductAmplitude (schmidtAmp collapsedBranch) :=
  ⟨(quantumEntangled_schmidtAmp_iff balancedBranch).2 balancedBranch_pos,
    (productAmplitude_schmidtAmp_iff collapsedBranch).2 collapsedBranch_amplitude⟩

/-! ## Concurrence and the marginal -/

/-- Pure two-qubit concurrence in terms of the existing amplitude determinant. -/
def concurrence (A : TwoQubitAmplitude) : ℝ := 2 * ‖amplitudeDet A‖

theorem concurrence_nonneg (A : TwoQubitAmplitude) : 0 ≤ concurrence A :=
  mul_nonneg (by norm_num) (norm_nonneg _)

/-- Concurrence of the diagonal purification. -/
theorem concurrence_schmidtAmp (w : TwoBranchWeight) :
    concurrence (schmidtAmp w) = 2 * Real.sqrt (amplitudeEntanglement w) := by
  rw [concurrence, amplitudeDet_schmidtAmp,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _)]

theorem concurrence_sq_schmidtAmp (w : TwoBranchWeight) :
    concurrence (schmidtAmp w) ^ 2 = 4 * amplitudeEntanglement w := by
  rw [concurrence_schmidtAmp]
  nlinarith [Real.sq_sqrt (amplitudeEntanglement_nonneg w)]

/-- The local imbalance and concurrence obey the exact complementarity identity. -/
theorem concurrence_complementarity (w : TwoBranchWeight) :
    (w.p - w.q) ^ 2 + concurrence (schmidtAmp w) ^ 2 = 1 := by
  rw [concurrence_sq_schmidtAmp]
  dsimp [amplitudeEntanglement, TwoBranchWeight.q]
  ring

/-- The Schmidt amplitude really has the specified diagonal reduced density. -/
theorem schmidtAmp_marginal (w : TwoBranchWeight) :
    Matrix.of (schmidtAmp w) * (Matrix.of (schmidtAmp w))ᴴ =
      Matrix.diagonal ![(w.p : ℂ), (w.q : ℂ)] := by
  have hp : (Real.sqrt w.p : ℂ) * (Real.sqrt w.p : ℂ) = (w.p : ℂ) := by
    exact_mod_cast (show Real.sqrt w.p * Real.sqrt w.p = w.p by
      nlinarith [Real.sq_sqrt w.nonneg])
  have hq : (Real.sqrt w.q : ℂ) * (Real.sqrt w.q : ℂ) = (w.q : ℂ) := by
    exact_mod_cast (show Real.sqrt w.q * Real.sqrt w.q = w.q by
      nlinarith [Real.sq_sqrt w.q_nonneg])
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
      schmidtAmp, hp, hq]

/-- The determinant of the actual Gram marginal is the squared determinant norm. -/
theorem amplitudeDet_gram (A : TwoQubitAmplitude) :
    Matrix.det (Matrix.of A * (Matrix.of A)ᴴ) = ((‖amplitudeDet A‖ ^ 2 : ℝ) : ℂ) := by
  have hdet : Matrix.det (Matrix.of A) = amplitudeDet A := Matrix.det_fin_two (Matrix.of A)
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, hdet]
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Every purification with the stated marginal has the same concurrence. -/
theorem concurrence_sq_of_marginal (w : TwoBranchWeight) (A : TwoQubitAmplitude)
    (hA : Matrix.of A * (Matrix.of A)ᴴ = Matrix.diagonal ![(w.p : ℂ), (w.q : ℂ)]) :
    concurrence A ^ 2 = 4 * amplitudeEntanglement w := by
  have hdet := congrArg Matrix.det hA
  rw [amplitudeDet_gram] at hdet
  have hd : Matrix.det (Matrix.diagonal ![(w.p : ℂ), (w.q : ℂ)]) =
      (amplitudeEntanglement w : ℂ) := by
    simp [amplitudeEntanglement]
  rw [hd] at hdet
  have hn : ‖amplitudeDet A‖ ^ 2 = amplitudeEntanglement w := by
    exact_mod_cast hdet
  dsimp [concurrence]
  nlinarith [hn]

/-! ## The absolute score on the full sign-test domain. -/

/-- The four-test CHSH operator, with no tracelessness restriction. -/
def chshOperator (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  a₀ ⊗ₖ b₀ + a₀ ⊗ₖ b₁ + a₁ ⊗ₖ b₀ - a₁ ⊗ₖ b₁

/-- The expectation of the actual CHSH operator. -/
def signScore (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ) : ℝ :=
  (ρ * chshOperator a₀ a₁ b₀ b₁).trace.re

/-- Negation preserves every Hermitian involutive sign test, including the identities. -/
theorem signTest_neg {a : Matrix Bool Bool ℂ} (ha : PairBell.SignTest a) :
    PairBell.SignTest (-a) := by
  constructor
  · change (-a)ᴴ = -a
    rw [Matrix.conjTranspose_neg, ha.1.eq]
  · simpa only [neg_mul_neg] using ha.2

theorem chshOperator_negAlice (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ) :
    chshOperator (-a₀) (-a₁) b₀ b₁ = -chshOperator a₀ a₁ b₀ b₁ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [chshOperator, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.kronecker_apply]
  ring

theorem signScore_negAlice (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ) :
    signScore ρ (-a₀) (-a₁) b₀ b₁ = -signScore ρ a₀ a₁ b₀ b₁ := by
  simp only [signScore, chshOperator_negAlice, Matrix.mul_neg, Matrix.trace_neg,
    Complex.neg_re]

/-- The mixed-state bound controls the absolute CHSH score for all sign tests. -/
theorem mixedExcess_abs (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ)
    (ha₀ : PairBell.SignTest a₀) (ha₁ : PairBell.SignTest a₁)
    (hb₀ : PairBell.SignTest b₀) (hb₁ : PairBell.SignTest b₁) :
    |signScore ρ a₀ a₁ b₀ b₁| ≤ 2 * Real.sqrt (2 - PairBell.localBlochSq ρ) := by
  have hupper := PairBell.mixedExcess ρ hρ htr a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
  have hneg := PairBell.mixedExcess ρ hρ htr (-a₀) (-a₁) b₀ b₁
    (signTest_neg ha₀) (signTest_neg ha₁) hb₀ hb₁
  change signScore ρ a₀ a₁ b₀ b₁ ≤ _ at hupper
  change signScore ρ (-a₀) (-a₁) b₀ b₁ ≤ _ at hneg
  rw [signScore_negAlice] at hneg
  exact abs_le.mpr ⟨by linarith, hupper⟩

/-! ## The density and the greatest score over all four sign tests. -/

/-- The basis identification used to connect the existing Fin 2 and Bool modules. -/
def boolFin : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := if i = 0 then false else true
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The actual rank-one density operator of an amplitude, reindexed to the Bell carrier. -/
def amplitudeDensity (A : TwoQubitAmplitude) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  outer (fun x => A (boolFin x.1) (boolFin x.2))

theorem amplitudeDensity_posSemidef (A : TwoQubitAmplitude) :
    (amplitudeDensity A).PosSemidef :=
  outer_positiveSemidefinite _

/-- The source partial trace of the outer product is exactly the amplitude Gram matrix. -/
theorem amplitudeDensity_marginal (A : TwoQubitAmplitude) :
    BoundaryReconstruction.Thermal.marginalLeft (amplitudeDensity A) =
      (Matrix.of A * (Matrix.of A)ᴴ).submatrix boolFin boolFin := by
  ext i j
  cases i <;> cases j <;>
    simp [BoundaryReconstruction.Thermal.marginalLeft, amplitudeDensity, outer_apply,
      Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, boolFin] <;> ring

def schmidtDensity (w : TwoBranchWeight) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  amplitudeDensity (schmidtAmp w)

theorem schmidtDensity_posSemidef (w : TwoBranchWeight) :
    (schmidtDensity w).PosSemidef :=
  amplitudeDensity_posSemidef _

theorem schmidtDensity_marginal (w : TwoBranchWeight) :
    BoundaryReconstruction.Thermal.marginalLeft (schmidtDensity w) =
      Matrix.diagonal (fun b : Bool => if b then (w.q : ℂ) else (w.p : ℂ)) := by
  rw [schmidtDensity, amplitudeDensity_marginal, schmidtAmp_marginal]
  ext i j
  cases i <;> cases j <;> simp [boolFin]

theorem schmidtDensity_trace (w : TwoBranchWeight) : (schmidtDensity w).trace = 1 := by
  rw [← BoundaryReconstruction.Thermal.marginalLeft_trace (schmidtDensity w),
    schmidtDensity_marginal, Matrix.trace_diagonal]
  have hn : (w.p : ℂ) + (w.q : ℂ) = 1 := by exact_mod_cast w.normalized
  simpa [Fintype.sum_bool, add_comm] using hn

/-- The purified pair inhabits the existing density-matrix carrier. -/
def schmidtDensityState (w : TwoBranchWeight) : DensityMatrix (Bool × Bool) where
  matrix := schmidtDensity w
  positive := schmidtDensity_posSemidef w
  trace_one := schmidtDensity_trace w

def schmidtAngle (w : TwoBranchWeight) : ℝ := Real.arccos (Real.sqrt w.p)

theorem cos_schmidtAngle (w : TwoBranchWeight) :
    Real.cos (schmidtAngle w) = Real.sqrt w.p := by
  apply Real.cos_arccos
  · nlinarith [Real.sqrt_nonneg w.p]
  · nlinarith [Real.sqrt_nonneg w.p, Real.sq_sqrt w.nonneg, w.le_one]

theorem sin_schmidtAngle (w : TwoBranchWeight) :
    Real.sin (schmidtAngle w) = Real.sqrt w.q := by
  rw [schmidtAngle, Real.sin_arccos, Real.sq_sqrt w.nonneg]
  rfl

theorem cos_sq_schmidtAngle (w : TwoBranchWeight) :
    Real.cos (schmidtAngle w) ^ 2 = w.p := by
  rw [cos_schmidtAngle, Real.sq_sqrt w.nonneg]

theorem cos_two_schmidtAngle (w : TwoBranchWeight) :
    Real.cos (2 * schmidtAngle w) = w.p - w.q := by
  rw [Real.cos_two_mul, cos_sq_schmidtAngle]
  dsimp [TwoBranchWeight.q]
  ring

/-- The actual density equals the existing analytic Schmidt-state family at the derived angle. -/
theorem schmidtDensity_eq_schmidtState (w : TwoBranchWeight) :
    schmidtDensity w = PairBell.schmidtState (schmidtAngle w) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  cases i <;> cases k <;> cases j <;> cases l <;>
    simp [schmidtDensity, amplitudeDensity, outer_apply, schmidtAmp, boolFin,
      PairBell.schmidtState, cos_schmidtAngle, sin_schmidtAngle]

theorem aliceTest_sign (x : Bool) : PairBell.SignTest (PairBell.aliceTest x) := by
  cases x
  · constructor
    · change PairQubit.pairZᴴ = PairQubit.pairZ
      ext i j
      cases i <;> cases j <;> simp [PairQubit.pairZ, Matrix.conjTranspose_apply]
    · exact PairQubit.pauli_relations.1
  · constructor
    · change PairQubit.pairXᴴ = PairQubit.pairX
      ext i j
      cases i <;> cases j <;> simp [PairQubit.pairX, Matrix.conjTranspose_apply]
    · exact PairQubit.pauli_relations.2.1

theorem bobTest_sign (θ : ℝ) (y : Bool) : PairBell.SignTest (PairBell.bobTest θ y) := by
  have hZ : PairQubit.pairZᴴ = PairQubit.pairZ := (aliceTest_sign false).1.eq
  have hX : PairQubit.pairXᴴ = PairQubit.pairX := (aliceTest_sign true).1.eq
  constructor
  · change (PairBell.bobTest θ y)ᴴ = PairBell.bobTest θ y
    simp only [PairBell.bobTest, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      hZ, hX, Complex.star_def, Complex.conj_ofReal]
  · have hs : Complex.sin (θ : ℂ) ^ 2 + Complex.cos (θ : ℂ) ^ 2 = 1 :=
      Complex.sin_sq_add_cos_sq _
    cases y <;> ext i j <;> cases i <;> cases j <;>
      simp [PairBell.bobTest, PairQubit.pairZ, PairQubit.pairX, Matrix.mul_apply] <;>
      ring_nf <;> linear_combination hs

theorem signScore_aliceBob (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ) (θ : ℝ) :
    signScore ρ (PairBell.aliceTest false) (PairBell.aliceTest true)
      (PairBell.bobTest θ false) (PairBell.bobTest θ true) = PairBell.chshScore ρ θ := by
  simp only [signScore, chshOperator, PairBell.chshScore, PairBell.stateCorrelation,
    Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re]

theorem signTest_one : PairBell.SignTest (1 : Matrix Bool Bool ℂ) := by
  constructor
  · change (1 : Matrix Bool Bool ℂ)ᴴ = 1
    simp
  · simp

theorem signTest_neg_one : PairBell.SignTest (-1 : Matrix Bool Bool ℂ) :=
  signTest_neg signTest_one

/-- Identity settings remain permitted and have score two in every trace-one state. -/
theorem identity_signScore (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ) (htr : ρ.trace = 1) :
    signScore ρ 1 1 1 1 = 2 := by
  simp only [signScore, chshOperator, Matrix.one_kronecker_one, Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_one, Matrix.trace_add, Matrix.trace_sub, htr, Complex.add_re,
    Complex.sub_re, Complex.one_re]
  norm_num

/-- All permitted scores, including choices of plus or minus the identity at any setting. -/
def signScores (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ) : Set ℝ :=
  {s | ∃ a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ,
    PairBell.SignTest a₀ ∧ PairBell.SignTest a₁ ∧
    PairBell.SignTest b₀ ∧ PairBell.SignTest b₁ ∧ signScore ρ a₀ a₁ b₀ b₁ = s}

theorem schmidtDensity_localBlochSq (w : TwoBranchWeight) :
    PairBell.localBlochSq (schmidtDensity w) = (w.p - w.q) ^ 2 := by
  obtain ⟨_, _, hz, hx, hy⟩ := PairBell.pureExcess (schmidtAngle w)
  rw [schmidtDensity_eq_schmidtState]
  simp [PairBell.localBlochSq, hx, hy, hz, cos_two_schmidtAngle]

/-- The stated value is attained and bounds every permitted quadruple of sign tests. -/
theorem schmidt_chsh_isGreatest (w : TwoBranchWeight) :
    IsGreatest (signScores (schmidtDensity w))
      (2 * Real.sqrt (1 + 4 * amplitudeEntanglement w)) := by
  have hrad : 2 - (w.p - w.q) ^ 2 = 1 + 4 * amplitudeEntanglement w := by
    dsimp [amplitudeEntanglement, TwoBranchWeight.q]
    ring
  obtain ⟨θ, hscore, _⟩ := PairBell.pureExcess (schmidtAngle w)
  rw [← schmidtDensity_eq_schmidtState, cos_two_schmidtAngle, hrad] at hscore
  constructor
  · refine ⟨PairBell.aliceTest false, PairBell.aliceTest true,
      PairBell.bobTest θ false, PairBell.bobTest θ true,
      aliceTest_sign false, aliceTest_sign true, bobTest_sign θ false, bobTest_sign θ true, ?_⟩
    rw [signScore_aliceBob]
    exact hscore
  · rintro s ⟨a₀, a₁, b₀, b₁, ha₀, ha₁, hb₀, hb₁, hs⟩
    have hbound := PairBell.mixedExcess (schmidtDensity w)
      (schmidtDensity_posSemidef w) (schmidtDensity_trace w)
      a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
    change signScore (schmidtDensity w) a₀ a₁ b₀ b₁ ≤ _ at hbound
    rw [schmidtDensity_localBlochSq, hrad, hs] at hbound
    exact hbound

theorem schmidt_chsh_isGreatest_concurrence (w : TwoBranchWeight) :
    IsGreatest (signScores (schmidtDensity w))
      (2 * Real.sqrt (1 + concurrence (schmidtAmp w) ^ 2)) := by
  rw [concurrence_sq_schmidtAmp]
  exact schmidt_chsh_isGreatest w

/-! ## Finite convex separability and the classical score bound. -/

/-- Werner separability: a finite convex mixture of products of actual density matrices. -/
def IsSeparable (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ) : Prop :=
  ∃ (n : ℕ) (w : Fin n → ℝ) (a b : Fin n → DensityMatrix Bool),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      ρ = ∑ i, (w i : ℂ) • ((a i).matrix ⊗ₖ (b i).matrix)

theorem isSeparable_posSemidef {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hρ : IsSeparable ρ) : ρ.PosSemidef := by
  rcases hρ with ⟨n, w, a, b, hw, _, rfl⟩
  apply BoundaryReconstruction.Thermal.psd_sum Finset.univ
  intro i _
  exact real_smul_positiveSemidefinite
    (BoundaryReconstruction.Thermal.tensor_posSemidef (a i).positive (b i).positive) (hw i)

theorem isSeparable_trace {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hρ : IsSeparable ρ) : ρ.trace = 1 := by
  rcases hρ with ⟨n, w, a, b, _, hw, rfl⟩
  simp only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_kronecker,
    density_trace_one, smul_eq_mul, mul_one]
  exact_mod_cast hw

private theorem psd_trace_re_nonneg {m : Type} [Fintype m] [DecidableEq m]
    {M : Matrix m m ℂ} (hM : M.PosSemidef) : 0 ≤ M.trace.re := by
  rw [Matrix.trace, Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  have h := hM.re_dotProduct_nonneg (Pi.single i 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

private theorem mean_conj_nonneg {m : Type} [Fintype m] [DecidableEq m]
    {ρ : Matrix m m ℂ} (hρ : ρ.PosSemidef) (M : Matrix m m ℂ) :
    0 ≤ (ρ * (Mᴴ * M)).trace.re := by
  have hcyc : (ρ * (Mᴴ * M)).trace = (M * ρ * Mᴴ).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (ρ * Mᴴ) M, Matrix.mul_assoc]
  rw [hcyc]
  exact psd_trace_re_nonneg (hρ.mul_mul_conjTranspose_same M)

private theorem mean_add {m : Type} [Fintype m] (ρ X Y : Matrix m m ℂ) :
    (ρ * (X + Y)).trace.re = (ρ * X).trace.re + (ρ * Y).trace.re := by
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

private theorem mean_smul {m : Type} [Fintype m] (ρ X : Matrix m m ℂ) (t : ℝ) :
    (ρ * ((t : ℂ) • X)).trace.re = t * (ρ * X).trace.re := by
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- A Hermitian test with scalar square has a correspondingly bounded expectation. -/
private theorem mean_sq_le {m : Type} [Fintype m] [DecidableEq m]
    {ρ : Matrix m m ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    {Z : Matrix m m ℂ} (hZ : Zᴴ = Z) {k : ℝ}
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

private theorem herm_trace_real {m : Type} [Fintype m] {X Y : Matrix m m ℂ}
    (hX : Xᴴ = X) (hY : Yᴴ = Y) :
    (((X * Y).trace.re : ℝ) : ℂ) = (X * Y).trace := by
  rw [← Complex.conj_eq_iff_re, ← Complex.star_def, ← Matrix.trace_conjTranspose,
    Matrix.conjTranspose_mul, hX, hY, Matrix.trace_mul_comm]

theorem density_sign_mean_le_one (ρ : DensityMatrix Bool) (a : Matrix Bool Bool ℂ)
    (ha : PairBell.SignTest a) : |(ρ.matrix * a).trace.re| ≤ 1 := by
  have hsq := mean_sq_le ρ.positive ρ.trace_one ha.1.eq
    (k := 1) (by simpa using ha.2)
  simpa using Real.abs_le_sqrt hsq

private theorem scalar_chsh_le_two (x₀ x₁ y₀ y₁ : ℝ)
    (hx₀ : |x₀| ≤ 1) (hx₁ : |x₁| ≤ 1) (hy₀ : |y₀| ≤ 1) (hy₁ : |y₁| ≤ 1) :
    x₀ * y₀ + x₀ * y₁ + x₁ * y₀ - x₁ * y₁ ≤ 2 := by
  have hmul (x y : ℝ) (hx : |x| ≤ 1) : x * y ≤ |y| := by
    calc
      x * y ≤ |x * y| := le_abs_self _
      _ = |x| * |y| := abs_mul _ _
      _ ≤ 1 * |y| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
      _ = |y| := one_mul _
  have hy : |y₀ + y₁| + |y₀ - y₁| ≤ 2 := by
    obtain ⟨h₀l, h₀u⟩ := abs_le.mp hy₀
    obtain ⟨h₁l, h₁u⟩ := abs_le.mp hy₁
    rcases le_total 0 (y₀ + y₁) with hs | hs
    · rcases le_total 0 (y₀ - y₁) with hd | hd
      · rw [abs_of_nonneg hs, abs_of_nonneg hd]
        linarith
      · rw [abs_of_nonneg hs, abs_of_nonpos hd]
        linarith
    · rcases le_total 0 (y₀ - y₁) with hd | hd
      · rw [abs_of_nonpos hs, abs_of_nonneg hd]
        linarith
      · rw [abs_of_nonpos hs, abs_of_nonpos hd]
        linarith
  calc
    x₀ * y₀ + x₀ * y₁ + x₁ * y₀ - x₁ * y₁ =
        x₀ * (y₀ + y₁) + x₁ * (y₀ - y₁) := by ring
    _ ≤ |y₀ + y₁| + |y₀ - y₁| := add_le_add (hmul _ _ hx₀) (hmul _ _ hx₁)
    _ ≤ 2 := hy

private theorem product_correlation (a b : DensityMatrix Bool)
    (X Y : Matrix Bool Bool ℂ) (hX : PairBell.SignTest X) (hY : PairBell.SignTest Y) :
    ((a.matrix ⊗ₖ b.matrix) * (X ⊗ₖ Y)).trace.re =
      (a.matrix * X).trace.re * (b.matrix * Y).trace.re := by
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
    ← herm_trace_real a.positive.1.eq hX.1.eq,
    ← herm_trace_real b.positive.1.eq hY.1.eq]
  simp [Complex.mul_re]

theorem product_chsh_le_two (a b : DensityMatrix Bool)
    (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ)
    (ha₀ : PairBell.SignTest a₀) (ha₁ : PairBell.SignTest a₁)
    (hb₀ : PairBell.SignTest b₀) (hb₁ : PairBell.SignTest b₁) :
    signScore (a.matrix ⊗ₖ b.matrix) a₀ a₁ b₀ b₁ ≤ 2 := by
  simp only [signScore, chshOperator, Matrix.mul_add, Matrix.mul_sub,
    Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re]
  rw [product_correlation a b a₀ b₀ ha₀ hb₀, product_correlation a b a₀ b₁ ha₀ hb₁,
    product_correlation a b a₁ b₀ ha₁ hb₀, product_correlation a b a₁ b₁ ha₁ hb₁]
  exact scalar_chsh_le_two _ _ _ _
    (density_sign_mean_le_one a a₀ ha₀) (density_sign_mean_le_one a a₁ ha₁)
    (density_sign_mean_le_one b b₀ hb₀) (density_sign_mean_le_one b b₁ hb₁)

theorem signScore_mixture {n : ℕ} (w : Fin n → ℝ)
    (ρ : Fin n → Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ) :
    signScore (∑ i, (w i : ℂ) • ρ i) a₀ a₁ b₀ b₁ =
      ∑ i, w i * signScore (ρ i) a₀ a₁ b₀ b₁ := by
  simp only [signScore, Finset.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
    Matrix.trace_smul, Complex.re_sum, smul_eq_mul, Complex.re_ofReal_mul]

/-- Finite convex separability implies the classical bound for every sign-test quadruple. -/
theorem separable_chsh_le_two {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hρ : IsSeparable ρ) (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ)
    (ha₀ : PairBell.SignTest a₀) (ha₁ : PairBell.SignTest a₁)
    (hb₀ : PairBell.SignTest b₀) (hb₁ : PairBell.SignTest b₁) :
    signScore ρ a₀ a₁ b₀ b₁ ≤ 2 := by
  rcases hρ with ⟨n, w, a, b, hw, hsum, rfl⟩
  rw [signScore_mixture]
  calc
    (∑ i, w i * signScore ((a i).matrix ⊗ₖ (b i).matrix) a₀ a₁ b₀ b₁) ≤
        ∑ i, w i * 2 := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (product_chsh_le_two (a i) (b i)
            a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁) (hw i))
    _ = 2 := by rw [← Finset.sum_mul, hsum, one_mul]

theorem separable_abs_chsh_le_two {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hρ : IsSeparable ρ) (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ)
    (ha₀ : PairBell.SignTest a₀) (ha₁ : PairBell.SignTest a₁)
    (hb₀ : PairBell.SignTest b₀) (hb₁ : PairBell.SignTest b₁) :
    |signScore ρ a₀ a₁ b₀ b₁| ≤ 2 := by
  have hupper := separable_chsh_le_two hρ a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
  have hneg := separable_chsh_le_two hρ (-a₀) (-a₁) b₀ b₁
    (signTest_neg ha₀) (signTest_neg ha₁) hb₀ hb₁
  rw [signScore_negAlice] at hneg
  exact abs_le.mpr ⟨by linarith, hupper⟩

theorem productDensity_separable (a b : DensityMatrix Bool) :
    IsSeparable (a.matrix ⊗ₖ b.matrix) := by
  refine ⟨1, fun _ => 1, fun _ => a, fun _ => b, ?_, ?_, ?_⟩
  · intro i
    norm_num
  · norm_num
  · simp

/-- A coordinate pure state, within the existing density-matrix type. -/
def basisQubit (b : Bool) : DensityMatrix Bool where
  matrix := Matrix.diagonal (fun i => if i = b then 1 else 0)
  positive := Matrix.PosSemidef.diagonal (by
    intro i
    change (0 : ℂ) ≤ if i = b then 1 else 0
    split_ifs <;> norm_num)
  trace_one := by simp [Matrix.trace_diagonal]

/-! ## Density separability recovers the zero observer product. -/

theorem schmidtDensity_separable_of_zero (w : TwoBranchWeight)
    (hw : amplitudeEntanglement w = 0) : IsSeparable (schmidtDensity w) := by
  rcases (amplitudeEntanglement_eq_zero_iff w).mp hw with hp | hp
  · have he : schmidtDensity w = (basisQubit true).matrix ⊗ₖ (basisQubit true).matrix := by
      ext ⟨i, k⟩ ⟨j, l⟩
      cases i <;> cases k <;> cases j <;> cases l <;>
        simp [schmidtDensity, amplitudeDensity, outer_apply, schmidtAmp, boolFin,
          basisQubit, hp, TwoBranchWeight.q]
    rw [he]
    exact productDensity_separable _ _
  · have he : schmidtDensity w = (basisQubit false).matrix ⊗ₖ (basisQubit false).matrix := by
      ext ⟨i, k⟩ ⟨j, l⟩
      cases i <;> cases k <;> cases j <;> cases l <;>
        simp [schmidtDensity, amplitudeDensity, outer_apply, schmidtAmp, boolFin,
          basisQubit, hp, TwoBranchWeight.q]
    rw [he]
    exact productDensity_separable _ _

/-- Standard finite-mixture separability is exactly the zero pair quantity. -/
theorem schmidtDensity_separable_iff (w : TwoBranchWeight) :
    IsSeparable (schmidtDensity w) ↔ amplitudeEntanglement w = 0 := by
  constructor
  · intro hsep
    obtain ⟨a₀, a₁, b₀, b₁, ha₀, ha₁, hb₀, hb₁, hs⟩ :=
      (schmidt_chsh_isGreatest w).1
    have hb := separable_chsh_le_two hsep a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
    rw [hs] at hb
    have hr : Real.sqrt (1 + 4 * amplitudeEntanglement w) ≤ 1 := by linarith
    have he := amplitudeEntanglement_nonneg w
    have hbase : 0 ≤ 1 + 4 * amplitudeEntanglement w := by linarith
    have hsqrt := Real.sq_sqrt hbase
    have hroot := Real.sqrt_nonneg (1 + 4 * amplitudeEntanglement w)
    nlinarith [mul_nonneg hroot (sub_nonneg.mpr hr)]
  · exact schmidtDensity_separable_of_zero w

theorem schmidtDensity_separable_iff_product (w : TwoBranchWeight) :
    IsSeparable (schmidtDensity w) ↔ ProductAmplitude (schmidtAmp w) :=
  (schmidtDensity_separable_iff w).trans (productAmplitude_schmidtAmp_iff w).symm

theorem purified_pair_separability (w : TwoBranchWeight) :
    (IsSeparable (schmidtDensity w) ↔ amplitudeEntanglement w = 0) ∧
    (amplitudeEntanglement w = 0 ↔ ProductAmplitude (schmidtAmp w)) :=
  ⟨schmidtDensity_separable_iff w, (productAmplitude_schmidtAmp_iff w).symm⟩

theorem schmidt_separability_nonvacuous :
    ¬ IsSeparable (schmidtDensity balancedBranch) ∧
      IsSeparable (schmidtDensity collapsedBranch) := by
  constructor
  · intro h
    have hz := (schmidtDensity_separable_iff balancedBranch).mp h
    exact (ne_of_gt balancedBranch_pos) hz
  · exact schmidtDensity_separable_of_zero collapsedBranch collapsedBranch_amplitude

/-! ## A joint unitary and invariance under a side-register unitary. -/

def cnotIndex (x : Fin 2 × Fin 2) : Fin 2 × Fin 2 :=
  (x.1, if x.1 = 0 then x.2 else flipQubit x.2)

/-- The controlled-NOT permutation matrix on the actual joint Hilbert carrier. -/
def cnotMatrix : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => if j = cnotIndex i then 1 else 0

theorem cnotMatrix_unitary :
    cnotMatrix ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change cnotMatrix * cnotMatrixᴴ = 1
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [cnotMatrix, cnotIndex, flipQubit, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

def cnotUnitary : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  ⟨cnotMatrix, cnotMatrix_unitary⟩

/-- The ordinary matrix-vector action of a joint unitary on the amplitude. -/
def applyUnitaryAmplitude (U : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ)
    (A : TwoQubitAmplitude) : TwoQubitAmplitude :=
  fun i j => ((U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) *ᵥ
    (fun x => A x.1 x.2)) (i, j)

theorem applyUnitaryAmplitude_cnot (A : TwoQubitAmplitude) :
    applyUnitaryAmplitude cnotUnitary A = cnotAmplitude A := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [applyUnitaryAmplitude, cnotUnitary, cnotMatrix, cnotIndex, cnotAmplitude,
      flipQubit, Matrix.mulVec, dotProduct]

theorem cnot_bell_eq_product :
    cnotAmplitude bellAmplitude = plusZeroAmplitude := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The controlled-NOT, applied in circuit order, maps the entangled Bell amplitude to a product. -/
theorem entanglement_split_unitary :
    ∃ U : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ,
      QuantumEntangled bellAmplitude ∧
      ProductAmplitude (applyUnitaryAmplitude U bellAmplitude) := by
  refine ⟨cnotUnitary, bell_state_nonseparable, ?_⟩
  rw [applyUnitaryAmplitude_cnot, cnot_bell_eq_product]
  exact plusZeroAmplitude_product

/-- The side-register operation is the source tensor unitary I ⊗ U. -/
def sideUnitaryAmplitude (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (A : TwoQubitAmplitude) : TwoQubitAmplitude :=
  applyUnitaryAmplitude (BoundaryReconstruction.Thermal.tensorUnitary 1 U) A

theorem sideUnitaryAmplitude_eq_mul_transpose (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (A : TwoQubitAmplitude) :
    Matrix.of (sideUnitaryAmplitude U A) = Matrix.of A * (U : Matrix (Fin 2) (Fin 2) ℂ)ᵀ := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [sideUnitaryAmplitude, applyUnitaryAmplitude,
      BoundaryReconstruction.Thermal.tensorUnitary, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

theorem sideUnitary_gram (U : Matrix.unitaryGroup (Fin 2) ℂ) (A : TwoQubitAmplitude) :
    Matrix.of (sideUnitaryAmplitude U A) * (Matrix.of (sideUnitaryAmplitude U A))ᴴ = Matrix.of A * (Matrix.of A)ᴴ := by
  have hu : (U : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *
      ((U : Matrix (Fin 2) (Fin 2) ℂ)ᵀ)ᴴ = 1 := by
    have h := congrArg Matrix.transpose U.property.1
    change ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
      (U : Matrix (Fin 2) (Fin 2) ℂ))ᵀ = (1 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ at h
    simpa only [Matrix.transpose_mul, Matrix.transpose_one,
      Matrix.conjTranspose_transpose, Matrix.transpose_conjTranspose] using h
  rw [sideUnitaryAmplitude_eq_mul_transpose, Matrix.conjTranspose_mul]
  calc
    (Matrix.of A * (U : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) *
        (((U : Matrix (Fin 2) (Fin 2) ℂ)ᵀ)ᴴ * (Matrix.of A)ᴴ) =
        Matrix.of A * ((U : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *
          ((U : Matrix (Fin 2) (Fin 2) ℂ)ᵀ)ᴴ) * (Matrix.of A)ᴴ := by noncomm_ring
    _ = Matrix.of A * (Matrix.of A)ᴴ := by rw [hu, Matrix.mul_one]

/-- The source partial trace is invariant under every side-register unitary. -/
theorem sideUnitary_marginal (U : Matrix.unitaryGroup (Fin 2) ℂ) (A : TwoQubitAmplitude) :
    BoundaryReconstruction.Thermal.marginalLeft (amplitudeDensity (sideUnitaryAmplitude U A)) =
      BoundaryReconstruction.Thermal.marginalLeft (amplitudeDensity A) := by
  simp only [amplitudeDensity_marginal, sideUnitary_gram]

theorem sideUnitary_concurrence_sq (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (A : TwoQubitAmplitude) :
    concurrence (sideUnitaryAmplitude U A) ^ 2 = concurrence A ^ 2 := by
  have h := congrArg Matrix.det (sideUnitary_gram U A)
  simp only [amplitudeDet_gram] at h
  have hn : ‖amplitudeDet (sideUnitaryAmplitude U A)‖ ^ 2 = ‖amplitudeDet A‖ ^ 2 := by
    exact_mod_cast h
  dsimp [concurrence]
  nlinarith [hn]

theorem sideUnitary_pair_quantity (w : TwoBranchWeight) (A : TwoQubitAmplitude)
    (hA : Matrix.of A * (Matrix.of A)ᴴ = Matrix.diagonal ![(w.p : ℂ), (w.q : ℂ)])
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    concurrence (sideUnitaryAmplitude U A) ^ 2 = 4 * amplitudeEntanglement w := by
  rw [sideUnitary_concurrence_sq]
  exact concurrence_sq_of_marginal w A hA

/-! ## The Werner family, partial transpose, and all-sign-test bounds. -/

/-- Partial transpose on the second factor, defined on the actual density matrix entries. -/
def partialTransposeRight (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun i j => ρ (i.1, j.2) (j.1, i.2)

theorem partialTransposeRight_kronecker (a b : Matrix Bool Bool ℂ) :
    partialTransposeRight (a ⊗ₖ b) = a ⊗ₖ bᵀ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rfl

theorem partialTransposeRight_mixture {n : ℕ} (w : Fin n → ℝ)
    (ρ : Fin n → Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    partialTransposeRight (∑ i, (w i : ℂ) • ρ i) =
      ∑ i, (w i : ℂ) • partialTransposeRight (ρ i) := by
  ext i j
  simp [partialTransposeRight, Matrix.sum_apply, Matrix.smul_apply]

/-- Finite convex products have positive partial transpose. -/
theorem separable_partialTranspose_pos {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hρ : IsSeparable ρ) : (partialTransposeRight ρ).PosSemidef := by
  rcases hρ with ⟨n, w, a, b, hw, _, rfl⟩
  rw [partialTransposeRight_mixture]
  apply BoundaryReconstruction.Thermal.psd_sum Finset.univ
  intro i _
  rw [partialTransposeRight_kronecker]
  have hb : (b i).matrix.PosSemidef := (b i).positive
  exact real_smul_positiveSemidefinite
    (BoundaryReconstruction.Thermal.tensor_posSemidef (a i).positive hb.transpose) (hw i)

/-- The two-qubit Bell state mixed with uniform white noise. -/
def wernerState (p : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (p : ℂ) • PairQubit.bellState + (((1 - p) / 4 : ℝ) : ℂ) • 1

theorem wernerState_posSemidef (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (wernerState p).PosSemidef := by
  unfold wernerState
  exact Matrix.PosSemidef.add
    (real_smul_positiveSemidefinite PairQubit.bell_state_posSemidef hp₀)
    (real_smul_positiveSemidefinite Matrix.PosSemidef.one (by linarith))

theorem wernerState_trace (p : ℝ) : (wernerState p).trace = 1 := by
  simp only [wernerState, Matrix.trace_add, Matrix.trace_smul,
    PairQubit.quantum_purification.2.2, Matrix.trace_one, smul_eq_mul]
  norm_num

def wernerDensity (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : DensityMatrix (Bool × Bool) where
  matrix := wernerState p
  positive := wernerState_posSemidef p hp₀ hp₁
  trace_one := wernerState_trace p

def antisymmetricKet : Bool × Bool → ℂ :=
  fun x => if x.1 = x.2 then 0 else if x.1 then -1 else 1

theorem antisymmetricKet_ne_zero : antisymmetricKet ≠ 0 := by
  intro h
  have e := congrFun h (false, true)
  norm_num [antisymmetricKet] at e

/-- The partial transpose has the antisymmetric eigenvector at eigenvalue (1 - 3p)/4. -/
theorem werner_partialTranspose_eigenvector (p : ℝ) :
    partialTransposeRight (wernerState p) *ᵥ antisymmetricKet =
      (((1 - 3 * p) / 4 : ℝ) : ℂ) • antisymmetricKet := by
  funext x
  rcases x with ⟨i, j⟩
  cases i <;> cases j <;>
    simp [partialTransposeRight, wernerState, PairQubit.bellState, antisymmetricKet,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.smul_apply,
      Matrix.one_apply] <;> ring

theorem werner_partialTranspose_has_eigenvalue (p : ℝ) :
    ∃ v : Bool × Bool → ℂ, v ≠ 0 ∧
      partialTransposeRight (wernerState p) *ᵥ v = (((1 - 3 * p) / 4 : ℝ) : ℂ) • v :=
  ⟨antisymmetricKet, antisymmetricKet_ne_zero, werner_partialTranspose_eigenvector p⟩

theorem werner_partialTranspose_expectation (p : ℝ) :
    (star antisymmetricKet ⬝ᵥ
      (partialTransposeRight (wernerState p) *ᵥ antisymmetricKet)).re = (1 - 3 * p) / 2 := by
  rw [werner_partialTranspose_eigenvector]
  simp [antisymmetricKet, dotProduct, Fintype.sum_prod_type, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- The Werner state is not a finite convex mixture of products above one third. -/
theorem werner_entangled (p : ℝ) (hp : (1 : ℝ) / 3 < p) :
    ¬ IsSeparable (wernerState p) := by
  intro hsep
  have h := (separable_partialTranspose_pos hsep).re_dotProduct_nonneg antisymmetricKet
  change 0 ≤ (star antisymmetricKet ⬝ᵥ
    (partialTransposeRight (wernerState p) *ᵥ antisymmetricKet)).re at h
  rw [werner_partialTranspose_expectation] at h
  linarith

private theorem kron_conjTranspose (a b : Matrix Bool Bool ℂ) :
    (a ⊗ₖ b)ᴴ = aᴴ ⊗ₖ bᴴ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kronecker_apply, StarMul.star_mul]
  exact mul_comm _ _

theorem chshOperator_hermitian (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ)
    (ha₀ : PairBell.SignTest a₀) (ha₁ : PairBell.SignTest a₁)
    (hb₀ : PairBell.SignTest b₀) (hb₁ : PairBell.SignTest b₁) :
    (chshOperator a₀ a₁ b₀ b₁).IsHermitian := by
  change (chshOperator a₀ a₁ b₀ b₁)ᴴ = chshOperator a₀ a₁ b₀ b₁
  simp only [chshOperator, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    kron_conjTranspose, ha₀.1.eq, ha₁.1.eq, hb₀.1.eq, hb₁.1.eq]

/-- The exact square identity supplies the commuting and identity-test cases. -/
theorem chshOperator_square (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ)
    (ha₀ : PairBell.SignTest a₀) (ha₁ : PairBell.SignTest a₁)
    (hb₀ : PairBell.SignTest b₀) (hb₁ : PairBell.SignTest b₁) :
    chshOperator a₀ a₁ b₀ b₁ * chshOperator a₀ a₁ b₀ b₁ =
      (4 : ℂ) • 1 - (a₀ * a₁ - a₁ * a₀) ⊗ₖ (b₀ * b₁ - b₁ * b₀) := by
  simp only [chshOperator, add_mul, sub_mul, mul_add, mul_sub,
    ← Matrix.mul_kronecker_mul, ha₀.2, ha₁.2, hb₀.2, hb₁.2, Matrix.one_kronecker_one]
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.kronecker_apply, smul_eq_mul]
  ring

theorem commuting_chsh_abs_le_two {ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ)
    (ha₀ : PairBell.SignTest a₀) (ha₁ : PairBell.SignTest a₁)
    (hb₀ : PairBell.SignTest b₀) (hb₁ : PairBell.SignTest b₁)
    (hcomm : a₀ * a₁ = a₁ * a₀ ∨ b₀ * b₁ = b₁ * b₀) :
    |signScore ρ a₀ a₁ b₀ b₁| ≤ 2 := by
  have hsq : chshOperator a₀ a₁ b₀ b₁ * chshOperator a₀ a₁ b₀ b₁ =
      ((4 : ℝ) : ℂ) • 1 := by
    rw [chshOperator_square a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁]
    rcases hcomm with h | h
    · rw [h, sub_self, Matrix.zero_kronecker, sub_zero]
      norm_num
    · rw [h, sub_self, Matrix.kronecker_zero, sub_zero]
      norm_num
  have hs := mean_sq_le hρ htr (chshOperator_hermitian a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁).eq hsq
  have hab := Real.abs_le_sqrt hs
  norm_num at hab
  exact hab
private theorem signTest_scalar {a : Matrix Bool Bool ℂ} (ha : PairBell.SignTest a)
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


/-- White noise contributes zero when Alice's two tests have zero trace; Bob remains unrestricted. -/
theorem werner_signScore_scaling (p : ℝ) (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ)
    (ta₀ : a₀.trace = 0) (ta₁ : a₁.trace = 0) :
    signScore (wernerState p) a₀ a₁ b₀ b₁ =
      p * signScore PairQubit.bellState a₀ a₁ b₀ b₁ := by
  have ht : (chshOperator a₀ a₁ b₀ b₁).trace = 0 := by
    simp [chshOperator, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_kronecker,
      ta₀, ta₁]
  simp only [signScore, wernerState, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    Complex.re_ofReal_mul, ht, mul_zero, add_zero]

theorem bell_localBlochSq_zero : PairBell.localBlochSq PairQubit.bellState = 0 := by
  norm_num [PairBell.localBlochSq, BoundaryReconstruction.Thermal.marginalLeft,
    PairQubit.bellState, PairQubit.pairX, PairQubit.pairY, PairQubit.pairZ,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]

/-- Every sign-test quadruple, including identity tests on either side, obeys the bound. -/
theorem werner_abs_chsh_le_two (p : ℝ) (hp₀ : 0 ≤ p) (hp : p ≤ 1 / Real.sqrt 2)
    (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ)
    (ha₀ : PairBell.SignTest a₀) (ha₁ : PairBell.SignTest a₁)
    (hb₀ : PairBell.SignTest b₀) (hb₁ : PairBell.SignTest b₁) :
    |signScore (wernerState p) a₀ a₁ b₀ b₁| ≤ 2 := by
  classical
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hssq : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsone : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hpmul : p * Real.sqrt 2 ≤ 1 := (le_div_iff₀ hspos).mp hp
  have hp₁ : p ≤ 1 := by
    nlinarith [mul_nonneg hp₀ (sub_nonneg.mpr hsone)]
  by_cases ht : a₀.trace = 0 ∧ a₁.trace = 0
  · obtain ⟨ta₀, ta₁⟩ := ht
    rw [werner_signScore_scaling p a₀ a₁ b₀ b₁ ta₀ ta₁,
      abs_mul, abs_of_nonneg hp₀]
    have hb := mixedExcess_abs PairQubit.bellState PairQubit.bell_state_posSemidef
      PairQubit.quantum_purification.2.2 a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
    rw [bell_localBlochSq_zero, sub_zero] at hb
    calc
      p * |signScore PairQubit.bellState a₀ a₁ b₀ b₁| ≤ p * (2 * Real.sqrt 2) :=
        mul_le_mul_of_nonneg_left hb hp₀
      _ ≤ 2 := by nlinarith [hpmul]
  · have hc : a₀ * a₁ = a₁ * a₀ ∨ b₀ * b₁ = b₁ * b₀ := by
      rcases not_and_or.mp ht with ht | ht
      · left
        rcases signTest_scalar ha₀ ht with he | he <;> simp [he]
      · left
        rcases signTest_scalar ha₁ ht with he | he <;> simp [he]
    exact commuting_chsh_abs_le_two (wernerState_posSemidef p hp₀ hp₁)
      (wernerState_trace p) a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁ hc

theorem werner_chsh_le_two (p : ℝ) (hp₀ : 0 ≤ p) (hp : p ≤ 1 / Real.sqrt 2)
    (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ)
    (ha₀ : PairBell.SignTest a₀) (ha₁ : PairBell.SignTest a₁)
    (hb₀ : PairBell.SignTest b₀) (hb₁ : PairBell.SignTest b₁) :
    signScore (wernerState p) a₀ a₁ b₀ b₁ ≤ 2 :=
  (le_abs_self _).trans (werner_abs_chsh_le_two p hp₀ hp a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁)

/-- A concrete density is entangled while every permitted CHSH score stays within two. -/
theorem werner_entangled_without_violation :
    ∃ ρ : DensityMatrix (Bool × Bool), ¬ IsSeparable ρ.matrix ∧
      ∀ a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ,
        PairBell.SignTest a₀ → PairBell.SignTest a₁ →
        PairBell.SignTest b₀ → PairBell.SignTest b₁ →
        |signScore ρ.matrix a₀ a₁ b₀ b₁| ≤ 2 := by
  refine ⟨wernerDensity (1 / 2) (by norm_num) (by norm_num),
    werner_entangled (1 / 2) (by norm_num), ?_⟩
  intro a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
  apply werner_abs_chsh_le_two (1 / 2) (by norm_num) _ a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end
end OperatorKO7.Meta.BoundaryObserver.PairPurification
