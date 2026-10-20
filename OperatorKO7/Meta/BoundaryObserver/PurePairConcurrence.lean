import OperatorKO7.Meta.BoundaryObserver.PairPurification

set_option autoImplicit false

/-!
# Every pure two-qubit state is the purified pair of its marginal's spectral law

`PairPurification.concurrence_sq_of_marginal` gives `C² = 4κρ` for an amplitude whose first
marginal is already `diagonal ![κ, ρ]`. This module removes that hypothesis. For every amplitude
the squared concurrence is four times the determinant of the first marginal `A Aᴴ`, hence four
times the product of its two eigenvalues. For a normalized amplitude a unitary on the first
system turns the marginal into `diagonal ![κ, ρ]`, with `(κ, ρ)` the spectral law of the marginal,
so the state is the purification of that law on a merged pair by a second two-state system, and
it is entangled exactly when `κρ > 0`.

Scope: pure states of two two-state systems. Mixed states and larger systems are outside this
module; the Werner family of `PairPurification` records the mixed-state boundary.
-/

namespace OperatorKO7.Meta.BoundaryObserver.PurePairConcurrence

open OperatorKO7.Meta.UUET
open OperatorKO7.Meta.UUET.Quantum
open OperatorKO7.Meta.BoundaryObserver.PairPurification
open scoped Matrix ComplexOrder

noncomputable section

/-- The first marginal `A Aᴴ` of a two-qubit amplitude. -/
def marginal (A : TwoQubitAmplitude) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of A * (Matrix.of A)ᴴ

theorem marginal_isHermitian (A : TwoQubitAmplitude) : (marginal A).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self (Matrix.of A)

theorem marginal_posSemidef (A : TwoQubitAmplitude) : (marginal A).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose (Matrix.of A)

/-- Proves: for every amplitude, the squared concurrence is four times the determinant of the
first marginal. Scope: no normalization is assumed. -/
theorem concurrence_sq_eq_four_det_marginal (A : TwoQubitAmplitude) :
    ((concurrence A ^ 2 : ℝ) : ℂ) = 4 * (marginal A).det := by
  rw [marginal, amplitudeDet_gram, concurrence]
  push_cast
  ring

/-- Proves: for every amplitude, the squared concurrence is four times the product of the two
eigenvalues of the first marginal. -/
theorem concurrence_sq_eq_four_eigenvalue_product (A : TwoQubitAmplitude) :
    concurrence A ^ 2 =
      4 * ((marginal_isHermitian A).eigenvalues 0 * (marginal_isHermitian A).eigenvalues 1) := by
  have h := concurrence_sq_eq_four_det_marginal A
  rw [(marginal_isHermitian A).det_eq_prod_eigenvalues, Fin.prod_univ_two] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  rfl

/-- The trace of the first marginal is the squared norm of the amplitude. -/
theorem marginal_trace (A : TwoQubitAmplitude) :
    (marginal A).trace = ((∑ i, ∑ j, Complex.normSq (A i j) : ℝ) : ℂ) := by
  simp only [marginal, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Complex.star_def, Complex.mul_conj]
  push_cast
  rfl

/-- Proves: the two eigenvalues of the first marginal add to the squared norm of the amplitude. -/
theorem eigenvalue_sum (A : TwoQubitAmplitude) :
    (marginal_isHermitian A).eigenvalues 0 + (marginal_isHermitian A).eigenvalues 1 =
      ∑ i, ∑ j, Complex.normSq (A i j) := by
  set hH := marginal_isHermitian A
  have hd := hH.star_mul_self_mul_eq_diagonal
  have ht := congrArg Matrix.trace hd
  rw [Matrix.trace_diagonal, Fin.sum_univ_two, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    (Matrix.mem_unitaryGroup_iff).mp hH.eigenvectorUnitary.2, Matrix.one_mul, marginal_trace] at ht
  have hre := congrArg Complex.re ht
  simpa using hre.symm

/-- Proves: after a unitary on the first system, every normalized pure state of two two-state
systems has first marginal `diagonal ![κ, ρ]` for the spectral law `w = (κ, ρ)` of its marginal,
and its squared concurrence is `4κρ`.
Scope: pure two-qubit states; the weight `w` is the spectrum of the marginal. -/
theorem pure_state_purified_pair (A : TwoQubitAmplitude)
    (hA : ∑ i, ∑ j, Complex.normSq (A i j) = 1) :
    ∃ (w : TwoBranchWeight) (U : Matrix.unitaryGroup (Fin 2) ℂ),
      (U : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of A *
          ((U : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of A)ᴴ =
        Matrix.diagonal ![(w.p : ℂ), (w.q : ℂ)] ∧
      concurrence A ^ 2 = 4 * amplitudeEntanglement w := by
  set hH := marginal_isHermitian A
  have hsum : hH.eigenvalues 0 + hH.eigenvalues 1 = 1 := (eigenvalue_sum A).trans hA
  have h0 : 0 ≤ hH.eigenvalues 0 := (marginal_posSemidef A).eigenvalues_nonneg 0
  have h1 : 0 ≤ hH.eigenvalues 1 := (marginal_posSemidef A).eigenvalues_nonneg 1
  refine ⟨⟨hH.eigenvalues 0, h0, by linarith⟩, star hH.eigenvectorUnitary, ?_, ?_⟩
  · have hd := hH.star_mul_self_mul_eq_diagonal
    have hq : (1 - hH.eigenvalues 0 : ℝ) = hH.eigenvalues 1 := by linarith
    rw [Matrix.conjTranspose_mul, unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    calc (hH.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Matrix.of A *
            ((Matrix.of A)ᴴ * (hH.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ))
        = star (hH.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) * marginal A *
            (hH.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) := by
          simp only [marginal, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
      _ = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := hd
      _ = Matrix.diagonal ![((hH.eigenvalues 0 : ℝ) : ℂ), ((1 - hH.eigenvalues 0 : ℝ) : ℂ)] := by
          have hfun : (RCLike.ofReal ∘ hH.eigenvalues : Fin 2 → ℂ) =
              ![((hH.eigenvalues 0 : ℝ) : ℂ), ((1 - hH.eigenvalues 0 : ℝ) : ℂ)] := by
            funext i
            fin_cases i
            · rfl
            · show ((hH.eigenvalues 1 : ℝ) : ℂ) = ((1 - hH.eigenvalues 0 : ℝ) : ℂ)
              rw [hq]
          rw [hfun]
  · rw [concurrence_sq_eq_four_eigenvalue_product]
    have hq : hH.eigenvalues 1 = 1 - hH.eigenvalues 0 := by linarith
    simp only [amplitudeEntanglement, TwoBranchWeight.q, hq]

/-- Proves: a pure two-qubit state is entangled exactly when the product of the two eigenvalues
of its first marginal is positive. -/
theorem pure_state_entangled_iff (A : TwoQubitAmplitude) :
    QuantumEntangled A ↔
      0 < (marginal_isHermitian A).eigenvalues 0 * (marginal_isHermitian A).eigenvalues 1 := by
  set hH := marginal_isHermitian A
  have h0 : 0 ≤ hH.eigenvalues 0 := (marginal_posSemidef A).eigenvalues_nonneg 0
  have h1 : 0 ≤ hH.eigenvalues 1 := (marginal_posSemidef A).eigenvalues_nonneg 1
  have hC := concurrence_sq_eq_four_eigenvalue_product A
  have hprod : 0 ≤ hH.eigenvalues 0 * hH.eigenvalues 1 := mul_nonneg h0 h1
  rw [QuantumEntangled, productAmplitude_iff_det_zero]
  constructor
  · intro hdet
    rcases hprod.lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      apply hdet
      have hc0 : concurrence A ^ 2 = 0 := by rw [hC, ← hzero, mul_zero]
      have hn : ‖amplitudeDet A‖ = 0 := by
        have : concurrence A = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc0
        simpa [concurrence] using this
      exact norm_eq_zero.mp hn
  · intro hpos hdet
    have hc0 : concurrence A = 0 := by simp [concurrence, hdet]
    rw [hc0] at hC
    linarith

/-- Non-vacuity: the normalization hypothesis holds for every purified pair `schmidtAmp w`. -/
theorem schmidtAmp_normalized (w : TwoBranchWeight) :
    ∑ i, ∑ j, Complex.normSq (schmidtAmp w i j) = 1 := by
  simp only [Fin.sum_univ_two, schmidtAmp]
  simp [Complex.normSq_ofReal, Real.mul_self_sqrt w.nonneg, Real.mul_self_sqrt w.q_nonneg]
  simp [TwoBranchWeight.q]

/-- Non-vacuity: the fair purified pair satisfies the hypothesis of `pure_state_purified_pair`
and is entangled. -/
theorem fair_pair_witness :
    (∑ i, ∑ j, Complex.normSq (schmidtAmp balancedBranch i j) = 1) ∧
      QuantumEntangled (schmidtAmp balancedBranch) :=
  ⟨schmidtAmp_normalized balancedBranch, schmidtAmp_nonvacuous.1⟩

end

end OperatorKO7.Meta.BoundaryObserver.PurePairConcurrence
