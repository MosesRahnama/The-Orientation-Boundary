import Mathlib

/-!
# Finite density matrices and POVM measurement (Reverse-Bridge QM substrate, target b)

Mechanizes the finite mixed-state / measurement object the reverse-bridge program imports as an analogy:
a finite density matrix `rho` (positive semidefinite, hence Hermitian, with unit trace) and a POVM
`{E i}` (positive-semidefinite effects summing to the identity), with the Born rule
`p i = Re Tr(rho E_i)` proved to be a genuine probability distribution: each `p i` is nonnegative and the
`p i` sum to one.

Complements (does not duplicate) the Born-rule-uniqueness reverse-bridge module (which derives the Born
exponent on pure states): here the object is the mixed-state density matrix and a general POVM, and the
result is that the Born probabilities form a bona fide distribution.

## Module contract
- Relation: finite-dimensional complex matrix algebra (density matrices and POVM effects).
- Closure: `propext`, `Classical.choice`, `Quot.sound`.
- Trust: no `sorry`/`admit`/`axiom`/`native_decide`/`@[csimp]`. Non-vacuity: the maximally mixed qubit
  state and the computational-basis POVM, with `p 0 = 1/2` computed.
- Scope: the probability-distribution property of POVM outcomes on a density matrix; no dynamics.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-- A finite **density matrix**: positive semidefinite (so Hermitian and `rho ≥ 0`) with unit trace. -/
def IsDensityMatrix (rho : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  rho.PosSemidef ∧ rho.trace = 1

/-- A density matrix is Hermitian. -/
theorem IsDensityMatrix.isHermitian {rho : Matrix (Fin n) (Fin n) ℂ}
    (h : IsDensityMatrix rho) : rho.IsHermitian := h.1.1

/-- A finite **POVM**: a family of positive-semidefinite effects summing to the identity. -/
def IsPOVM {ι : Type*} [Fintype ι] (E : ι → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i, (E i).PosSemidef) ∧ ∑ i, E i = 1

/-- The **Born probability** of outcome `i`: `Re Tr(rho E_i)`. -/
noncomputable def prob {ι : Type*} (rho : Matrix (Fin n) (Fin n) ℂ)
    (E : ι → Matrix (Fin n) (Fin n) ℂ) (i : ι) : ℝ :=
  ((rho * E i).trace).re

/-- A diagonal entry of a positive-semidefinite matrix has nonnegative real part. -/
theorem psd_diag_re_nonneg {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) (i : Fin n) :
    0 ≤ (M i i).re := by
  have h := hM.re_dotProduct_nonneg (Pi.single i 1)
  have he : star (Pi.single i (1 : ℂ)) ⬝ᵥ (M *ᵥ Pi.single i 1) = M i i := by
    simp [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq, eq_comm]
  rw [he] at h
  simpa using h

/-- The real part of the trace of a positive-semidefinite matrix is nonnegative. -/
theorem psd_trace_re_nonneg {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) :
    0 ≤ (M.trace).re := by
  have htr : (M.trace).re = ∑ i, (M i i).re := by
    simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  rw [htr]
  exact Finset.sum_nonneg fun i _ => psd_diag_re_nonneg hM i

/-- **Each Born probability is nonnegative.** Writing `rho = S * S` with `S = sqrt rho` Hermitian,
`Tr(rho E_i) = Tr(S E_i S)` and `S E_i S` is positive semidefinite. -/
theorem prob_nonneg {ι : Type*} [Fintype ι] {rho : Matrix (Fin n) (Fin n) ℂ}
    {E : ι → Matrix (Fin n) (Fin n) ℂ} (hrho : IsDensityMatrix rho) (hE : IsPOVM E) (i : ι) :
    0 ≤ prob rho E i := by
  set S := hrho.1.sqrt with hSdef
  have hSS : S * S = rho := hrho.1.sqrt_mul_self
  have hSh : Sᴴ = S := hrho.1.posSemidef_sqrt.1.eq
  have hPSD : (S * E i * S).PosSemidef := by
    have := (hE.1 i).mul_mul_conjTranspose_same S
    rwa [hSh] at this
  have htr : (rho * E i).trace = (S * E i * S).trace := by
    rw [← hSS, Matrix.mul_assoc, Matrix.trace_mul_comm]
  show 0 ≤ ((rho * E i).trace).re
  rw [htr]
  exact psd_trace_re_nonneg hPSD

/-- **The Born probabilities sum to one.** `∑ i, Re Tr(rho E_i) = Re Tr(rho * ∑ E_i) = Re Tr rho = 1`. -/
theorem prob_sum_one {ι : Type*} [Fintype ι] {rho : Matrix (Fin n) (Fin n) ℂ}
    {E : ι → Matrix (Fin n) (Fin n) ℂ} (hrho : IsDensityMatrix rho) (hE : IsPOVM E) :
    ∑ i, prob rho E i = 1 := by
  have hsum : ∑ i, (rho * E i).trace = (1 : ℂ) := by
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, hE.2, Matrix.mul_one, hrho.2]
  calc ∑ i, prob rho E i = ∑ i, ((rho * E i).trace).re := rfl
    _ = (∑ i, (rho * E i).trace).re := by rw [Complex.re_sum]
    _ = (1 : ℂ).re := by rw [hsum]
    _ = 1 := Complex.one_re

/-! ## Non-vacuity: the maximally mixed qubit and the computational-basis POVM. -/

/-- The maximally mixed qubit state `rho = diag(1/2, 1/2)`. -/
noncomputable def rhoMix : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![((1 / 2 : ℝ) : ℂ), ((1 / 2 : ℝ) : ℂ)]

/-- The computational-basis POVM `{|0><0|, |1><1|}` on a qubit. -/
noncomputable def basisPOVM : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![Matrix.diagonal ![((1 : ℝ) : ℂ), ((0 : ℝ) : ℂ)],
    Matrix.diagonal ![((0 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]]

theorem isDensityMatrix_rhoMix : IsDensityMatrix rhoMix := by
  refine ⟨?_, ?_⟩
  · unfold rhoMix
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> exact Complex.zero_le_real.mpr (by norm_num)
  · unfold rhoMix
    rw [Matrix.trace_diagonal, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ← Complex.ofReal_add]
    norm_num

theorem isPOVM_basisPOVM : IsPOVM basisPOVM := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · show (Matrix.diagonal ![((1 : ℝ) : ℂ), ((0 : ℝ) : ℂ)]).PosSemidef
      rw [Matrix.posSemidef_diagonal_iff]
      intro j; fin_cases j <;> exact Complex.zero_le_real.mpr (by norm_num)
    · show (Matrix.diagonal ![((0 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).PosSemidef
      rw [Matrix.posSemidef_diagonal_iff]
      intro j; fin_cases j <;> exact Complex.zero_le_real.mpr (by norm_num)
  · rw [Fin.sum_univ_two]
    show Matrix.diagonal ![((1 : ℝ) : ℂ), ((0 : ℝ) : ℂ)]
        + Matrix.diagonal ![((0 : ℝ) : ℂ), ((1 : ℝ) : ℂ)] = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply]

/-- The computational-basis POVM reads the maximally mixed qubit as `1/2` for the first outcome. -/
theorem prob_rhoMix_basisPOVM_zero : prob rhoMix basisPOVM 0 = 1 / 2 := by
  show ((rhoMix * basisPOVM 0).trace).re = 1 / 2
  simp only [rhoMix, basisPOVM, Matrix.cons_val_zero]
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

#print axioms IsDensityMatrix.isHermitian
#print axioms prob_nonneg
#print axioms prob_sum_one
#print axioms isDensityMatrix_rhoMix
#print axioms isPOVM_basisPOVM
#print axioms prob_rhoMix_basisPOVM_zero

end OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM
