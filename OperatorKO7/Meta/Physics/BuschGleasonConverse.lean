import OperatorKO7.Meta.Physics.BuschGleasonFinite
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Finite-dimensional Busch-Gleason converse

For a complex-linear functional `μ` on finite-dimensional complex matrices, positivity on positive-semidefinite matrices and normalization at the identity make `traceDual μ` a density operator. The module also proves that the representing density operator is unique.

The proof derives positivity from rank-one matrices, Hermiticity by polarization, and unit trace from the trace representation at the identity. The theorem assumes complex-linearity and finite dimension.

Trust status: PROVEN-IN-LEAN, Mathlib baseline.
-/

namespace OperatorKO7.Meta.Physics.BuschGleasonConverse

open Matrix BigOperators
open scoped ComplexOrder
open OperatorKO7.Meta.Physics.BuschGleasonFinite

variable {d : ℕ}

/-! ## 1. Rank-one positive matrices and the quadratic form -/

/-- The rank-one matrix `x xᴴ`, with entries `(x xᴴ) i j = x i * star (x j)`. -/
noncomputable def rankOne (x : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => x i * star (x j)

/-- The rank-one matrix is positive semidefinite: it is the conjugate-transpose
square of the row matrix whose single row is `star x`. -/
theorem rankOne_posSemidef (x : Fin d → ℂ) : (rankOne x).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self
    (Matrix.of (fun (_ : Fin 1) (j : Fin d) => star (x j)))
  have hEq : (Matrix.of (fun (_ : Fin 1) (j : Fin d) => star (x j)))ᴴ *
      (Matrix.of (fun (_ : Fin 1) (j : Fin d) => star (x j))) = rankOne x := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, rankOne]
  rwa [hEq] at h

/-- Trace of the representer against a rank-one matrix is the quadratic form. -/
theorem trace_mul_rankOne (ρ : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    (ρ * rankOne x).trace = star x ⬝ᵥ ρ *ᵥ x := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, rankOne, Matrix.of_apply]
  rw [dotProduct]
  simp only [Matrix.mulVec, dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-! ## 2. Positive functionals -/

/-- A functional is positive when it is nonnegative on every positive-semidefinite
matrix. -/
def IsPositiveFunctional (μ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ) : Prop :=
  ∀ E : Matrix (Fin d) (Fin d) ℂ, E.PosSemidef → 0 ≤ μ E

/-- The quadratic form of the representer of a positive functional is
nonnegative at every vector. -/
theorem quadraticForm_nonneg {μ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ}
    (hpos : IsPositiveFunctional μ) (x : Fin d → ℂ) :
    0 ≤ star x ⬝ᵥ (traceDual μ) *ᵥ x := by
  have h := hpos (rankOne x) (rankOne_posSemidef x)
  rwa [← traceDual_represents μ (rankOne x), trace_mul_rankOne] at h

/-! ## 3. Hermiticity by polarization -/

/-- Diagonal entries of the representer are real and nonnegative: test the
quadratic form at a standard basis vector. -/
theorem diag_nonneg_of_positive {μ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ}
    (hpos : IsPositiveFunctional μ) (i : Fin d) :
    0 ≤ traceDual μ i i := by
  have h := quadraticForm_nonneg hpos (Pi.single i (1 : ℂ))
  have hstar : star (Pi.single i (1 : ℂ)) = (Pi.single i 1 : Fin d → ℂ) := by
    ext k; simp [Pi.single_apply, Pi.star_apply, apply_ite]
  rw [hstar, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
    single_one_dotProduct] at h
  simpa using h

/-- Cross term of the quadratic form at two single-support vectors. -/
theorem cross_single (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) (a c : ℂ) :
    star (Pi.single i a) ⬝ᵥ A *ᵥ (Pi.single j c) = star a * A i j * c := by
  rw [Matrix.mulVec_single]
  simp only [dotProduct, Pi.star_apply, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Polarization step: the quadratic form at `e_i + c e_j` expands bilinearly. -/
theorem quadratic_pair (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) (c : ℂ) :
    star (Pi.single i (1 : ℂ) + Pi.single j c) ⬝ᵥ
        A *ᵥ (Pi.single i (1 : ℂ) + Pi.single j c)
      = A i i + (star c * A j j * c) + A i j * c + star c * A j i := by
  rw [star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
    cross_single, cross_single, cross_single, cross_single]
  simp only [star_one, one_mul, mul_one]
  ring

/-- Abstract polarization: if `u + v` is real and `I*u - I*v` is real, then
`v = star u`. -/
theorem eq_star_of_polarization (u v : ℂ)
    (h1 : (u + v).im = 0)
    (h2 : (Complex.I * u - Complex.I * v).im = 0) : v = star u := by
  simp only [Complex.add_im] at h1
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add] at h2
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]; linarith
  · simp only [Complex.star_def, Complex.conj_im]; linarith

/-- The quadratic form at a standard basis vector is the diagonal entry. -/
theorem quadratic_single (A : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    star (Pi.single i (1 : ℂ)) ⬝ᵥ A *ᵥ (Pi.single i (1 : ℂ)) = A i i := by
  rw [cross_single]; simp

/-- **Hermiticity from positivity.** A matrix whose quadratic form is
nonnegative at every complex vector is Hermitian. Proved by polarization at
`c = 1` and `c = i`, with no spectral theory. -/
theorem isHermitian_of_quadraticForm_nonneg (A : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ x : Fin d → ℂ, 0 ≤ star x ⬝ᵥ A *ᵥ x) : A.IsHermitian := by
  have hdiag : ∀ k : Fin d, (A k k).im = 0 := by
    intro k
    have hk := h (Pi.single k (1 : ℂ))
    rw [quadratic_single] at hk
    exact ((Complex.nonneg_iff.mp hk).2).symm
  have hoff : ∀ i j : Fin d, A j i = star (A i j) := by
    intro i j
    have h1 := h (Pi.single i (1 : ℂ) + Pi.single j 1)
    have hI := h (Pi.single i (1 : ℂ) + Pi.single j Complex.I)
    rw [quadratic_pair] at h1 hI
    have r1 : (A i i + star (1 : ℂ) * A j j * 1 + A i j * 1 + star (1 : ℂ) * A j i).im = 0 :=
      ((Complex.nonneg_iff.mp h1).2).symm
    have rI : (A i i + star Complex.I * A j j * Complex.I + A i j * Complex.I
        + star Complex.I * A j i).im = 0 :=
      ((Complex.nonneg_iff.mp hI).2).symm
    have e1 : (A i j + A j i).im = 0 := by
      simp only [star_one, one_mul, mul_one, Complex.add_im] at r1
      simp only [Complex.add_im]
      linarith [hdiag i, hdiag j, r1]
    have e2 : (Complex.I * A i j - Complex.I * A j i).im = 0 := by
      have hII : star Complex.I * A j j * Complex.I = A j j := by
        simp only [Complex.star_def, Complex.conj_I]
        ring_nf
        simp [Complex.I_sq]
      rw [hII] at rI
      simp only [Complex.star_def, Complex.conj_I, Complex.add_im] at rI
      simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        zero_mul, one_mul, zero_add]
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.neg_im, zero_mul, one_mul, zero_add, neg_mul] at rI
      linarith [hdiag i, hdiag j, rI]
    exact eq_star_of_polarization (A i j) (A j i) e1 e2
  ext i j
  simp only [Matrix.conjTranspose_apply, RCLike.star_def]
  rw [hoff j i]
  simp

/-! ## 4. The converse theorem -/

/-- The representer of a positive normalized complex-linear functional is a density operator. -/
theorem representer_isDensity_of_positive_normalized
    (μ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ)
    (hpos : IsPositiveFunctional μ) (hnorm : μ 1 = 1) :
    IsDensity (traceDual μ) := by
  constructor
  · exact ⟨isHermitian_of_quadraticForm_nonneg _ (quadraticForm_nonneg hpos),
      quadraticForm_nonneg hpos⟩
  · have h := traceDual_represents μ 1
    rwa [mul_one, hnorm] at h

/-- Every positive normalized complex-linear functional on these matrices has a unique density operator whose trace pairing agrees with the functional. -/
theorem density_functional_correspondence
    (μ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ)
    (hpos : IsPositiveFunctional μ) (hnorm : μ 1 = 1) :
    ∃! ρ : Matrix (Fin d) (Fin d) ℂ, IsDensity ρ ∧ ∀ A, (ρ * A).trace = μ A := by
  refine ⟨traceDual μ,
    ⟨representer_isDensity_of_positive_normalized μ hpos hnorm,
      traceDual_represents μ⟩, ?_⟩
  intro ρ hρ
  exact trace_rule_unique ρ (traceDual μ)
    (fun A => by rw [hρ.2 A, traceDual_represents μ A])

/-- Lean declaration name for the converse density theorem. -/
def busch_gleason_converse_anchor : String :=
  "OperatorKO7.Meta.Physics.BuschGleasonConverse.representer_isDensity_of_positive_normalized"

end OperatorKO7.Meta.Physics.BuschGleasonConverse
