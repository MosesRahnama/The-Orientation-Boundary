import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Based Hermitian Kernels

A based Hermitian kernel is a complex-valued kernel with a distinguished base
point at which the kernel vanishes, Hermitian symmetry, and positive
semidefinite finite Gram matrices. Every finite sample admits a Kolmogorov
feature realization in Euclidean space, and the feature-distance identity
expresses Hilbert-space distance through kernel values.
-/

set_option autoImplicit false

open scoped ComplexOrder
open Matrix

namespace OperatorKO7.RH.Screw.BasedKernel

noncomputable section

/-- The Gram matrix of a kernel on a finite sample. -/
def kernelGram {X : Type*} (K : X → X → ℂ) {n : ℕ} (x : Fin n → X) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => K (x i) (x j)

/-- The finite quadratic form attached to a kernel and sample. -/
def kernelQuadratic {X : Type*} (K : X → X → ℂ) {n : ℕ} (x : Fin n → X)
    (c : Fin n → ℂ) : ℂ :=
  star c ⬝ᵥ (kernelGram K x *ᵥ c)

/-- A based Hermitian kernel with finite positive semidefinite quadratic forms. -/
structure BasedHermitianKernel (X : Type*) where
  base : X
  K : X → X → ℂ
  hermitian : ∀ x y : X, star (K y x) = K x y
  base_left : ∀ x : X, K base x = 0
  base_right : ∀ x : X, K x base = 0
  finitePSD : ∀ {n : ℕ} (x : Fin n → X) (c : Fin n → ℂ),
    0 ≤ (kernelQuadratic K x c).re

lemma hermitian_quadratic_isSelfAdjoint {n : Type*} [Fintype n] (M : Matrix n n ℂ)
    (hM : M.IsHermitian) (c : n → ℂ) :
    IsSelfAdjoint (star c ⬝ᵥ (M *ᵥ c)) := by
  rw [isSelfAdjoint_iff]
  calc
    star (star c ⬝ᵥ (M *ᵥ c)) = star (M *ᵥ c) ⬝ᵥ c := by
      simpa using (star_dotProduct (M *ᵥ c) c).symm
    _ = (star c ᵥ* Mᴴ) ⬝ᵥ c := by rw [star_mulVec]
    _ = star c ⬝ᵥ (Mᴴ *ᵥ c) := (dotProduct_mulVec (star c) Mᴴ c).symm
    _ = star c ⬝ᵥ (M *ᵥ c) := by rw [hM.eq]

/-- The finite sample Gram matrix of a based Hermitian kernel is Hermitian. -/
theorem gram_isHermitian {X : Type*} (H : BasedHermitianKernel X) {n : ℕ}
    (x : Fin n → X) :
    (kernelGram H.K x).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [kernelGram, H.hermitian]

/-- The finite sample Gram matrix of a based Hermitian kernel is positive semidefinite. -/
theorem gram_posSemidef {X : Type*} (H : BasedHermitianKernel X) {n : ℕ}
    (x : Fin n → X) :
    (kernelGram H.K x).PosSemidef := by
  refine ⟨gram_isHermitian H x, ?_⟩
  intro c
  exact (Complex.re_nonneg_iff_nonneg
    (hermitian_quadratic_isSelfAdjoint (kernelGram H.K x) (gram_isHermitian H x) c)).mp
    (by simpa [kernelQuadratic] using H.finitePSD x c)

/-- Finite Kolmogorov realization via Mathlib's PSD factorization. -/
theorem finite_realization {X : Type*} (H : BasedHermitianKernel X) {n : ℕ}
    (x : Fin n → X) :
    ∃ v : Fin n → EuclideanSpace ℂ (Fin n),
      ∀ i j : Fin n, @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (v i) (v j) =
        H.K (x i) (x j) := by
  classical
  obtain ⟨B, hB⟩ :=
    Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp (gram_posSemidef H x)
  let v : Fin n → EuclideanSpace ℂ (Fin n) :=
    fun i => WithLp.toLp 2 (fun k : Fin n => B k i)
  refine ⟨v, ?_⟩
  intro i j
  calc
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (v i) (v j)
        = (Bᴴ * B) i j := by
          simp [v, EuclideanSpace.inner_toLp_toLp, Matrix.mul_apply,
            Matrix.conjTranspose_apply, dotProduct, mul_comm]
    _ = H.K (x i) (x j) := by
      rw [← hB]
      rfl

/-- Packaged finite realization: PSD Gram plus realizing feature vectors. -/
theorem finite_realization_package {X : Type*} (H : BasedHermitianKernel X) {n : ℕ}
    (x : Fin n → X) :
    (kernelGram H.K x).PosSemidef ∧
      ∃ v : Fin n → EuclideanSpace ℂ (Fin n),
        ∀ i j : Fin n, @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (v i) (v j) =
          H.K (x i) (x j) := by
  exact ⟨gram_posSemidef H x, finite_realization H x⟩

/-- The feature-distance identity for any finite realization. -/
theorem feature_distance_identity {X : Type*} (H : BasedHermitianKernel X) {n : ℕ}
    (x : Fin n → X) (v : Fin n → EuclideanSpace ℂ (Fin n))
    (hreal :
      ∀ i j : Fin n, @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (v i) (v j) =
        H.K (x i) (x j))
    (i j : Fin n) :
    ‖v i - v j‖ ^ 2 =
      (H.K (x i) (x i)).re + (H.K (x j) (x j)).re -
        2 * (H.K (x i) (x j)).re := by
  calc
    ‖v i - v j‖ ^ 2 =
        ‖v i‖ ^ 2 - 2 * (inner ℂ (v i) (v j)).re + ‖v j‖ ^ 2 := by
      rw [@norm_sub_sq ℂ (EuclideanSpace ℂ (Fin n))]
      simp [RCLike.re_to_complex]
    _ =
        (inner ℂ (v i) (v i)).re - 2 * (inner ℂ (v i) (v j)).re +
          (inner ℂ (v j) (v j)).re := by
      rw [@norm_sq_eq_re_inner ℂ (EuclideanSpace ℂ (Fin n)),
        @norm_sq_eq_re_inner ℂ (EuclideanSpace ℂ (Fin n))]
      simp [RCLike.re_to_complex]
    _ =
        (H.K (x i) (x i)).re + (H.K (x j) (x j)).re -
          2 * (H.K (x i) (x j)).re := by
      rw [hreal i i, hreal i j, hreal j j]
      ring

private lemma euclidean_vector_kernel_finitePSD {m n : ℕ}
    (v : Fin n → EuclideanSpace ℂ (Fin m)) (c : Fin n → ℂ) :
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j * inner ℂ (v i) (v j)).re := by
  let z : EuclideanSpace ℂ (Fin m) := ∑ i : Fin n, c i • v i
  have hquad :
      (∑ i : Fin n, ∑ j : Fin n,
        star (c i) * c j * inner ℂ (v i) (v j)) = inner ℂ z z := by
    simp only [z, inner_sum, sum_inner, inner_smul_left, inner_smul_right]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    simp [mul_assoc, mul_comm]
  rw [hquad]
  rw [← RCLike.re_to_complex, ← norm_sq_eq_re_inner]
  exact sq_nonneg ‖z‖

private lemma euclidean_vector_kernel_matrixOrder_finitePSD {m n : ℕ}
    (v : Fin n → EuclideanSpace ℂ (Fin m)) (c : Fin n → ℂ) :
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      star (c i) * (inner ℂ (v i) (v j) * c j)).re := by
  have horder :
      (∑ i : Fin n, ∑ j : Fin n,
        star (c i) * (inner ℂ (v i) (v j) * c j)) =
        ∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * inner ℂ (v i) (v j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [horder]
  exact euclidean_vector_kernel_finitePSD v c

/-- Two-point nonzero feature fixture: the base maps to zero and the other point maps to `1`. -/
def twoPointFeature_fixture (x : Fin 2) : EuclideanSpace ℂ (Fin 1) :=
  if x = 0 then 0 else WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℂ))

/-- A nonzero two-point based-kernel fixture. -/
def twoPointKernel_fixture : BasedHermitianKernel (Fin 2) where
  base := 0
  K := fun x y => inner ℂ (twoPointFeature_fixture x) (twoPointFeature_fixture y)
  hermitian := by
    intro x y
    simp [inner_conj_symm]
  base_left := by
    intro x
    simp [twoPointFeature_fixture]
  base_right := by
    intro x
    simp [twoPointFeature_fixture]
  finitePSD := by
    intro n x c
    have hq :
        (kernelQuadratic
          (fun a b => inner ℂ (twoPointFeature_fixture a) (twoPointFeature_fixture b)) x c).re =
          (∑ i : Fin n, ∑ j : Fin n,
            star (c i) *
              (inner ℂ (twoPointFeature_fixture (x i)) (twoPointFeature_fixture (x j)) *
                c j)).re := by
      congr 1
      simp [kernelQuadratic, kernelGram, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [hq]
    exact euclidean_vector_kernel_matrixOrder_finitePSD
      (fun i : Fin n => twoPointFeature_fixture (x i)) c

/-- The two-point fixture takes value 1 at (1, 1). -/
theorem twoPointKernel_fixture_nonzero :
    twoPointKernel_fixture.K 1 1 = 1 := by
  simp [twoPointKernel_fixture, twoPointFeature_fixture, EuclideanSpace.inner_toLp_toLp,
    dotProduct]

#check BasedHermitianKernel
#check gram_isHermitian
#print axioms gram_isHermitian
#check gram_posSemidef
#print axioms gram_posSemidef
#check finite_realization
#print axioms finite_realization
#check finite_realization_package
#print axioms finite_realization_package
#check feature_distance_identity
#print axioms feature_distance_identity
#check twoPointKernel_fixture
#check twoPointKernel_fixture_nonzero
#print axioms twoPointKernel_fixture_nonzero

end

end OperatorKO7.RH.Screw.BasedKernel
