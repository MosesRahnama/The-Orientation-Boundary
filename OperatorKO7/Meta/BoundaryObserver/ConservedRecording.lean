import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Conserved quantities and recording unitaries

Manuscript: Theorem `thm:way` of the Observation-Boundary Principle.

A unitary `U` on `S ⊗ A` that commutes with the additive quantity `L = L_S ⊗ I + I ⊗ L_A` and
writes the outcome of an orthogonal projector family `P_k` into orthonormal vectors `a_k` of `A`,
`U (ψ ⊗ a₀) = ∑ₖ Pₖ ψ ⊗ aₖ` for every `ψ`, forces `L_S` to commute with every `P_k`: the theorem
of Wigner, Araki and Yanase. The proof never uses that `L` is Hermitian, so the Lean statement
carries no Hermiticity hypothesis on `L_S` or `L_A`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Kronecker BigOperators Matrix

namespace OperatorKO7.Meta.BoundaryObserver.ConservedRecording

variable {ι κ K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype K] [DecidableEq K]

/-- The additive quantity `L_S ⊗ I + I ⊗ L_A` on the composite system. -/
def additive (LS : Matrix ι ι ℂ) (LA : Matrix κ κ ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  LS ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ LA

/-- The matrix of the map `ψ ↦ (X ψ) ⊗ b`. -/
def tensorCol (X : Matrix ι ι ℂ) (b : κ → ℂ) : Matrix (ι × κ) ι ℂ :=
  fun p j => X p.1 j * b p.2

theorem tensorCol_zero (b : κ → ℂ) : tensorCol (0 : Matrix ι ι ℂ) b = 0 := by
  ext p j
  simp [tensorCol]

theorem tensorCol_mul (X Y : Matrix ι ι ℂ) (b : κ → ℂ) :
    tensorCol X b * Y = tensorCol (X * Y) b := by
  ext p j
  simp only [Matrix.mul_apply, tensorCol, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem tensorCol_one_mulVec (b : κ → ℂ) (ψ : ι → ℂ) :
    tensorCol (1 : Matrix ι ι ℂ) b *ᵥ ψ = fun p => ψ p.1 * b p.2 := by
  funext p
  simp [Matrix.mulVec, dotProduct, tensorCol, Matrix.one_apply, mul_comm]

theorem sum_tensorCol_mulVec (X : K → Matrix ι ι ℂ) (b : K → κ → ℂ) (ψ : ι → ℂ) :
    (∑ k, tensorCol (X k) (b k)) *ᵥ ψ = fun p => ∑ k, (X k *ᵥ ψ) p.1 * b k p.2 := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, tensorCol, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

theorem kron_one_mul_tensorCol (A Y : Matrix ι ι ℂ) (c : κ → ℂ) :
    (A ⊗ₖ (1 : Matrix κ κ ℂ)) * tensorCol Y c = tensorCol (A * Y) c := by
  ext ⟨i, a⟩ j
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply,
    tensorCol, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [mul_ite, ite_mul, Finset.sum_ite_eq, mul_assoc]

theorem one_kron_mul_tensorCol (B : Matrix κ κ ℂ) (Y : Matrix ι ι ℂ) (c : κ → ℂ) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ B) * tensorCol Y c = tensorCol Y (B *ᵥ c) := by
  ext ⟨i, a⟩ j
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply,
    tensorCol, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp only [↓reduceIte, one_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem tensorCol_conjTranspose_mul (X Z : Matrix ι ι ℂ) (b d : κ → ℂ) :
    (tensorCol X b)ᴴ * tensorCol Z d = (star b ⬝ᵥ d) • (Xᴴ * Z) := by
  ext j j'
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply, tensorCol,
    Matrix.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply, star_mul']
  conv_rhs => rw [Finset.sum_mul_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The quadratic form of the additive quantity between two vectors of the form `Xψ ⊗ b`. -/
theorem sandwich (LS X Y : Matrix ι ι ℂ) (LA : Matrix κ κ ℂ) (b c : κ → ℂ) :
    (tensorCol X b)ᴴ * additive LS LA * tensorCol Y c =
      (star b ⬝ᵥ c) • (Xᴴ * LS * Y) + (star b ⬝ᵥ (LA *ᵥ c)) • (Xᴴ * Y) := by
  rw [additive, Matrix.mul_assoc, Matrix.add_mul, kron_one_mul_tensorCol, one_kron_mul_tensorCol,
    Matrix.mul_add, tensorCol_conjTranspose_mul, tensorCol_conjTranspose_mul, Matrix.mul_assoc]

/-- The vector form of the recording hypothesis is the matrix identity
`U (I ⊗ a₀) = ∑ₖ Pₖ ⊗ aₖ`. -/
theorem recording_matrix (U : Matrix (ι × κ) (ι × κ) ℂ) (P : K → Matrix ι ι ℂ) (a0 : κ → ℂ)
    (a : K → κ → ℂ)
    (hrec : ∀ ψ : ι → ℂ,
      U *ᵥ (fun p => ψ p.1 * a0 p.2) = fun p => ∑ k, (P k *ᵥ ψ) p.1 * a k p.2) :
    U * tensorCol (1 : Matrix ι ι ℂ) a0 = ∑ k, tensorCol (P k) (a k) := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun ψ => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, tensorCol_one_mulVec, hrec,
    sum_tensorCol_mulVec]

/-- **Wigner, Araki and Yanase.** A unitary that commutes with `L_S ⊗ I + I ⊗ L_A` and writes the
outcome of the orthogonal projectors `P_k` into orthonormal vectors `a_k` makes `L_S` commute with
every `P_k`. -/
theorem wigner_araki_yanase (LS : Matrix ι ι ℂ) (LA : Matrix κ κ ℂ)
    (U : Matrix (ι × κ) (ι × κ) ℂ) (hU : U ∈ Matrix.unitaryGroup (ι × κ) ℂ)
    (hcomm : U * additive LS LA = additive LS LA * U)
    (P : K → Matrix ι ι ℂ) (hPh : ∀ k, (P k)ᴴ = P k)
    (hPP : ∀ k l, P k * P l = if k = l then P k else 0) (hPsum : ∑ k, P k = 1)
    (a0 : κ → ℂ) (a : K → κ → ℂ) (ha0 : star a0 ⬝ᵥ a0 = 1)
    (ha : ∀ k l, star (a k) ⬝ᵥ a l = if k = l then 1 else 0)
    (hrec : ∀ ψ : ι → ℂ,
      U *ᵥ (fun p => ψ p.1 * a0 p.2) = fun p => ∑ k, (P k *ᵥ ψ) p.1 * a k p.2)
    (k : K) : LS * P k = P k * LS := by
  have hUV := recording_matrix U P a0 a hrec
  have hUU : Uᴴ * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU
  -- conservation carries the quadratic form of `L` along `U`
  have hcons : (∑ k, tensorCol (P k) (a k))ᴴ * additive LS LA * (∑ k, tensorCol (P k) (a k)) =
      (tensorCol (1 : Matrix ι ι ℂ) a0)ᴴ * additive LS LA * tensorCol (1 : Matrix ι ι ℂ) a0 := by
    rw [← hUV, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (additive LS LA) U, ← hcomm, Matrix.mul_assoc U (additive LS LA),
      ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul]
  have hV : (tensorCol (1 : Matrix ι ι ℂ) a0)ᴴ * additive LS LA * tensorCol (1 : Matrix ι ι ℂ) a0 =
      LS + (star a0 ⬝ᵥ (LA *ᵥ a0)) • 1 := by
    rw [sandwich, ha0, one_smul]
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hWP : ∀ n, (∑ k, tensorCol (P k) (a k)) * P n = tensorCol (P n) (a n) := by
    intro n
    rw [Matrix.sum_mul, Finset.sum_eq_single n]
    · rw [tensorCol_mul, hPP, if_pos rfl]
    · intro m _ hm
      rw [tensorCol_mul, hPP, if_neg hm, tensorCol_zero]
    · intro h
      exact absurd (Finset.mem_univ n) h
  -- `L_S` has no entries between different ranges of the projectors
  have hoff : ∀ m n, m ≠ n → P m * LS * P n = 0 := by
    intro m n hmn
    have h1 : P m * ((∑ k, tensorCol (P k) (a k))ᴴ * additive LS LA *
        (∑ k, tensorCol (P k) (a k))) * P n =
        P m * (LS + (star a0 ⬝ᵥ (LA *ᵥ a0)) • 1) * P n := by
      rw [hcons, hV]
    have h2 : P m * ((∑ k, tensorCol (P k) (a k))ᴴ * additive LS LA *
        (∑ k, tensorCol (P k) (a k))) * P n = 0 := by
      calc _ = ((∑ k, tensorCol (P k) (a k)) * P m)ᴴ * additive LS LA *
            ((∑ k, tensorCol (P k) (a k)) * P n) := by
            rw [Matrix.conjTranspose_mul, hPh]
            simp only [Matrix.mul_assoc]
        _ = 0 := by
            rw [hWP, hWP, sandwich, ha, if_neg hmn, zero_smul, zero_add, hPh, hPP, if_neg hmn,
              smul_zero]
    rw [h2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hPP, if_neg hmn, smul_zero, add_zero] at h1
    exact h1.symm
  calc LS * P k = (∑ m, P m) * LS * P k := by rw [hPsum, Matrix.one_mul]
    _ = ∑ m, P m * LS * P k := by rw [Finset.sum_mul, Finset.sum_mul]
    _ = P k * LS * P k :=
        Finset.sum_eq_single k (fun m _ hm => hoff m k hm)
          (fun h => absurd (Finset.mem_univ k) h)
    _ = ∑ m, P k * LS * P m :=
        (Finset.sum_eq_single k (fun m _ hm => hoff k m (Ne.symm hm))
          (fun h => absurd (Finset.mem_univ k) h)).symm
    _ = P k * LS * ∑ m, P m := by rw [Finset.mul_sum]
    _ = P k * LS := by rw [hPsum, Matrix.mul_one]

/-- The conserved part `L_S` commutes with the recorded observable `A_S = ∑ₖ λₖ Pₖ`. -/
theorem wigner_araki_yanase_observable (LS : Matrix ι ι ℂ) (LA : Matrix κ κ ℂ)
    (U : Matrix (ι × κ) (ι × κ) ℂ) (hU : U ∈ Matrix.unitaryGroup (ι × κ) ℂ)
    (hcomm : U * additive LS LA = additive LS LA * U)
    (P : K → Matrix ι ι ℂ) (hPh : ∀ k, (P k)ᴴ = P k)
    (hPP : ∀ k l, P k * P l = if k = l then P k else 0) (hPsum : ∑ k, P k = 1)
    (a0 : κ → ℂ) (a : K → κ → ℂ) (ha0 : star a0 ⬝ᵥ a0 = 1)
    (ha : ∀ k l, star (a k) ⬝ᵥ a l = if k = l then 1 else 0)
    (hrec : ∀ ψ : ι → ℂ,
      U *ᵥ (fun p => ψ p.1 * a0 p.2) = fun p => ∑ k, (P k *ᵥ ψ) p.1 * a k p.2)
    (lam : K → ℂ) : LS * (∑ k, lam k • P k) = (∑ k, lam k • P k) * LS := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul,
    wigner_araki_yanase LS LA U hU hcomm P hPh hPP hPsum a0 a ha0 ha hrec k]

/-- `L_S` maps the range of every recorded projector into itself: a quantity conserved by the
recording unitary preserves every eigenspace of the recorded observable. -/
theorem wigner_araki_yanase_range (LS : Matrix ι ι ℂ) (LA : Matrix κ κ ℂ)
    (U : Matrix (ι × κ) (ι × κ) ℂ) (hU : U ∈ Matrix.unitaryGroup (ι × κ) ℂ)
    (hcomm : U * additive LS LA = additive LS LA * U)
    (P : K → Matrix ι ι ℂ) (hPh : ∀ k, (P k)ᴴ = P k)
    (hPP : ∀ k l, P k * P l = if k = l then P k else 0) (hPsum : ∑ k, P k = 1)
    (a0 : κ → ℂ) (a : K → κ → ℂ) (ha0 : star a0 ⬝ᵥ a0 = 1)
    (ha : ∀ k l, star (a k) ⬝ᵥ a l = if k = l then 1 else 0)
    (hrec : ∀ ψ : ι → ℂ,
      U *ᵥ (fun p => ψ p.1 * a0 p.2) = fun p => ∑ k, (P k *ᵥ ψ) p.1 * a k p.2)
    (k : K) (ψ : ι → ℂ) (hψ : P k *ᵥ ψ = ψ) : P k *ᵥ (LS *ᵥ ψ) = LS *ᵥ ψ := by
  rw [Matrix.mulVec_mulVec,
    ← wigner_araki_yanase LS LA U hU hcomm P hPh hPP hPsum a0 a ha0 ha hrec k,
    ← Matrix.mulVec_mulVec, hψ]

end OperatorKO7.Meta.BoundaryObserver.ConservedRecording
