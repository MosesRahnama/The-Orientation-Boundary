import Mathlib

set_option autoImplicit false

/-!
# Local tomography selects the complex field at the dimension count (60.8b)

Section 60.8 as written claims the complex assignment is forced by offset
conservation and gauge covariance. It is not: `(1, n)` is Definition 60.7, and
neither offset conservation nor payload-gauge covariance mentions a field. What
DOES separate the real from the complex theory is Postulate 4 of Section 12,
local tomography: the state space of a composite is determined by the states of
its parts, so the real dimension of the joint state space must be the product of
the real dimensions of the factors.

This module proves the dimension arithmetic. Over the complex field the real
dimension of the space of Hermitian `n` by `n` matrices is `n ^ 2` and that
count is multiplicative. Over the real field the analogous space is the
symmetric matrices, of real dimension `n (n + 1) / 2`, and that count is NOT
multiplicative: the joint space is strictly larger than the product, starting at
two by two, where it is `10` against `9`. The real theory therefore fails local
tomography, and the complex theory does not.

Both counts are proved to BE the real dimensions of the matrix spaces they
count. Mathlib carries no lemma for either, so this module supplies them.

The complex count comes from the Cartesian decomposition: over a complex star
module the real-linear map `a ↦ (ℜ a, ℑ a)` is an equivalence onto pairs of
self-adjoint elements, so the whole space has twice the real dimension of its
self-adjoint part. Applied to the `n` by `n` complex matrices, whose real
dimension is `2 n ^ 2` by the tower `ℝ ≤ ℂ`, this gives `n ^ 2`.

The real count comes from a bijection instead: a real symmetric matrix is
exactly a function on unordered pairs of indices, so the symmetric matrices are
real-linearly equivalent to `Sym2 (Fin n) → ℝ`, whose dimension is the
cardinality of `Sym2 (Fin n)`, namely `(n + 1).choose 2`.

Relation: real dimensions of the two matrix spaces.
Property: multiplicativity and its failure.
Trust: Mathlib linear algebra over kernel-only arithmetic.
Scope: finite dimensions; `Fin n` index types.
-/

namespace OperatorKO7.Meta.UUET.Quantum.LocalTomographyDimension

/-! ## The two dimension counts -/

/--
Proves: nothing on its own. The real dimension count of the Hermitian `n` by `n`
complex matrices: `n ^ 2`. This is the standard count of real parameters in a
complex quantum state space of dimension `n` before normalization.

That this equals `Module.finrank ℝ (selfAdjoint (Matrix (Fin n) (Fin n) ℂ))`
is proved below as `finrank_hermitian_eq_hermitianRealDim`.

Trust: kernel-only.
Scope: a natural-number counting function.
-/
def hermitianRealDim (n : ℕ) : ℕ := n ^ 2

/--
Proves: nothing on its own. The real dimension count of the symmetric `n` by `n`
real matrices: `n (n + 1) / 2`. This is the real-quantum-theory analogue of
`hermitianRealDim`.

That this equals the finrank of the real symmetric matrices is proved below as
`finrank_symmetric_eq_symmetricRealDim`.

Trust: kernel-only.
Scope: a natural-number counting function; the division is exact because
`n * (n + 1)` is always even.
-/
def symmetricRealDim (n : ℕ) : ℕ := n * (n + 1) / 2

/--
Proves: the symmetric count is exact: twice it is `n (n + 1)`. The truncating
natural division loses nothing because consecutive naturals have an even
product.

Trust: kernel-only.
Scope: all naturals.
-/
theorem symmetricRealDim_two_mul (n : ℕ) :
    2 * symmetricRealDim n = n * (n + 1) := by
  have hdvd : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
  unfold symmetricRealDim
  omega

/-! ## The complex count is multiplicative -/

/--
Proves: Section 60.8b, the positive half. The Hermitian real-dimension count is
multiplicative: the count for a composite of dimensions `d1` and `d2` equals the
product of the counts. This is local tomography at the level of the dimension
count.

Does not prove: that the complex quantum state space satisfies local tomography
as a statement about states. That is Postulate 4 of Section 12, recorded as
ESTABLISHED.

Relation: natural-number arithmetic.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the counting function; all dimension pairs.
-/
theorem complex_joint_dim_eq_product (d1 d2 : ℕ) :
    hermitianRealDim (d1 * d2) = hermitianRealDim d1 * hermitianRealDim d2 := by
  unfold hermitianRealDim
  ring

/-! ## The real count is not multiplicative -/

/--
Proves: Section 60.8b, the refuting half at the smallest case. Two real qubits
have a joint symmetric dimension count of `10`, while the product of the factor
counts is `9`. The real theory carries one real parameter that no pair of local
measurements determines.

Relation: natural-number arithmetic.
Trust: kernel-only.
Scope: the two by two case.
-/
theorem real_joint_dim_ne_product_two_two :
    symmetricRealDim 4 ≠ symmetricRealDim 2 * symmetricRealDim 2 := by
  decide

/-- The two by two counts, made explicit: `10` against `9`. -/
theorem real_joint_dim_two_two_values :
    symmetricRealDim 4 = 10 ∧ symmetricRealDim 2 * symmetricRealDim 2 = 9 := by
  constructor <;> decide

/--
Proves: Section 60.8b in general. For every pair of dimensions at least two, the
symmetric real-dimension count of the composite is STRICTLY GREATER than the
product of the factor counts. The gap is `d1 d2 (d1 - 1) (d2 - 1)` after
clearing the factor four, so it grows with the dimensions.

Does not prove: that real quantum theory is empirically refuted. That is the
2021 Nature result and its experimental tests, recorded as ESTABLISHED.

Relation: natural-number arithmetic.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: dimensions at least two; the counting functions.
-/
theorem real_joint_dim_gt_product {d1 d2 : ℕ} (h1 : 2 ≤ d1) (h2 : 2 ≤ d2) :
    symmetricRealDim d1 * symmetricRealDim d2 < symmetricRealDim (d1 * d2) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h1
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h2
  have e1 := symmetricRealDim_two_mul (2 + a)
  have e2 := symmetricRealDim_two_mul (2 + b)
  have e3 := symmetricRealDim_two_mul ((2 + a) * (2 + b))
  have key :
      4 * (symmetricRealDim (2 + a) * symmetricRealDim (2 + b))
        < 4 * symmetricRealDim ((2 + a) * (2 + b)) := by
    have l : 4 * (symmetricRealDim (2 + a) * symmetricRealDim (2 + b))
        = (2 * symmetricRealDim (2 + a)) * (2 * symmetricRealDim (2 + b)) := by
      ring
    have r : 4 * symmetricRealDim ((2 + a) * (2 + b))
        = 2 * (2 * symmetricRealDim ((2 + a) * (2 + b))) := by ring
    rw [l, r, e1, e2, e3]
    -- the exact gap: `x y (x - 1) (y - 1)` with `x = 2 + a` and `y = 2 + b`
    have ident :
        2 * ((2 + a) * (2 + b) * ((2 + a) * (2 + b) + 1))
          = (2 + a) * (2 + a + 1) * ((2 + b) * (2 + b + 1))
            + (2 + a) * (2 + b) * (1 + a) * (1 + b) := by ring
    rw [ident]
    exact Nat.lt_add_of_pos_right (by positivity)
  exact Nat.lt_of_mul_lt_mul_left key

/-! ## The counts are the dimensions

Everything above is arithmetic on two natural-number functions. This section
proves those functions compute the real dimensions of the two matrix spaces, so
the results above are statements about state spaces and not about counters. -/

open ComplexStarModule in
/--
Proves: the Cartesian decomposition of a complex star module as a real-linear
equivalence. Every element is `ℜ a + i ℑ a` with both parts self-adjoint, and
the assignment `a ↦ (ℜ a, ℑ a)` is a real-linear bijection onto pairs.

Relation: real-linear equivalence.
Trust: Mathlib `realPart`, `imaginaryPart` and their algebra.
Scope: any complex star module.
-/
noncomputable def selfAdjointPairEquiv (A : Type) [AddCommGroup A] [Module ℂ A]
    [StarAddMonoid A] [StarModule ℂ A] : A ≃ₗ[ℝ] (selfAdjoint A × selfAdjoint A) where
  toFun a := (realPart a, imaginaryPart a)
  map_add' a b := by simp
  map_smul' r a := by simp
  invFun p := (p.1 : A) + Complex.I • (p.2 : A)
  left_inv a := realPart_add_I_smul_imaginaryPart a
  right_inv := by
    rintro ⟨x, y⟩
    have hx : IsSelfAdjoint (x : A) := x.2
    have hy : IsSelfAdjoint (y : A) := y.2
    have h1 : realPart ((x : A) + Complex.I • (y : A)) = x := by
      apply Subtype.ext
      rw [map_add, realPart_I_smul]
      simp [hx.coe_realPart, hy.imaginaryPart]
    have h2 : imaginaryPart ((x : A) + Complex.I • (y : A)) = y := by
      apply Subtype.ext
      rw [map_add, imaginaryPart_I_smul]
      simp [hy.coe_realPart, hx.imaginaryPart]
    exact Prod.ext h1 h2

/--
Proves: twice the real dimension of the self-adjoint part is the real dimension
of the whole complex star module. This is the dimension shadow of the Cartesian
decomposition.

Relation: dimension identity.
Trust: Mathlib finrank of a product.
Scope: finite-dimensional complex star modules.
-/
theorem two_mul_finrank_selfAdjoint (A : Type) [AddCommGroup A] [Module ℂ A]
    [StarAddMonoid A] [StarModule ℂ A] [FiniteDimensional ℝ A] :
    2 * Module.finrank ℝ (selfAdjoint A) = Module.finrank ℝ A := by
  have hfd : FiniteDimensional ℝ (selfAdjoint A × selfAdjoint A) :=
    (selfAdjointPairEquiv A).finiteDimensional
  have hfst : FiniteDimensional ℝ (selfAdjoint A) :=
    Module.Finite.of_surjective (LinearMap.fst ℝ (selfAdjoint A) (selfAdjoint A))
      Prod.fst_surjective
  have h := (selfAdjointPairEquiv A).finrank_eq
  rw [Module.finrank_prod] at h
  omega

/--
Proves: the self-adjoint complex matrices are the Hermitian ones. The membership
predicate and `Matrix.IsHermitian` agree by unfolding `star` to the conjugate
transpose.

Relation: predicate identity.
Trust: kernel-only after `Matrix.star_eq_conjTranspose`.
Scope: square complex matrices over any index type.
-/
theorem mem_selfAdjoint_matrix_complex_iff_isHermitian {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) :
    M ∈ selfAdjoint (Matrix (Fin n) (Fin n) ℂ) ↔ M.IsHermitian := by
  rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
  rfl

/--
Proves: Section 60.8b, the complex dimension count identified with the actual
dimension. The real dimension of the space of Hermitian `n` by `n` complex
matrices is `hermitianRealDim n = n ^ 2`.

The proof runs the Cartesian decomposition against the field tower: the complex
matrices have real dimension `2 n ^ 2`, because they have complex dimension
`n ^ 2` and `ℂ` has real dimension `2`; the decomposition halves it.

Relation: dimension identity.
Closure: not applicable.
Strategy: not applicable.
Trust: Mathlib linear algebra.
Scope: all finite `n`.
-/
theorem finrank_hermitian_eq_hermitianRealDim (n : ℕ) :
    Module.finrank ℝ (selfAdjoint (Matrix (Fin n) (Fin n) ℂ)) = hermitianRealDim n := by
  have hC : Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) = n * n := by
    simp [Module.finrank_matrix]
  have hR : Module.finrank ℝ (Matrix (Fin n) (Fin n) ℂ) = 2 * (n * n) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (Matrix (Fin n) (Fin n) ℂ),
      Complex.finrank_real_complex, hC]
  have h2 := two_mul_finrank_selfAdjoint (Matrix (Fin n) (Fin n) ℂ)
  rw [hR] at h2
  have h3 : Module.finrank ℝ (selfAdjoint (Matrix (Fin n) (Fin n) ℂ)) = n * n := by omega
  rw [h3, hermitianRealDim, sq]

/--
Proves: over the reals the self-adjoint matrices are the symmetric ones, because
`star` on `ℝ` is the identity and the conjugate transpose collapses to the
transpose.

Relation: predicate identity.
Trust: kernel-only.
Scope: square real matrices.
-/
theorem mem_selfAdjoint_matrix_real_iff_isSymm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    M ∈ selfAdjoint (Matrix (Fin n) (Fin n) ℝ) ↔ M.IsSymm := by
  rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
  constructor
  · intro h; ext i j
    have := congrArg (fun A => A i j) h
    simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using this
  · intro h; ext i j
    have := congrArg (fun A => A i j) h
    simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using this

/--
Proves: a function on unordered index pairs is a real symmetric matrix, real
linearly. The unordered pair carries exactly the symmetry constraint, so this
map is the whole content of the symmetric-dimension count.

Relation: real-linear map.
Trust: kernel-only after `Sym2.eq_swap`.
Scope: `Fin n` index type.
-/
def sym2ToSymmMatrix (n : ℕ) :
    (Sym2 (Fin n) → ℝ) →ₗ[ℝ] selfAdjoint (Matrix (Fin n) (Fin n) ℝ) where
  toFun g := ⟨Matrix.of fun i j => g s(i, j), by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    ext i j
    simp [Matrix.conjTranspose_apply, Sym2.eq_swap]⟩
  map_add' g h := by apply Subtype.ext; ext i j; simp
  map_smul' r g := by apply Subtype.ext; ext i j; simp

/--
Proves: that map is a bijection. Injectivity because every unordered pair is
`s(i, j)` for some ordered pair; surjectivity because a symmetric matrix lifts
through `Sym2.lift`.

Relation: bijectivity.
Trust: Mathlib `Sym2` induction and lifting.
Scope: `Fin n` index type.
-/
theorem sym2ToSymmMatrix_bijective (n : ℕ) : Function.Bijective (sym2ToSymmMatrix n) := by
  constructor
  · intro g h hgh
    have hco : ((sym2ToSymmMatrix n g : selfAdjoint (Matrix (Fin n) (Fin n) ℝ))
        : Matrix (Fin n) (Fin n) ℝ)
        = ((sym2ToSymmMatrix n h : selfAdjoint (Matrix (Fin n) (Fin n) ℝ))
        : Matrix (Fin n) (Fin n) ℝ) := Subtype.ext_iff.mp hgh
    have hc : ∀ i j : Fin n, g s(i, j) = h s(i, j) := by
      intro i j
      have := congrFun (congrFun hco i) j
      simpa [sym2ToSymmMatrix] using this
    funext z
    induction z using Sym2.ind with
    | _ i j => exact hc i j
  · rintro ⟨M, hM⟩
    have hsymm : ∀ a b : Fin n, M a b = M b a := by
      intro a b
      have h := (mem_selfAdjoint_matrix_real_iff_isSymm M).mp hM
      have := congrArg (fun A => A a b) h
      simpa [Matrix.transpose_apply] using this.symm
    refine ⟨Sym2.lift ⟨fun a b => M a b, fun a b => hsymm a b⟩, ?_⟩
    apply Subtype.ext
    ext i j
    simp [sym2ToSymmMatrix]

/--
Proves: Section 60.8b, the real dimension count identified with the actual
dimension. The real dimension of the space of symmetric `n` by `n` real matrices
is `symmetricRealDim n = n (n + 1) / 2`.

The proof transports the dimension across the bijection above and reads off the
cardinality of `Sym2 (Fin n)`, which Mathlib gives as `(n + 1).choose 2`.

Relation: dimension identity.
Closure: not applicable.
Strategy: not applicable.
Trust: Mathlib linear algebra and `Sym2.card`.
Scope: all finite `n`.
-/
theorem finrank_symmetric_eq_symmetricRealDim (n : ℕ) :
    Module.finrank ℝ (selfAdjoint (Matrix (Fin n) (Fin n) ℝ)) = symmetricRealDim n := by
  have he : (Sym2 (Fin n) → ℝ) ≃ₗ[ℝ] selfAdjoint (Matrix (Fin n) (Fin n) ℝ) :=
    LinearEquiv.ofBijective (sym2ToSymmMatrix n) (sym2ToSymmMatrix_bijective n)
  have h1 : Module.finrank ℝ (selfAdjoint (Matrix (Fin n) (Fin n) ℝ))
      = Fintype.card (Sym2 (Fin n)) := by
    rw [← he.finrank_eq, Module.finrank_pi ℝ]
  rw [h1, Sym2.card, Nat.choose_two_right, symmetricRealDim]
  simp [Fintype.card_fin, Nat.mul_comm]

/-! ## Local tomography, stated about the state spaces -/

/--
Proves: Section 60.8b, the positive half, as a statement about matrix spaces.
The real dimension of the Hermitian matrices on a composite of dimensions `d1`
and `d2` is the product of the real dimensions of the Hermitian matrices on the
factors. The complex theory satisfies local tomography at the dimension count.

Does not prove: that complex quantum theory satisfies local tomography as a
statement about states. That is Postulate 4 of Section 12, recorded as
ESTABLISHED.

Relation: dimension identity.
Trust: Mathlib linear algebra.
Scope: all dimension pairs.
-/
theorem complex_joint_finrank_eq_product (d1 d2 : ℕ) :
    Module.finrank ℝ (selfAdjoint (Matrix (Fin (d1 * d2)) (Fin (d1 * d2)) ℂ))
      = Module.finrank ℝ (selfAdjoint (Matrix (Fin d1) (Fin d1) ℂ))
        * Module.finrank ℝ (selfAdjoint (Matrix (Fin d2) (Fin d2) ℂ)) := by
  rw [finrank_hermitian_eq_hermitianRealDim, finrank_hermitian_eq_hermitianRealDim,
    finrank_hermitian_eq_hermitianRealDim]
  exact complex_joint_dim_eq_product d1 d2

/--
Proves: Section 60.8b, the refuting half, as a statement about matrix spaces.
For dimensions at least two the real dimension of the symmetric matrices on the
composite STRICTLY EXCEEDS the product of the factor dimensions. The real theory
carries joint parameters that no pair of local state spaces determines, so it
fails local tomography.

Does not prove: that real quantum theory is empirically refuted. That is the
2021 Nature result and its experimental tests, recorded as ESTABLISHED.

Relation: strict dimension inequality.
Trust: Mathlib linear algebra over kernel-only arithmetic.
Scope: dimensions at least two.
-/
theorem real_joint_finrank_gt_product {d1 d2 : ℕ} (h1 : 2 ≤ d1) (h2 : 2 ≤ d2) :
    Module.finrank ℝ (selfAdjoint (Matrix (Fin d1) (Fin d1) ℝ))
        * Module.finrank ℝ (selfAdjoint (Matrix (Fin d2) (Fin d2) ℝ))
      < Module.finrank ℝ (selfAdjoint (Matrix (Fin (d1 * d2)) (Fin (d1 * d2)) ℝ)) := by
  rw [finrank_symmetric_eq_symmetricRealDim, finrank_symmetric_eq_symmetricRealDim,
    finrank_symmetric_eq_symmetricRealDim]
  exact real_joint_dim_gt_product h1 h2

/--
Proves: the two-qubit case as a dimension statement. Two real qubits have a
joint symmetric space of real dimension `10` while the product of the factor
dimensions is `9`. One real parameter of the joint space is invisible to every
pair of local state spaces.

Relation: finite dimension fixture.
Trust: Mathlib linear algebra.
Scope: the two by two case.
-/
theorem real_joint_finrank_two_two_values :
    Module.finrank ℝ (selfAdjoint (Matrix (Fin 4) (Fin 4) ℝ)) = 10
      ∧ Module.finrank ℝ (selfAdjoint (Matrix (Fin 2) (Fin 2) ℝ))
          * Module.finrank ℝ (selfAdjoint (Matrix (Fin 2) (Fin 2) ℝ)) = 9 := by
  rw [finrank_symmetric_eq_symmetricRealDim, finrank_symmetric_eq_symmetricRealDim]
  exact ⟨by decide, by decide⟩

/-! ## Non-vacuity -/

/--
Proves: both counting facts are non-vacuous at concrete dimensions. The complex
count is multiplicative at `(2, 2)` with value `16 = 4 * 4`, and the real count
is strictly larger than the product at `(2, 2)` with `10 > 9`.

Relation: finite fixtures.
Trust: kernel-only.
Scope: the two by two case.
-/
theorem localTomographyDimension_nonvacuous :
    hermitianRealDim 4 = 16
      ∧ hermitianRealDim 2 * hermitianRealDim 2 = 16
      ∧ symmetricRealDim 2 * symmetricRealDim 2 < symmetricRealDim 4
      ∧ Module.finrank ℝ (selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) = 4
      ∧ Module.finrank ℝ (selfAdjoint (Matrix (Fin 2) (Fin 2) ℝ)) = 3 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · have h := real_joint_dim_gt_product (d1 := 2) (d2 := 2) (by omega) (by omega)
    simpa using h
  · rw [finrank_hermitian_eq_hermitianRealDim]; decide
  · rw [finrank_symmetric_eq_symmetricRealDim]; decide

/-! Imported NameGate and TypeGate. -/
#check @Nat.even_mul_succ_self
#check @Nat.lt_of_mul_lt_mul_left
#check @selfAdjoint
#check @Module.finrank
#check @Sym2.card
#check @Sym2.lift
#check @Module.finrank_matrix
#check @Module.finrank_pi
#check @Module.finrank_mul_finrank
#check @Complex.finrank_real_complex
#check @realPart_add_I_smul_imaginaryPart

#check @hermitianRealDim
#check @symmetricRealDim
#check @symmetricRealDim_two_mul
#check @complex_joint_dim_eq_product
#check @real_joint_dim_ne_product_two_two
#check @real_joint_dim_two_two_values
#check @real_joint_dim_gt_product
#check @selfAdjointPairEquiv
#check @two_mul_finrank_selfAdjoint
#check @mem_selfAdjoint_matrix_complex_iff_isHermitian
#check @finrank_hermitian_eq_hermitianRealDim
#check @mem_selfAdjoint_matrix_real_iff_isSymm
#check @sym2ToSymmMatrix
#check @sym2ToSymmMatrix_bijective
#check @finrank_symmetric_eq_symmetricRealDim
#check @complex_joint_finrank_eq_product
#check @real_joint_finrank_gt_product
#check @real_joint_finrank_two_two_values
#check @localTomographyDimension_nonvacuous

#print axioms symmetricRealDim_two_mul
#print axioms complex_joint_dim_eq_product
#print axioms real_joint_dim_ne_product_two_two
#print axioms real_joint_dim_two_two_values
#print axioms real_joint_dim_gt_product
#print axioms two_mul_finrank_selfAdjoint
#print axioms mem_selfAdjoint_matrix_complex_iff_isHermitian
#print axioms finrank_hermitian_eq_hermitianRealDim
#print axioms mem_selfAdjoint_matrix_real_iff_isSymm
#print axioms sym2ToSymmMatrix_bijective
#print axioms finrank_symmetric_eq_symmetricRealDim
#print axioms complex_joint_finrank_eq_product
#print axioms real_joint_finrank_gt_product
#print axioms real_joint_finrank_two_two_values
#print axioms localTomographyDimension_nonvacuous

end OperatorKO7.Meta.UUET.Quantum.LocalTomographyDimension
