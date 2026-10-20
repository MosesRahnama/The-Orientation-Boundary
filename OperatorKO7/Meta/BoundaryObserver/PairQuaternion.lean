import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

set_option autoImplicit false

open scoped Quaternion BigOperators TensorProduct

namespace OperatorKO7.Meta.BoundaryObserver.PairQuaternion

noncomputable section

/-!
The E1 dimension unit constructs the actual real spaces of quaternionic
Hermitian matrices. Its coordinate equivalence records a real diagonal
and independent quaternion entries strictly above that diagonal.

The dimension results have no caller assumptions.

PREMISE_ORIGIN_AUDIT
The Hermitian membership evidence is DERIVED_FROM_CERTIFIED_STRUCTURE
through the subtype carrier.
The reconstruction and inverse identities are INDEPENDENTLY_PROVED
within this source candidate.
The quaternion dimension and finrank transport are
DERIVED_FROM_CERTIFIED_STRUCTURE through pinned Mathlib declarations.
The branch inequalities are ORIGINAL_FINAL_ASSUMPTION within the
corresponding helper statements and are discharged in their applications.

HONESTY_STATUS=SOURCE_CANDIDATE_NOT_KERNEL_VALIDATED
-/

/-- The matrix carrier uses Mathlib quaternions over the reals. -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℍ[ℝ]

/-- The Hermitian matrices form a real submodule of the matrix carrier. -/
def hermitianSubmodule (n : ℕ) : Submodule ℝ (Mat n) where
  carrier := {A | A.IsHermitian}
  zero_mem' := Matrix.isHermitian_zero
  add_mem' := by
    intro A B hA hB
    exact Matrix.IsHermitian.add hA hB
  smul_mem' := by
    intro r A hA
    change A.IsHermitian at hA
    change (r • A).IsHermitian
    apply Matrix.IsHermitian.ext
    intro i j
    change star (r • A j i) = r • A i j
    rw [Quaternion.star_smul, hA.apply i j]

/-- The Hermitian carrier inherits its real vector space structure. -/
abbrev Hermitian (n : ℕ) : Type := ↥(hermitianSubmodule n)

/-- The upper indices select each off-diagonal pair exactly once. -/
abbrev Upper (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The independent coordinates consist of real and quaternion entries. -/
abbrev Coordinates (n : ℕ) :=
  (Fin n → ℝ) × (Upper n → ℍ[ℝ])

/-- The reconstruction places conjugate coordinates below the diagonal. -/
def matrixOfCoordinates (n : ℕ) (x : Coordinates n) : Mat n :=
  fun i j =>
    if hij : i = j then (x.1 i : ℍ[ℝ])
    else if hlt : i < j then x.2 ⟨(i, j), hlt⟩
    else star (x.2 ⟨(j, i), by
      change j < i
      omega⟩)

theorem matrixOfCoordinates_diag (n : ℕ) (x : Coordinates n) (i : Fin n) :
    matrixOfCoordinates n x i i = (x.1 i : ℍ[ℝ]) := by
  unfold matrixOfCoordinates
  rw [dif_pos rfl]

theorem matrixOfCoordinates_upper (n : ℕ) (x : Coordinates n)
    (i j : Fin n) (h : i < j) :
    matrixOfCoordinates n x i j = x.2 ⟨(i, j), h⟩ := by
  have hne : i ≠ j := by omega
  unfold matrixOfCoordinates
  rw [dif_neg hne, dif_pos h]

theorem matrixOfCoordinates_lower (n : ℕ) (x : Coordinates n)
    (i j : Fin n) (h : j < i) :
    matrixOfCoordinates n x i j = star (x.2 ⟨(j, i), h⟩) := by
  have hne : i ≠ j := by omega
  have hn : ¬ i < j := by omega
  unfold matrixOfCoordinates
  rw [dif_neg hne, dif_neg hn]

theorem matrixOfCoordinates_hermitian (n : ℕ) (x : Coordinates n) :
    (matrixOfCoordinates n x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases heq : i = j
  · subst j
    rw [matrixOfCoordinates_diag, Quaternion.star_coe]
  · by_cases hlt : i < j
    · rw [matrixOfCoordinates_lower n x j i hlt,
        matrixOfCoordinates_upper n x i j hlt]
      exact star_star _
    · have hgt : j < i := by omega
      rw [matrixOfCoordinates_upper n x j i hgt,
        matrixOfCoordinates_lower n x i j hgt]

/-- The reconstruction carries an explicit proof of Hermitian membership. -/
def assemble (n : ℕ) (x : Coordinates n) : Hermitian n :=
  ⟨matrixOfCoordinates n x, matrixOfCoordinates_hermitian n x⟩

/-- The coordinate extraction reads the diagonal and upper entries. -/
def coordinates (n : ℕ) (A : Hermitian n) : Coordinates n :=
  (fun i => (A.val i i).re, fun p => A.val p.val.1 p.val.2)

theorem assemble_coordinates (n : ℕ) (A : Hermitian n) :
    assemble n (coordinates n A) = A := by
  have hA : A.val.IsHermitian := A.property
  apply Subtype.ext
  funext i j
  change matrixOfCoordinates n (coordinates n A) i j = A.val i j
  by_cases heq : i = j
  · subst j
    exact (matrixOfCoordinates_diag n (coordinates n A) i).trans
      (Quaternion.star_eq_self.mp (hA.apply i i)).symm
  · by_cases hlt : i < j
    · exact matrixOfCoordinates_upper n (coordinates n A) i j hlt
    · have hgt : j < i := by omega
      exact (matrixOfCoordinates_lower n (coordinates n A) i j hgt).trans
        (hA.apply i j)

theorem coordinates_assemble (n : ℕ) (x : Coordinates n) :
    coordinates n (assemble n x) = x := by
  apply Prod.ext
  · funext i
    change (matrixOfCoordinates n x i i).re = x.1 i
    rw [matrixOfCoordinates_diag, Quaternion.coe_re]
  · funext p
    change matrixOfCoordinates n x p.val.1 p.val.2 = x.2 p
    exact matrixOfCoordinates_upper n x p.val.1 p.val.2 p.property

/-- The actual Hermitian space is real linearly equivalent to its coordinates. -/
def coordinateEquiv (n : ℕ) : Hermitian n ≃ₗ[ℝ] Coordinates n where
  toFun := coordinates n
  invFun := assemble n
  left_inv := assemble_coordinates n
  right_inv := coordinates_assemble n
  map_add' := by
    intro A B
    rfl
  map_smul' := by
    intro r A
    rfl

/-- The coordinate equivalence certifies finite dimensionality. -/
instance hermitianFinite (n : ℕ) : FiniteDimensional ℝ (Hermitian n) :=
  (coordinateEquiv n).symm.finiteDimensional

/-- Every real vector space is free; the instance is named for the Hermitian carrier. -/
instance hermitianFree (n : ℕ) : Module.Free ℝ (Hermitian n) :=
  Module.Free.of_divisionRing ℝ (Hermitian n)

/-- The real dimension counts the independent quaternion coordinates. -/
theorem hermitian_finrank (n : ℕ) :
    Module.finrank ℝ (Hermitian n) = n + Fintype.card (Upper n) * 4 := by
  rw [(coordinateEquiv n).finrank_eq]
  change Module.finrank ℝ ((Fin n → ℝ) × (Upper n → ℍ[ℝ])) =
    n + Fintype.card (Upper n) * 4
  rw [Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_pi_fintype]
  exact congrArg (fun d : ℕ => n + d)
    (Finset.sum_const_nat (s := (Finset.univ : Finset (Upper n)))
      (fun _ _ => Quaternion.finrank_eq_four (R := ℝ)))

theorem hermitian_finrank_two :
    Module.finrank ℝ (Hermitian 2) = 6 := by
  rw [hermitian_finrank]
  have h : Fintype.card (Upper 2) = 1 := by decide
  norm_num only [h]

theorem hermitian_finrank_four :
    Module.finrank ℝ (Hermitian 4) = 28 := by
  rw [hermitian_finrank]
  have h : Fintype.card (Upper 4) = 6 := by decide
  norm_num only [h]

/-- The E1 dimension goal refers to the actual matrix subspaces. -/
def QuaternionHermitianDimensionsGoal : Prop :=
  Module.finrank ℝ (Hermitian 2) = 6 ∧
  Module.finrank ℝ (Hermitian 4) = 28

theorem quaternionHermitianDimensionsGoal : QuaternionHermitianDimensionsGoal :=
  ⟨hermitian_finrank_two, hermitian_finrank_four⟩

/-!
## Unit 2: the real tensor-product obstruction

The comparison concerns the actual real vector spaces of quaternionic
Hermitian matrices. The tensor product of the two local real spaces has
dimension 36, while the composite Hermitian space has dimension 28.
The result rules out a real linear equivalence between these spaces.
It does not assert that a chosen product of local observables spans a
proper subspace of the composite, since such an assertion requires an
independent product construction and proof of its Hermitian range.
HONESTY_STATUS=SOURCE_CANDIDATE_NOT_KERNEL_VALIDATED
-/

/-- A quaternionic composite is not the real tensor product of its two local test spaces. -/
def QuaternionicTensorDimensionMismatchGoal : Prop :=
  ¬ Nonempty ((Hermitian 2 ⊗[ℝ] Hermitian 2) ≃ₗ[ℝ] Hermitian 4)

/-- Unequal real dimensions exclude every linear equivalence of these actual spaces. -/
theorem quaternionicTensorDimensionMismatchGoal :
    QuaternionicTensorDimensionMismatchGoal := by
  rintro ⟨e⟩
  have heq := e.finrank_eq
  rw [Module.finrank_tensorProduct,
    hermitian_finrank_two, hermitian_finrank_four] at heq
  norm_num at heq


/-!
## Unit 3: the dimension formula for every size

The strictly upper index pairs of size N are counted through the fibers over
their larger index. No caller premise enters.
-/

/-- The strictly upper index pairs of size n number n(n-1)/2. -/
theorem upper_card (n : ℕ) : Fintype.card (Upper n) = n * (n - 1) / 2 := by
  let e : Upper n ≃ Σ j : Fin n, Set.Iio j :=
    { toFun := fun p => ⟨p.val.2, ⟨p.val.1, p.property⟩⟩
      invFun := fun s => ⟨(s.2.val, s.1), s.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_Iio, Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

/-- E1(a): the quaternionic Hermitian matrices of size N have real dimension
N + 4 N(N-1)/2. -/
def QuaternionHermitianDimensionFormulaGoal : Prop :=
  ∀ N : ℕ, Module.finrank ℝ (Hermitian N) = N + 4 * (N * (N - 1) / 2)

theorem quaternionHermitianDimensionFormulaGoal :
    QuaternionHermitianDimensionFormulaGoal := by
  intro N
  rw [hermitian_finrank, upper_card, Nat.mul_comm]

/-!
## Unit 4: Hermitian Kronecker products span the composite Hermitian space

The composite of two quaternionic pairs uses the Kronecker product of the
local matrices, reindexed along the explicit equivalence of Fin 4 with
Fin 2 × Fin 2. A raw product of two Hermitian matrices need not be Hermitian;
the products that are Hermitian already span the whole composite Hermitian
space. The local Hermitian premises and the Hermitian premise on the product
are ORIGINAL_FINAL_ASSUMPTION in the membership predicate; every spanning
identity is INDEPENDENTLY_PROVED by entrywise computation.
-/

/-- The four composite indices list the pairs of local indices. -/
def pairIndex : Fin 4 ≃ Fin 2 × Fin 2 where
  toFun := ![(0, 0), (0, 1), (1, 0), (1, 1)]
  invFun := fun p => ⟨2 * p.1.val + p.2.val, by
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    omega⟩
  left_inv := by decide
  right_inv := by decide

theorem pairIndex_zero : pairIndex 0 = (0, 0) := rfl
theorem pairIndex_one : pairIndex 1 = (0, 1) := rfl
theorem pairIndex_two : pairIndex 2 = (1, 0) := rfl
theorem pairIndex_three : pairIndex 3 = (1, 1) := rfl

/-- The composite matrix of two local matrices is their Kronecker product,
reindexed by the composite index. -/
def kron (A B : Mat 2) : Mat 4 :=
  Matrix.reindex pairIndex.symm pairIndex.symm (Matrix.kroneckerMap (· * ·) A B)

theorem kron_apply (A B : Mat 2) (i j : Fin 4) :
    kron A B i j = A (pairIndex i).1 (pairIndex j).1 * B (pairIndex i).2 (pairIndex j).2 :=
  rfl

/-- A diagonal unit selects one local index. -/
def diagUnit (a : Fin 2) : Mat 2 := Matrix.of fun i j => if i = a ∧ j = a then 1 else 0

/-- The off-diagonal Hermitian matrix carrying one quaternion. -/
def offDiag (q : ℍ[ℝ]) : Mat 2 := !![0, q; star q, 0]

/-- A composite diagonal unit. -/
def diagGen (k : Fin 4) : Mat 4 := Matrix.of fun i j => if i = k ∧ j = k then 1 else 0

/-- A composite off-diagonal pair carrying one quaternion and its conjugate. -/
def pairGen (k l : Fin 4) (q : ℍ[ℝ]) : Mat 4 :=
  Matrix.of fun i j => if i = k ∧ j = l then q else if i = l ∧ j = k then star q else 0

/-- The Hermitian Kronecker products of two Hermitian local matrices. -/
def hermitianProducts : Set (Mat 4) :=
  {M | M.IsHermitian ∧ ∃ A B : Mat 2, A.IsHermitian ∧ B.IsHermitian ∧ M = kron A B}

/-- E1(b): the Hermitian products span the composite Hermitian space of size 4. -/
def QuaternionHermitianProductSpanGoal : Prop :=
  Submodule.span ℝ hermitianProducts = hermitianSubmodule 4

/-- The imaginary unit i of the Hamilton quaternions. -/
def qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

/-- The imaginary unit j of the Hamilton quaternions. -/
def qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩

theorem qi_mul_self : qi * qi = -1 := by
  ext <;> simp [qi]

theorem star_qi : star qi = -qi := by
  ext <;> simp [qi]

theorem qi_mul_neg_qi : qi * -qi = 1 := by
  ext <;> simp [qi]

theorem neg_qi_mul_qi : -qi * qi = 1 := by
  ext <;> simp [qi]

theorem neg_qi_mul_neg_qi : -qi * -qi = -1 := by
  ext <;> simp [qi]

theorem diagUnit_hermitian (a : Fin 2) : (diagUnit a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [diagUnit, Matrix.of_apply]
  by_cases h : i = a ∧ j = a
  · rw [if_pos ⟨h.2, h.1⟩, if_pos h, star_one]
  · rw [if_neg (fun h' => h ⟨h'.2, h'.1⟩), if_neg h, star_zero]

theorem offDiag_hermitian (q : ℍ[ℝ]) : (offDiag q).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [offDiag]

theorem diagGen_hermitian (k : Fin 4) : (diagGen k).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [diagGen, Matrix.of_apply]
  by_cases h : i = k ∧ j = k
  · rw [if_pos ⟨h.2, h.1⟩, if_pos h, star_one]
  · rw [if_neg (fun h' => h ⟨h'.2, h'.1⟩), if_neg h, star_zero]

theorem pairGen_hermitian (k l : Fin 4) (q : ℍ[ℝ]) (hkl : k ≠ l) :
    (pairGen k l q).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [pairGen, Matrix.of_apply]
  by_cases h1 : j = k ∧ i = l
  · rcases h1 with ⟨rfl, rfl⟩
    simp [hkl, Ne.symm hkl]
  · by_cases h2 : j = l ∧ i = k
    · rcases h2 with ⟨rfl, rfl⟩
      simp [hkl, Ne.symm hkl]
    · have h3 : ¬ (i = k ∧ j = l) := fun h => h2 ⟨h.2, h.1⟩
      have h4 : ¬ (i = l ∧ j = k) := fun h => h1 ⟨h.2, h.1⟩
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, star_zero]

theorem pairGen_add (k l : Fin 4) (q r : ℍ[ℝ]) :
    pairGen k l (q + r) = pairGen k l q + pairGen k l r := by
  refine Matrix.ext fun i j => ?_
  simp only [pairGen, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp [star_add]

theorem pairGen_neg (k l : Fin 4) (q : ℍ[ℝ]) : pairGen k l (-q) = -pairGen k l q := by
  refine Matrix.ext fun i j => ?_
  simp only [pairGen, Matrix.of_apply, Matrix.neg_apply]
  split_ifs <;> simp [star_neg]

theorem pairGen_coe (k l : Fin 4) (r : ℝ) :
    pairGen k l (r : ℍ[ℝ]) = r • pairGen k l 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [pairGen, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> ext <;> simp

theorem kron_diag_diag_zero_zero : kron (diagUnit 0) (diagUnit 0) = diagGen 0 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [kron_apply, pairIndex_zero, pairIndex_one, pairIndex_two, pairIndex_three,
      diagUnit, diagGen]

theorem kron_diag_diag_zero_one : kron (diagUnit 0) (diagUnit 1) = diagGen 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [kron_apply, pairIndex_zero, pairIndex_one, pairIndex_two, pairIndex_three,
      diagUnit, diagGen]

theorem kron_diag_diag_one_zero : kron (diagUnit 1) (diagUnit 0) = diagGen 2 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [kron_apply, pairIndex_zero, pairIndex_one, pairIndex_two, pairIndex_three,
      diagUnit, diagGen]

theorem kron_diag_diag_one_one : kron (diagUnit 1) (diagUnit 1) = diagGen 3 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [kron_apply, pairIndex_zero, pairIndex_one, pairIndex_two, pairIndex_three,
      diagUnit, diagGen]

theorem kron_diag_zero_offDiag (q : ℍ[ℝ]) : kron (diagUnit 0) (offDiag q) = pairGen 0 1 q := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [kron_apply, pairIndex_zero, pairIndex_one, pairIndex_two, pairIndex_three,
      diagUnit, offDiag, pairGen]

theorem kron_diag_one_offDiag (q : ℍ[ℝ]) : kron (diagUnit 1) (offDiag q) = pairGen 2 3 q := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [kron_apply, pairIndex_zero, pairIndex_one, pairIndex_two, pairIndex_three,
      diagUnit, offDiag, pairGen]

theorem kron_offDiag_diag_zero (q : ℍ[ℝ]) : kron (offDiag q) (diagUnit 0) = pairGen 0 2 q := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [kron_apply, pairIndex_zero, pairIndex_one, pairIndex_two, pairIndex_three,
      diagUnit, offDiag, pairGen]

theorem kron_offDiag_diag_one (q : ℍ[ℝ]) : kron (offDiag q) (diagUnit 1) = pairGen 1 3 q := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [kron_apply, pairIndex_zero, pairIndex_one, pairIndex_two, pairIndex_three,
      diagUnit, offDiag, pairGen]

theorem kron_offDiag_offDiag_one (q : ℍ[ℝ]) :
    kron (offDiag q) (offDiag 1) = pairGen 0 3 q + pairGen 1 2 q := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [kron_apply, pairIndex_zero, pairIndex_one, pairIndex_two, pairIndex_three,
      offDiag, pairGen]

theorem kron_offDiag_one_offDiag (q : ℍ[ℝ]) :
    kron (offDiag 1) (offDiag q) = pairGen 0 3 q + pairGen 1 2 (star q) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [kron_apply, pairIndex_zero, pairIndex_one, pairIndex_two, pairIndex_three,
      offDiag, pairGen]

theorem kron_offDiag_qi_qi :
    kron (offDiag qi) (offDiag qi) = pairGen 0 3 (-1) + pairGen 1 2 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [kron_apply, pairIndex_zero, pairIndex_one, pairIndex_two, pairIndex_three,
      offDiag, pairGen, star_qi, qi_mul_self, qi_mul_neg_qi, neg_qi_mul_qi, neg_qi_mul_neg_qi]

/-- A raw product of two Hermitian matrices can fail to be Hermitian:
the off-diagonal matrices of i and j give a non-Hermitian product. -/
theorem kron_offDiag_qi_qj_not_hermitian : ¬ (kron (offDiag qi) (offDiag qj)).IsHermitian := by
  intro h
  have h30 := congrArg (fun x : ℍ[ℝ] => x.imK) (h.apply 3 0)
  norm_num [kron_apply, pairIndex_zero, pairIndex_three, offDiag, qi, qj] at h30

theorem kron_mem_span (A B : Mat 2) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hK : (kron A B).IsHermitian) : kron A B ∈ Submodule.span ℝ hermitianProducts :=
  Submodule.subset_span ⟨hK, A, B, hA, hB, rfl⟩

theorem mem_span_of_add_self_mem {M : Mat 4}
    (h : M + M ∈ Submodule.span ℝ hermitianProducts) :
    M ∈ Submodule.span ℝ hermitianProducts := by
  have h' := Submodule.smul_mem (Submodule.span ℝ hermitianProducts) (1 / 2 : ℝ) h
  rwa [← two_smul ℝ M, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h'

theorem diagGen_mem_span (k : Fin 4) : diagGen k ∈ Submodule.span ℝ hermitianProducts := by
  have h0 : diagGen 0 ∈ Submodule.span ℝ hermitianProducts := by
    rw [← kron_diag_diag_zero_zero]
    refine kron_mem_span _ _ (diagUnit_hermitian 0) (diagUnit_hermitian 0) ?_
    rw [kron_diag_diag_zero_zero]
    exact diagGen_hermitian 0
  have h1 : diagGen 1 ∈ Submodule.span ℝ hermitianProducts := by
    rw [← kron_diag_diag_zero_one]
    refine kron_mem_span _ _ (diagUnit_hermitian 0) (diagUnit_hermitian 1) ?_
    rw [kron_diag_diag_zero_one]
    exact diagGen_hermitian 1
  have h2 : diagGen 2 ∈ Submodule.span ℝ hermitianProducts := by
    rw [← kron_diag_diag_one_zero]
    refine kron_mem_span _ _ (diagUnit_hermitian 1) (diagUnit_hermitian 0) ?_
    rw [kron_diag_diag_one_zero]
    exact diagGen_hermitian 2
  have h3 : diagGen 3 ∈ Submodule.span ℝ hermitianProducts := by
    rw [← kron_diag_diag_one_one]
    refine kron_mem_span _ _ (diagUnit_hermitian 1) (diagUnit_hermitian 1) ?_
    rw [kron_diag_diag_one_one]
    exact diagGen_hermitian 3
  fin_cases k
  exacts [h0, h1, h2, h3]

theorem pairGen01_mem_span (q : ℍ[ℝ]) : pairGen 0 1 q ∈ Submodule.span ℝ hermitianProducts := by
  rw [← kron_diag_zero_offDiag]
  refine kron_mem_span _ _ (diagUnit_hermitian 0) (offDiag_hermitian q) ?_
  rw [kron_diag_zero_offDiag]
  exact pairGen_hermitian 0 1 q (by decide)

theorem pairGen23_mem_span (q : ℍ[ℝ]) : pairGen 2 3 q ∈ Submodule.span ℝ hermitianProducts := by
  rw [← kron_diag_one_offDiag]
  refine kron_mem_span _ _ (diagUnit_hermitian 1) (offDiag_hermitian q) ?_
  rw [kron_diag_one_offDiag]
  exact pairGen_hermitian 2 3 q (by decide)

theorem pairGen02_mem_span (q : ℍ[ℝ]) : pairGen 0 2 q ∈ Submodule.span ℝ hermitianProducts := by
  rw [← kron_offDiag_diag_zero]
  refine kron_mem_span _ _ (offDiag_hermitian q) (diagUnit_hermitian 0) ?_
  rw [kron_offDiag_diag_zero]
  exact pairGen_hermitian 0 2 q (by decide)

theorem pairGen13_mem_span (q : ℍ[ℝ]) : pairGen 1 3 q ∈ Submodule.span ℝ hermitianProducts := by
  rw [← kron_offDiag_diag_one]
  refine kron_mem_span _ _ (offDiag_hermitian q) (diagUnit_hermitian 1) ?_
  rw [kron_offDiag_diag_one]
  exact pairGen_hermitian 1 3 q (by decide)

theorem pairGen_cross_q_one_mem (q : ℍ[ℝ]) :
    pairGen 0 3 q + pairGen 1 2 q ∈ Submodule.span ℝ hermitianProducts := by
  rw [← kron_offDiag_offDiag_one]
  refine kron_mem_span _ _ (offDiag_hermitian q) (offDiag_hermitian 1) ?_
  rw [kron_offDiag_offDiag_one]
  exact (pairGen_hermitian 0 3 q (by decide)).add (pairGen_hermitian 1 2 q (by decide))

theorem pairGen_cross_one_q_mem (q : ℍ[ℝ]) :
    pairGen 0 3 q + pairGen 1 2 (star q) ∈ Submodule.span ℝ hermitianProducts := by
  rw [← kron_offDiag_one_offDiag]
  refine kron_mem_span _ _ (offDiag_hermitian 1) (offDiag_hermitian q) ?_
  rw [kron_offDiag_one_offDiag]
  exact (pairGen_hermitian 0 3 q (by decide)).add (pairGen_hermitian 1 2 (star q) (by decide))

theorem pairGen_cross_qi_mem :
    pairGen 0 3 (-1) + pairGen 1 2 1 ∈ Submodule.span ℝ hermitianProducts := by
  rw [← kron_offDiag_qi_qi]
  refine kron_mem_span _ _ (offDiag_hermitian qi) (offDiag_hermitian qi) ?_
  rw [kron_offDiag_qi_qi]
  exact (pairGen_hermitian 0 3 (-1) (by decide)).add (pairGen_hermitian 1 2 1 (by decide))

theorem pairGen12_one_mem_span : pairGen 1 2 1 ∈ Submodule.span ℝ hermitianProducts := by
  apply mem_span_of_add_self_mem
  have h := Submodule.add_mem _ (pairGen_cross_q_one_mem 1) pairGen_cross_qi_mem
  rw [pairGen_neg] at h
  have heq : pairGen 0 3 1 + pairGen 1 2 1 + (-pairGen 0 3 1 + pairGen 1 2 1) =
      pairGen 1 2 1 + pairGen 1 2 1 := by
    abel
  rwa [heq] at h

theorem pairGen12_mem_span (q : ℍ[ℝ]) : pairGen 1 2 q ∈ Submodule.span ℝ hermitianProducts := by
  apply mem_span_of_add_self_mem
  have hsum : pairGen 1 2 q + pairGen 1 2 (star q) = (2 * q.re) • pairGen 1 2 1 := by
    rw [← pairGen_add, Quaternion.self_add_star', pairGen_coe]
  have h := Submodule.add_mem _
    (Submodule.sub_mem _ (pairGen_cross_q_one_mem q) (pairGen_cross_one_q_mem q))
    (Submodule.smul_mem _ (2 * q.re) pairGen12_one_mem_span)
  have heq : pairGen 0 3 q + pairGen 1 2 q - (pairGen 0 3 q + pairGen 1 2 (star q)) +
      (2 * q.re) • pairGen 1 2 1 = pairGen 1 2 q + pairGen 1 2 q := by
    rw [← hsum]
    abel
  rwa [heq] at h

theorem pairGen03_mem_span (q : ℍ[ℝ]) : pairGen 0 3 q ∈ Submodule.span ℝ hermitianProducts := by
  apply mem_span_of_add_self_mem
  have hsum : pairGen 1 2 q + pairGen 1 2 (star q) = (2 * q.re) • pairGen 1 2 1 := by
    rw [← pairGen_add, Quaternion.self_add_star', pairGen_coe]
  have h := Submodule.sub_mem _
    (Submodule.add_mem _ (pairGen_cross_q_one_mem q) (pairGen_cross_one_q_mem q))
    (Submodule.smul_mem _ (2 * q.re) pairGen12_one_mem_span)
  have heq : pairGen 0 3 q + pairGen 1 2 q + (pairGen 0 3 q + pairGen 1 2 (star q)) -
      (2 * q.re) • pairGen 1 2 1 = pairGen 0 3 q + pairGen 0 3 q := by
    rw [← hsum]
    abel
  rwa [heq] at h

/-- A composite diagonal entry carrying one quaternion. -/
def diagVal (k : Fin 4) (x : ℍ[ℝ]) : Mat 4 :=
  Matrix.of fun i j => if i = k ∧ j = k then x else 0

theorem diagVal_coe (k : Fin 4) (r : ℝ) : diagVal k (r : ℍ[ℝ]) = r • diagGen k := by
  refine Matrix.ext fun i j => ?_
  simp only [diagVal, diagGen, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> ext <;> simp

/-- Every Hermitian matrix of size 4 is the sum of its diagonal and pair generators. -/
theorem hermitian_decomposition (M : Mat 4) (hM : M.IsHermitian) :
    M = (∑ k : Fin 4, diagVal k (M k k)) +
      (pairGen 0 1 (M 0 1) + pairGen 0 2 (M 0 2) + pairGen 0 3 (M 0 3) +
        pairGen 1 2 (M 1 2) + pairGen 1 3 (M 1 3) + pairGen 2 3 (M 2 3)) := by
  have hlow : ∀ i j : Fin 4, star (M j i) = M i j := fun i j => hM.apply i j
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) only [Matrix.add_apply,
      Fin.sum_univ_four, diagVal, pairGen, Matrix.of_apply, ↓reduceIte, add_zero, zero_add,
      hlow] <;> rfl

theorem hermitian_mem_span (M : Mat 4) (hM : M.IsHermitian) :
    M ∈ Submodule.span ℝ hermitianProducts := by
  rw [hermitian_decomposition M hM]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => ?_) ?_
  · have hk : M k k = ((M k k).re : ℍ[ℝ]) := Quaternion.star_eq_self.mp (hM.apply k k)
    rw [hk, diagVal_coe]
    exact Submodule.smul_mem _ _ (diagGen_mem_span k)
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.add_mem _ (pairGen01_mem_span _) (pairGen02_mem_span _))
      (pairGen03_mem_span _)) (pairGen12_mem_span _)) (pairGen13_mem_span _))
    (pairGen23_mem_span _)

theorem quaternionHermitianProductSpanGoal : QuaternionHermitianProductSpanGoal := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro M hM
    exact hM.1
  · intro M hM
    exact hermitian_mem_span M hM

/-!
## Unit 5: no injective real-linear map from the local tensor product

The real tensor product of the two local Hermitian spaces has dimension 36 and
the composite Hermitian space has dimension 28, so no injective real-linear map
of the first into the second exists. The result concerns the actual real vector
spaces, beyond equality of two numbers.
-/

/-- E1(c): no injective real-linear map from the 36-dimensional local tensor
product into the 28-dimensional composite Hermitian space exists. -/
def QuaternionicTensorNoInjectionGoal : Prop :=
  ¬ ∃ f : (Hermitian 2 ⊗[ℝ] Hermitian 2) →ₗ[ℝ] Hermitian 4, Function.Injective f

theorem quaternionicTensorNoInjectionGoal : QuaternionicTensorNoInjectionGoal := by
  rintro ⟨f, hf⟩
  have hle := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_tensorProduct, hermitian_finrank_two, hermitian_finrank_four] at hle
  norm_num at hle

/-- The corrected E1 statement: the dimension formula for every size, the span of
the Hermitian products, and the absence of an injective map from the local tensor
product. -/
def PairQuaternionGoal : Prop :=
  QuaternionHermitianDimensionFormulaGoal ∧ QuaternionHermitianProductSpanGoal ∧
    QuaternionicTensorNoInjectionGoal

theorem pairQuaternionGoal : PairQuaternionGoal :=
  ⟨quaternionHermitianDimensionFormulaGoal, quaternionHermitianProductSpanGoal,
    quaternionicTensorNoInjectionGoal⟩

end

end OperatorKO7.Meta.BoundaryObserver.PairQuaternion
