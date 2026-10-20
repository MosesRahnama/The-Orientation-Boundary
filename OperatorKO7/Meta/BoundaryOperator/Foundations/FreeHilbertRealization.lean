import Mathlib.Analysis.InnerProductSpace.PiL2
import OperatorKO7.Meta.UUET.Quantum.FiniteHilbert

/-!
# Finite free Hilbert realization from explicit weights

Role labels do not create Hilbert structure.  This module starts from an
explicit finite basis and a strictly positive real weight on each basis
coordinate.  Coefficients live in the algebraically free complex function
space.  Positive weights embed that free carrier into the genuine finite
Hilbert space `EuclideanSpace ℂ ι`; the inner product used below is the pullback
of the actual Hilbert inner product along that embedding.

The free claim is algebraic and theorem-backed: every basis assignment into an
arbitrary complex module has a canonical linear extension, and that extension
is unique among linear maps agreeing on the basis.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryOperator.Foundations.FreeHilbertRealization

open scoped BigOperators

universe u v

/-- Strictly positive finite weights. -/
structure PositiveWeights (ι : Type u) [Fintype ι] where
  weight : ι -> ℝ
  positive : ∀ i, 0 < weight i

/-- Algebraically free finite coefficient carrier over `ℂ`. -/
abbrev FreeCarrier (ι : Type u) := ι -> ℂ

/-- Genuine finite complex Hilbert target supplied by Mathlib. -/
abbrev HilbertCarrier (ι : Type u) := EuclideanSpace ℂ ι

/-- Canonical free basis vector. -/
def basisVector {ι : Type u} [DecidableEq ι] (i : ι) : FreeCarrier ι :=
  fun j => if j = i then 1 else 0

/--
Weight-dependent embedding into the genuine finite Hilbert carrier.  The
coefficient of basis state `i` is multiplied by `sqrt(weight i)`.
-/
noncomputable def weightedScale {ι : Type u} [Fintype ι]
    (weights : PositiveWeights ι) (x : FreeCarrier ι) : HilbertCarrier ι :=
  (EuclideanSpace.equiv ι ℂ).symm
    (fun i => (((Real.sqrt (weights.weight i) : ℝ) : ℂ) * x i))

/-- Coordinate formula for the weighted embedding. -/
theorem weightedScale_apply {ι : Type u} [Fintype ι]
    (weights : PositiveWeights ι) (x : FreeCarrier ι) (i : ι) :
    weightedScale weights x i =
      (((Real.sqrt (weights.weight i) : ℝ) : ℂ) * x i) :=
  rfl

/-- Strict positivity makes the weight-dependent Hilbert embedding injective. -/
theorem weightedScale_injective {ι : Type u} [Fintype ι]
    (weights : PositiveWeights ι) : Function.Injective (weightedScale weights) := by
  classical
  intro x y hxy
  funext i
  have hi := congrArg (fun z : HilbertCarrier ι => z i) hxy
  change weightedScale weights x i = weightedScale weights y i at hi
  simp only [weightedScale_apply] at hi
  have hsqrtR : Real.sqrt (weights.weight i) ≠ 0 :=
    (Real.sqrt_pos.mpr (weights.positive i)).ne'
  have hsqrtC : (((Real.sqrt (weights.weight i) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hsqrtR
  exact mul_left_cancel₀ hsqrtC hi

/-- The weight-dependent sesquilinear form is pulled back from a genuine Hilbert inner product. -/
noncomputable def weightedInner {ι : Type u} [Fintype ι]
    (weights : PositiveWeights ι) (x y : FreeCarrier ι) : ℂ :=
  inner ℂ (weightedScale weights x) (weightedScale weights y)

/-- Pullback positivity: every vector has nonnegative real self-inner-product. -/
theorem weightedInner_self_re_nonneg {ι : Type u} [Fintype ι]
    (weights : PositiveWeights ι) (x : FreeCarrier ι) :
    0 <= (weightedInner weights x x).re := by
  change 0 ≤ (inner ℂ (weightedScale weights x) (weightedScale weights x)).re
  exact inner_self_nonneg (𝕜 := ℂ) (x := weightedScale weights x)

/-- The weighted embedding sends the zero coefficient vector to zero. -/
theorem weightedScale_zero {ι : Type u} [Fintype ι]
    (weights : PositiveWeights ι) :
    weightedScale weights (0 : FreeCarrier ι) = 0 := by
  ext i
  simp [weightedScale_apply]

/-- Pullback nondegeneracy follows from the Hilbert target and positive weights. -/
theorem weightedInner_self_eq_zero_iff {ι : Type u} [Fintype ι]
    (weights : PositiveWeights ι) (x : FreeCarrier ι) :
    weightedInner weights x x = 0 ↔ x = 0 := by
  change inner ℂ (weightedScale weights x) (weightedScale weights x) = 0 ↔ x = 0
  constructor
  · intro h
    have hScale : weightedScale weights x = 0 :=
      (inner_self_eq_zero (𝕜 := ℂ)).mp h
    apply weightedScale_injective weights
    simpa [weightedScale_zero] using hScale
  · intro hx
    subst x
    rw [weightedScale_zero]
    simp

/-- The weighted embedding sends a free basis vector to the corresponding scaled Hilbert basis. -/
theorem weightedScale_basis {ι : Type u} [Fintype ι] [DecidableEq ι]
    (weights : PositiveWeights ι) (i : ι) :
    weightedScale weights (basisVector i) =
      EuclideanSpace.single i (((Real.sqrt (weights.weight i) : ℝ) : ℂ)) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [weightedScale_apply, basisVector, EuclideanSpace.single_apply]
  · simp [weightedScale_apply, basisVector, EuclideanSpace.single_apply, hji]

/-- The self-inner-product of a basis vector is exactly its supplied weight. -/
theorem weightedInner_basis_self {ι : Type u} [Fintype ι] [DecidableEq ι]
    (weights : PositiveWeights ι) (i : ι) :
    weightedInner weights (basisVector i) (basisVector i) =
      ((weights.weight i : ℝ) : ℂ) := by
  change inner ℂ (weightedScale weights (basisVector i))
    (weightedScale weights (basisVector i)) = _
  rw [weightedScale_basis weights i]
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  simp only [if_true, Complex.conj_ofReal]
  have hs : Real.sqrt (weights.weight i) * Real.sqrt (weights.weight i) =
      weights.weight i :=
    Real.mul_self_sqrt (le_of_lt (weights.positive i))
  exact_mod_cast hs

/--
Canonical linear extension of arbitrary basis data.  This is the algebraic
universal map behind the word `free`.
-/
noncomputable def linearExtension {ι : Type u} [Fintype ι]
    {V : Type v} [AddCommMonoid V] [Module ℂ V]
    (f : ι -> V) : FreeCarrier ι →ₗ[ℂ] V where
  toFun x := ∑ i, x i • f i
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
    rfl

/-- The canonical extension agrees with the supplied basis assignment. -/
theorem linearExtension_basis {ι : Type u} [Fintype ι] [DecidableEq ι]
    {V : Type v} [AddCommMonoid V] [Module ℂ V]
    (f : ι -> V) (i : ι) :
    linearExtension f (basisVector i) = f i := by
  classical
  simp [linearExtension, basisVector]

/-- Every coefficient vector is the finite linear combination of its basis coordinates. -/
theorem basis_decomposition {ι : Type u} [Fintype ι] [DecidableEq ι]
    (x : FreeCarrier ι) :
    x = ∑ i, x i • basisVector i := by
  classical
  funext j
  simp [basisVector]

/-- Universal property: the basis extension is the unique linear map with those basis values. -/
theorem linearExtension_unique {ι : Type u} [Fintype ι] [DecidableEq ι]
    {V : Type v} [AddCommMonoid V] [Module ℂ V]
    (f : ι -> V) (g : FreeCarrier ι →ₗ[ℂ] V)
    (hBasis : ∀ i, g (basisVector i) = f i) :
    g = linearExtension f := by
  apply LinearMap.ext
  intro x
  calc
    g x = g (∑ i, x i • basisVector i) := by rw [← basis_decomposition x]
    _ = ∑ i, x i • g (basisVector i) := by simp
    _ = ∑ i, x i • f i := by simp [hBasis]
    _ = linearExtension f x := rfl

/-- The complete explicit-data finite free Hilbert realization. -/
structure FiniteFreeHilbertRealization (ι : Type u) [Fintype ι] where
  weights : PositiveWeights ι

namespace FiniteFreeHilbertRealization

/-- Weight-derived embedding associated to the realization. -/
noncomputable def toHilbert {ι : Type u} [Fintype ι]
    (realization : FiniteFreeHilbertRealization ι) :
    FreeCarrier ι -> HilbertCarrier ι :=
  weightedScale realization.weights

/-- The realization's pullback inner form. -/
noncomputable def innerForm {ι : Type u} [Fintype ι]
    (realization : FiniteFreeHilbertRealization ι) :
    FreeCarrier ι -> FreeCarrier ι -> ℂ :=
  weightedInner realization.weights

/-- Positive weights make the realization faithful. -/
theorem toHilbert_injective {ι : Type u} [Fintype ι]
    (realization : FiniteFreeHilbertRealization ι) :
    Function.Injective realization.toHilbert :=
  weightedScale_injective realization.weights

/-- Nondegeneracy of the realized inner form. -/
theorem innerForm_nondegenerate {ι : Type u} [Fintype ι]
    (realization : FiniteFreeHilbertRealization ι) (x : FreeCarrier ι) :
    realization.innerForm x x = 0 ↔ x = 0 :=
  weightedInner_self_eq_zero_iff realization.weights x

end FiniteFreeHilbertRealization

/-! ## Two-state fixture and role-label no-go -/

/-- Uniform positive weights on a two-state basis. -/
def uniformTwoWeights : PositiveWeights (Fin 2) where
  weight := fun _ => 1
  positive := by intro i; norm_num

/-- A distinct positive weighting on the same two role labels. -/
def skewTwoWeights : PositiveWeights (Fin 2) where
  weight := fun i => if i = 0 then 1 else 2
  positive := by
    intro i
    fin_cases i <;> norm_num

/-- Nontrivial two-state free Hilbert realization. -/
def twoStateRealization : FiniteFreeHilbertRealization (Fin 2) :=
  ⟨skewTwoWeights⟩

/-- Its two free basis vectors are distinct before any Hilbert interpretation. -/
theorem two_state_basis_nontrivial :
    basisVector (0 : Fin 2) ≠ basisVector (1 : Fin 2) := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  norm_num [basisVector] at h0

/--
Negative theorem: the same two basis/role labels admit distinct positive
weightings and therefore distinct Hilbert pullback inner products.  Labels alone
do not determine the inner product.
-/
theorem role_labels_alone_do_not_determine_inner_product :
    weightedInner uniformTwoWeights (basisVector (1 : Fin 2)) (basisVector (1 : Fin 2)) ≠
      weightedInner skewTwoWeights (basisVector (1 : Fin 2)) (basisVector (1 : Fin 2)) := by
  rw [weightedInner_basis_self, weightedInner_basis_self]
  norm_num [uniformTwoWeights, skewTwoWeights]

/-- The two-state realization retains the full algebraic free-extension property. -/
theorem two_state_free_extension_unique
    {V : Type v} [AddCommMonoid V] [Module ℂ V]
    (f : Fin 2 -> V) (g : FreeCarrier (Fin 2) →ₗ[ℂ] V)
    (hBasis : ∀ i, g (basisVector i) = f i) :
    g = linearExtension f :=
  linearExtension_unique f g hBasis

#check @weightedScale_injective
#check @weightedInner_self_re_nonneg
#check @weightedInner_self_eq_zero_iff
#check @weightedInner_basis_self
#check @linearExtension_basis
#check @linearExtension_unique
#check @FiniteFreeHilbertRealization.toHilbert_injective
#check @FiniteFreeHilbertRealization.innerForm_nondegenerate
#check two_state_basis_nontrivial
#check role_labels_alone_do_not_determine_inner_product
#print axioms weightedScale_injective
#print axioms weightedInner_self_re_nonneg
#print axioms weightedInner_self_eq_zero_iff
#print axioms weightedInner_basis_self
#print axioms linearExtension_unique
#print axioms FiniteFreeHilbertRealization.innerForm_nondegenerate
#print axioms role_labels_alone_do_not_determine_inner_product


/-! ## Normalized quotient coordinates and the invariant Hilbert subspace -/

section QuotientHilbert

variable {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]

/-- The square root of an observation-fiber cardinality, as a complex scalar. -/
noncomputable def fiberRoot (q : X → Q) (y : Q) : ℂ :=
  ((Real.sqrt (Fintype.card {x // q x = y} : ℝ) : ℝ) : ℂ)

omit [Fintype Q] in
theorem star_fiberRoot (q : X → Q) (y : Q) : star (fiberRoot q y) = fiberRoot q y := by
  simp [fiberRoot]

omit [Fintype Q] in
theorem fiberRoot_mul_self (q : X → Q) (y : Q) :
    fiberRoot q y * fiberRoot q y = (Fintype.card {x // q x = y} : ℂ) := by
  have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ (Fintype.card {x // q x = y} : ℝ) by positivity)
  unfold fiberRoot
  exact_mod_cast h

omit [Fintype Q] in
theorem fiberRoot_ne_zero (q : X → Q) (hq : Function.Surjective q) (y : Q) :
    fiberRoot q y ≠ 0 := by
  obtain ⟨x, hx⟩ := hq y
  letI : Nonempty {x // q x = y} := ⟨⟨x, hx⟩⟩
  have hpos : (0 : ℝ) < (Fintype.card {x // q x = y} : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := {x // q x = y}))
  have hs := (Real.sqrt_pos.mpr hpos).ne'
  simp only [fiberRoot, ne_eq, Complex.ofReal_eq_zero]
  exact hs

/-- The normalized lift sends a record amplitude to equal amplitudes on its fiber. -/
noncomputable def normalizedFiberLift (q : X → Q) (v : HilbertCarrier Q) : HilbertCarrier X :=
  (EuclideanSpace.equiv X ℂ).symm (fun x => v (q x) / fiberRoot q (q x))

omit [Fintype Q] in
theorem normalizedFiberLift_apply (q : X → Q) (v : HilbertCarrier Q) (x : X) :
    normalizedFiberLift q v x = v (q x) / fiberRoot q (q x) := rfl

/-- Normalized fiber sums preserve the actual complex Hilbert inner product. -/
theorem normalizedFiberLift_inner (q : X → Q) (hq : Function.Surjective q)
    (v w : HilbertCarrier Q) :
    inner ℂ (normalizedFiberLift q v) (normalizedFiberLift q w) = inner ℂ v w := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ x, normalizedFiberLift q w x * star (normalizedFiberLift q v x)) =
    ∑ y, w y * star (v y)
  rw [← Fintype.sum_fiberwise q
    (fun x => normalizedFiberLift q w x * star (normalizedFiberLift q v x))]
  apply Finset.sum_congr rfl
  intro y _
  have hterm (x : {x // q x = y}) :
      normalizedFiberLift q w x.1 * star (normalizedFiberLift q v x.1) =
        (w y * star (v y)) / (fiberRoot q y * fiberRoot q y) := by
    rw [normalizedFiberLift_apply, normalizedFiberLift_apply, x.2, star_div₀, star_fiberRoot]
    ring
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← fiberRoot_mul_self q y]
  field_simp [fiberRoot_ne_zero q hq y]

/-- The actual linear isometry from record amplitudes into source amplitudes. -/
noncomputable def normalizedFiberIsometry (q : X → Q) (hq : Function.Surjective q) :
    HilbertCarrier Q →ₗᵢ[ℂ] HilbertCarrier X where
  toFun := normalizedFiberLift q
  map_add' v w := by
    ext x
    change (v (q x) + w (q x)) / fiberRoot q (q x) =
      v (q x) / fiberRoot q (q x) + w (q x) / fiberRoot q (q x)
    ring
  map_smul' c v := by
    ext x
    change (c * v (q x)) / fiberRoot q (q x) =
      c * (v (q x) / fiberRoot q (q x))
    ring
  norm_map' v := by
    have h := normalizedFiberLift_inner q hq v v
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have hs : ‖normalizedFiberLift q v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

/-- The subspace of amplitudes constant on each observation fiber. -/
noncomputable def fiberConstantSubspace (q : X → Q) : Submodule ℂ (HilbertCarrier X) where
  carrier := {v | ∀ x x', q x = q x' → v x = v x'}
  zero_mem' := by intro x x' _; rfl
  add_mem' := by
    intro v w hv hw x x' h
    change v x + w x = v x' + w x'
    rw [hv x x' h, hw x x' h]
  smul_mem' := by
    intro c v hv x x' h
    change c * v x = c * v x'
    rw [hv x x' h]

omit [Fintype Q] in
theorem normalizedFiberLift_mem (q : X → Q) (v : HilbertCarrier Q) :
    normalizedFiberLift q v ∈ fiberConstantSubspace q := by
  intro x x' h
  change v (q x) / fiberRoot q (q x) = v (q x') / fiberRoot q (q x')
  exact congrArg (fun y => v y / fiberRoot q y) h

omit [Fintype Q] in
/-- Every fiber-constant amplitude has record coordinates; the inverse multiplies by sqrt size. -/
theorem normalizedFiberLift_surjective_subspace (q : X → Q) (hq : Function.Surjective q)
    (v : fiberConstantSubspace q) :
    ∃ w : HilbertCarrier Q, normalizedFiberLift q w = v.1 := by
  classical
  let choose : Q → X := fun y => Classical.choose (hq y)
  have hchoose : ∀ y, q (choose y) = y := fun y => Classical.choose_spec (hq y)
  let w : HilbertCarrier Q := (EuclideanSpace.equiv Q ℂ).symm
    (fun y => fiberRoot q y * v.1 (choose y))
  refine ⟨w, ?_⟩
  ext x
  change (fiberRoot q (q x) * v.1 (choose (q x))) / fiberRoot q (q x) = v.1 x
  rw [v.2 (choose (q x)) x (hchoose (q x))]
  field_simp [fiberRoot_ne_zero q hq (q x)]

/-- The normalized quotient lift is a genuine linear isometry equivalence onto invariant amplitudes. -/
noncomputable def normalizedFiberEquiv (q : X → Q) (hq : Function.Surjective q) :
    HilbertCarrier Q ≃ₗᵢ[ℂ] fiberConstantSubspace q :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap :=
        { toFun := fun v => ⟨normalizedFiberLift q v, normalizedFiberLift_mem q v⟩
          map_add' := by
            intro v w
            apply Subtype.ext
            exact (normalizedFiberIsometry q hq).map_add v w
          map_smul' := by
            intro c v
            apply Subtype.ext
            exact (normalizedFiberIsometry q hq).map_smul c v }
      norm_map' := fun v => (normalizedFiberIsometry q hq).norm_map v }
    (by
      intro v
      obtain ⟨w, hw⟩ := normalizedFiberLift_surjective_subspace q hq v
      exact ⟨w, Subtype.ext hw⟩)

theorem normalizedFiberEquiv_apply (q : X → Q) (hq : Function.Surjective q)
    (v : HilbertCarrier Q) (x : X) :
    (normalizedFiberEquiv q hq v).1 x = v (q x) / fiberRoot q (q x) := rfl

/-- Diagonal multiplication on an actual finite Hilbert carrier. -/
noncomputable def diagonalAction {I : Type} [Fintype I] (d : I → ℂ) :
    HilbertCarrier I →ₗ[ℂ] HilbertCarrier I where
  toFun v := (EuclideanSpace.equiv I ℂ).symm (fun i => d i * v i)
  map_add' v w := by
    ext i
    change d i * (v i + w i) = d i * v i + d i * w i
    ring
  map_smul' c v := by ext i; change d i * (c * v i) = c * (d i * v i); ring

/-- The normalized equivalence intertwines every diagonal observable pulled back along q. -/
theorem normalizedFiberLift_intertwines (q : X → Q) (d : Q → ℂ) (v : HilbertCarrier Q) :
    normalizedFiberLift q (diagonalAction d v) =
      diagonalAction (d ∘ q) (normalizedFiberLift q v) := by
  ext x
  change (d (q x) * v (q x)) / fiberRoot q (q x) =
    d (q x) * (v (q x) / fiberRoot q (q x))
  ring

omit [Fintype Q] [DecidableEq Q] in
/-- When the fibers are precisely group orbits, fiber-constant amplitudes are exactly the
invariant vectors. The acting group itself need not be finite. -/
theorem fiberConstant_iff_group_invariant {G : Type*} [Group G] [MulAction G X]
    (q : X → Q) (horbit : ∀ x x', q x = q x' ↔ ∃ g : G, g • x = x')
    (v : HilbertCarrier X) :
    v ∈ fiberConstantSubspace q ↔ ∀ g : G, ∀ x : X, v (g • x) = v x := by
  constructor
  · intro hv g x
    exact (hv x (g • x) ((horbit x (g • x)).mpr ⟨g, rfl⟩)).symm
  · intro hv x x' h
    obtain ⟨g, hg⟩ := (horbit x x').mp h
    rw [← hg, hv g x]

end QuotientHilbert

#check @fiberRoot
#print axioms fiberRoot
#check @star_fiberRoot
#print axioms star_fiberRoot
#check @fiberRoot_mul_self
#print axioms fiberRoot_mul_self
#check @fiberRoot_ne_zero
#print axioms fiberRoot_ne_zero
#check @normalizedFiberLift
#print axioms normalizedFiberLift
#check @normalizedFiberLift_apply
#print axioms normalizedFiberLift_apply
#check @normalizedFiberLift_inner
#print axioms normalizedFiberLift_inner
#check @normalizedFiberIsometry
#print axioms normalizedFiberIsometry
#check @fiberConstantSubspace
#print axioms fiberConstantSubspace
#check @normalizedFiberLift_mem
#print axioms normalizedFiberLift_mem
#check @normalizedFiberLift_surjective_subspace
#print axioms normalizedFiberLift_surjective_subspace
#check @normalizedFiberEquiv
#print axioms normalizedFiberEquiv
#check @normalizedFiberEquiv_apply
#print axioms normalizedFiberEquiv_apply
#check @diagonalAction
#print axioms diagonalAction
#check @normalizedFiberLift_intertwines
#print axioms normalizedFiberLift_intertwines
#check @fiberConstant_iff_group_invariant
#print axioms fiberConstant_iff_group_invariant

/-! ## Descent of source operators along the normalized lift

An operator on source amplitudes descends to record amplitudes if and only if it keeps
fiber-constant amplitudes fiber-constant; the descended operator is unique. Operators that
commute with a group whose orbits are the fibers descend, and a diagonal multiplier descends
if and only if it is constant on fibers. -/

section OperatorDescent

variable {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]

/-- The normalized lift is injective on record amplitudes. -/
theorem normalizedFiberLift_injective (q : X → Q) (hq : Function.Surjective q) :
    Function.Injective (normalizedFiberLift q) :=
  (normalizedFiberIsometry q hq).injective

/-- An operator on source amplitudes descends along the normalized lift if and only if it maps
fiber-constant amplitudes to fiber-constant amplitudes. -/
theorem descends_iff_preserves_fiberConstant (q : X → Q) (hq : Function.Surjective q)
    (A : HilbertCarrier X →ₗ[ℂ] HilbertCarrier X) :
    (∃ B : HilbertCarrier Q →ₗ[ℂ] HilbertCarrier Q,
        ∀ v, normalizedFiberLift q (B v) = A (normalizedFiberLift q v)) ↔
      ∀ v ∈ fiberConstantSubspace q, A v ∈ fiberConstantSubspace q := by
  constructor
  · rintro ⟨B, hB⟩ v hv
    obtain ⟨w, hw⟩ := normalizedFiberLift_surjective_subspace q hq ⟨v, hv⟩
    have hw' : normalizedFiberLift q w = v := hw
    rw [← hw', ← hB w]
    exact normalizedFiberLift_mem q (B w)
  · intro hA
    let E := normalizedFiberEquiv q hq
    let Ares : fiberConstantSubspace q →ₗ[ℂ] fiberConstantSubspace q := A.restrict hA
    refine ⟨E.symm.toLinearEquiv.toLinearMap ∘ₗ Ares ∘ₗ E.toLinearEquiv.toLinearMap, ?_⟩
    intro v
    have key : ∀ u : fiberConstantSubspace q, normalizedFiberLift q (E.symm u) = u.1 :=
      fun u => congrArg Subtype.val (E.apply_symm_apply u)
    exact key (Ares (E v))

/-- A descended operator is determined by the source operator. -/
theorem descended_unique (q : X → Q) (hq : Function.Surjective q)
    (A : HilbertCarrier X →ₗ[ℂ] HilbertCarrier X)
    {B B' : HilbertCarrier Q →ₗ[ℂ] HilbertCarrier Q}
    (hB : ∀ v, normalizedFiberLift q (B v) = A (normalizedFiberLift q v))
    (hB' : ∀ v, normalizedFiberLift q (B' v) = A (normalizedFiberLift q v)) :
    B = B' :=
  LinearMap.ext fun v => normalizedFiberLift_injective q hq ((hB v).trans (hB' v).symm)

/-- Translation of source amplitudes by a group element. -/
noncomputable def translateAmplitude {G : Type*} [Group G] [MulAction G X] (g : G)
    (v : HilbertCarrier X) : HilbertCarrier X :=
  (EuclideanSpace.equiv X ℂ).symm (fun x => v (g • x))

omit [Fintype X] [Fintype Q] [DecidableEq Q] in
theorem translateAmplitude_apply {G : Type*} [Group G] [MulAction G X] (g : G)
    (v : HilbertCarrier X) (x : X) : translateAmplitude g v x = v (g • x) := rfl

omit [Fintype Q] [DecidableEq Q] in
/-- An operator commuting with every translation keeps orbit-constant amplitudes orbit-constant. -/
theorem equivariant_preserves_fiberConstant {G : Type*} [Group G] [MulAction G X]
    (q : X → Q) (horbit : ∀ x x', q x = q x' ↔ ∃ g : G, g • x = x')
    (A : HilbertCarrier X →ₗ[ℂ] HilbertCarrier X)
    (hA : ∀ (g : G) (v : HilbertCarrier X), A (translateAmplitude g v) = translateAmplitude g (A v)) :
    ∀ v ∈ fiberConstantSubspace q, A v ∈ fiberConstantSubspace q := by
  intro v hv
  rw [fiberConstant_iff_group_invariant q horbit] at hv ⊢
  intro g x
  have hfix : translateAmplitude g v = v := by
    ext y
    exact hv g y
  have hx := congrArg (fun w : HilbertCarrier X => w x) (hA g v)
  simp only [hfix, translateAmplitude_apply] at hx
  exact hx.symm

/-- On orbit fibers, every operator commuting with the translations descends to a unique
operator on record amplitudes. -/
theorem equivariant_descends_unique {G : Type*} [Group G] [MulAction G X]
    (q : X → Q) (hq : Function.Surjective q)
    (horbit : ∀ x x', q x = q x' ↔ ∃ g : G, g • x = x')
    (A : HilbertCarrier X →ₗ[ℂ] HilbertCarrier X)
    (hA : ∀ (g : G) (v : HilbertCarrier X), A (translateAmplitude g v) = translateAmplitude g (A v)) :
    ∃! B : HilbertCarrier Q →ₗ[ℂ] HilbertCarrier Q,
      ∀ v, normalizedFiberLift q (B v) = A (normalizedFiberLift q v) := by
  obtain ⟨B, hB⟩ := (descends_iff_preserves_fiberConstant q hq A).mpr
    (equivariant_preserves_fiberConstant q horbit A hA)
  exact ⟨B, hB, fun B' hB' => descended_unique q hq A hB' hB⟩

end OperatorDescent

section DiagonalDescent

variable {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]

/-- Multiplication by a source function descends if and only if the function is constant on
every observation fiber. -/
theorem diagonal_descends_iff (q : X → Q) (hq : Function.Surjective q) (d : X → ℂ) :
    (∃ B : HilbertCarrier Q →ₗ[ℂ] HilbertCarrier Q,
        ∀ v, normalizedFiberLift q (B v) = diagonalAction d (normalizedFiberLift q v)) ↔
      ∀ x x', q x = q x' → d x = d x' := by
  rw [descends_iff_preserves_fiberConstant q hq]
  constructor
  · intro h x x' hxx'
    have hc : (EuclideanSpace.equiv X ℂ).symm (fun _ => (1 : ℂ)) ∈ fiberConstantSubspace q := by
      intro y y' _
      rfl
    have hv := h _ hc x x' hxx'
    change d x * 1 = d x' * 1 at hv
    simpa using hv
  · intro hd v hv x x' hxx'
    change d x * v x = d x' * v x'
    rw [hd x x' hxx', hv x x' hxx']

end DiagonalDescent

/-- Control: on a two-point source over a one-point record, multiplication by the indicator of
one point does not descend. -/
theorem indicator_not_descends :
    ¬ ∃ B : HilbertCarrier Unit →ₗ[ℂ] HilbertCarrier Unit,
      ∀ v, normalizedFiberLift (fun _ : Bool => ()) (B v) =
        diagonalAction (fun b : Bool => if b then (1 : ℂ) else 0)
          (normalizedFiberLift (fun _ : Bool => ()) v) := by
  rw [diagonal_descends_iff _ (fun _ => ⟨true, rfl⟩)]
  intro h
  have hv := h true false rfl
  norm_num at hv

#check @normalizedFiberLift_injective
#print axioms normalizedFiberLift_injective
#check @descends_iff_preserves_fiberConstant
#print axioms descends_iff_preserves_fiberConstant
#check @descended_unique
#print axioms descended_unique
#check @translateAmplitude
#print axioms translateAmplitude
#check @translateAmplitude_apply
#print axioms translateAmplitude_apply
#check @equivariant_preserves_fiberConstant
#print axioms equivariant_preserves_fiberConstant
#check @equivariant_descends_unique
#print axioms equivariant_descends_unique
#check @diagonal_descends_iff
#print axioms diagonal_descends_iff
#check @indicator_not_descends
#print axioms indicator_not_descends

end OperatorKO7.Meta.BoundaryOperator.Foundations.FreeHilbertRealization
