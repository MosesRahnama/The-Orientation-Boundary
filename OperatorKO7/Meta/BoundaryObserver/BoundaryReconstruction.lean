import Mathlib.Algebra.Star.Subalgebra
import OperatorKO7.Meta.ReverseBridge.QMLaw_EntropyLaws
import OperatorKO7.Meta.Physics.BuschGleasonConverse
import OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction

/-!
# Finite observation-fiber algebra and state representation

Graph: notes/universal-roadmap/UNIVERSAL-OBSERVATION-PROOF-GRAPH.md, M5_1 and M5_2.
Author: observation-reconstruction. Compiler owner: observation-execution.
LASOT 2.3 read in full at Code-Audits/LEAN_AGENT_AUDIT_SOURCE_OF_TRUTH.md.
Status: source candidate; no compiler or axiom inspection performed by this author.

The algebra uses native matrices, matrix multiplication and conjugate transpose.
The finite carrier is Fin n, including n = 0. The record type need not be finite.
Complex scalars are supplied, not reconstructed from the observation map.
-/

set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators Classical ComplexOrder

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Native matrix unit; the following lemma identifies the entrywise convention. -/
def unitEntry {n : ℕ} (i j : Fin n) : Mat n := Matrix.single i j 1

theorem unitEntry_apply {n : ℕ} (i j r c : Fin n) :
    unitEntry i j r c = if r = i ∧ c = j then 1 else 0 := by
  simp only [unitEntry, Matrix.single, Matrix.of_apply, eq_comm]

/-- The permutation sends the column basis vector at j to the one at s j. -/
def permutationMat {n : ℕ} (s : Equiv.Perm (Fin n)) : Mat n :=
  Matrix.of fun r c => if r = s c then 1 else 0

abbrev dagger {n : ℕ} (a : Mat n) : Mat n := a.conjTranspose
abbrev tr {n : ℕ} (a : Mat n) : ℂ := a.trace

theorem dagger_entrywise {n : ℕ} (a : Mat n) :
    dagger a = (fun i j => star (a j i)) := rfl

theorem tr_entrywise {n : ℕ} (a : Mat n) : tr a = ∑ i, a i i := rfl

/-- The full sandwich identity, with the direction of the permutation explicit. -/
theorem matrix_unit_sandwich {n : ℕ} (i j : Fin n)
    (s : Equiv.Perm (Fin n)) (h : s j = i) :
    unitEntry i i * permutationMat s * unitEntry j j = unitEntry i j := by
  unfold unitEntry
  rw [Matrix.single_mul_mul_single]
  simp [permutationMat, h]

theorem unitEntry_mul {n : ℕ} (i j k : Fin n) :
    unitEntry i j * unitEntry j k = unitEntry i k := by
  simp [unitEntry]

theorem unitEntry_mul_of_ne {n : ℕ} (i j k l : Fin n) (h : j ≠ k) :
    unitEntry i j * unitEntry k l = 0 := by
  exact Matrix.single_mul_single_of_ne (1 : ℂ) i j k h 1

theorem unitEntry_adjoint {n : ℕ} (i j : Fin n) :
    dagger (unitEntry i j) = unitEntry j i := by
  simp [unitEntry]

/-- Cross-fiber entries vanish. No surjectivity or nonempty-fiber premise. -/
def FiberClosed {n : ℕ} {Q : Type*} (q : Fin n → Q) (a : Mat n) : Prop :=
  ∀ i j, q i ≠ q j → a i j = 0

theorem fiberClosed_zero {n : ℕ} {Q : Type*} (q : Fin n → Q) :
    FiberClosed q 0 := by
  intro i j h
  rfl

theorem fiberClosed_one {n : ℕ} {Q : Type*} (q : Fin n → Q) :
    FiberClosed q 1 := by
  intro i j h
  have hij : i ≠ j := fun e => h (congrArg q e)
  simp [hij]

theorem fiberClosed_add {n : ℕ} {Q : Type*} {q : Fin n → Q} {a b : Mat n}
    (ha : FiberClosed q a) (hb : FiberClosed q b) : FiberClosed q (a + b) := by
  intro i j h
  change a i j + b i j = 0
  rw [ha i j h, hb i j h, add_zero]

theorem fiberClosed_mul {n : ℕ} {Q : Type*} {q : Fin n → Q} {a b : Mat n}
    (ha : FiberClosed q a) (hb : FiberClosed q b) : FiberClosed q (a * b) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hik : q i = q k
  · have hkj : q k ≠ q j := fun h => hij (hik.trans h)
    rw [hb k j hkj, mul_zero]
  · rw [ha i k hik, zero_mul]

theorem fiberClosed_adjoint {n : ℕ} {Q : Type*} {q : Fin n → Q} {a : Mat n}
    (ha : FiberClosed q a) : FiberClosed q (dagger a) := by
  intro i j h
  change star (a j i) = 0
  rw [ha j i (Ne.symm h), star_zero]

theorem fiberClosed_smul {n : ℕ} {Q : Type*} {q : Fin n → Q} {a : Mat n}
    (z : ℂ) (ha : FiberClosed q a) : FiberClosed q (z • a) := by
  intro i j h
  change z * a i j = 0
  rw [ha i j h, mul_zero]

/-- The entire closure assertion of the specification, on native operations. -/
theorem fiber_algebra_closed {n : ℕ} {Q : Type*} {q : Fin n → Q} {a b : Mat n}
    (ha : FiberClosed q a) (hb : FiberClosed q b) :
    FiberClosed q (a + b) ∧ FiberClosed q (a * b) ∧ FiberClosed q (dagger a) :=
  ⟨fiberClosed_add ha hb, fiberClosed_mul ha hb, fiberClosed_adjoint ha⟩

/-- Native unital star subalgebra, not an independently assigned multiplication. -/
def fiberAlgebra {n : ℕ} {Q : Type*} (q : Fin n → Q) : StarSubalgebra ℂ (Mat n) where
  carrier := {a | FiberClosed q a}
  zero_mem' := fiberClosed_zero q
  one_mem' := fiberClosed_one q
  add_mem' := fiberClosed_add
  mul_mem' := fiberClosed_mul
  algebraMap_mem' z := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact fiberClosed_smul z (fiberClosed_one q)
  star_mem' := fiberClosed_adjoint

theorem fiberClosed_unitEntry {n : ℕ} {Q : Type*} {q : Fin n → Q}
    (i j : Fin n) (hij : q i = q j) : FiberClosed q (unitEntry i j) := by
  intro r c hrc
  rw [unitEntry_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hrc hij

theorem fiberClosed_permutation {n : ℕ} {Q : Type*} {q : Fin n → Q}
    (s : Equiv.Perm (Fin n)) (hs : ∀ i, q (s i) = q i) :
    FiberClosed q (permutationMat s) := by
  intro i j hij
  change (if i = s j then (1 : ℂ) else 0) = 0
  rw [if_neg]
  intro h
  exact hij ((congrArg q h).trans (hs j))

/-- The closure conditions are the specification's complete generator interface. -/
def GeneratorClosed {n : ℕ} {Q : Type*} (q : Fin n → Q) (S : Set (Mat n)) : Prop :=
  0 ∈ S ∧ (∀ i, unitEntry i i ∈ S) ∧
  (∀ s : Equiv.Perm (Fin n), (∀ i, q (s i) = q i) → permutationMat s ∈ S) ∧
  (∀ a ∈ S, ∀ b ∈ S, a + b ∈ S ∧ a * b ∈ S) ∧
  (∀ a ∈ S, dagger a ∈ S) ∧ ∀ z : ℂ, ∀ a ∈ S, z • a ∈ S

def Generated {n : ℕ} {Q : Type*} (q : Fin n → Q) (a : Mat n) : Prop :=
  ∀ S : Set (Mat n), GeneratorClosed q S → a ∈ S

theorem fiber_preserving_swap {n : ℕ} {Q : Type*} {q : Fin n → Q}
    (i j : Fin n) (hij : q i = q j) : ∀ k, q (Equiv.swap i j k) = q k := by
  intro k
  by_cases hki : k = i
  · subst k
    simpa using hij.symm
  · by_cases hkj : k = j
    · subst k
      simpa using hij
    · simp [Equiv.swap_apply_def, hki, hkj]

theorem generatorClosed_contains_units {n : ℕ} {Q : Type*} {q : Fin n → Q}
    {S : Set (Mat n)} (hS : GeneratorClosed q S) (i j : Fin n) (hij : q i = q j) :
    unitEntry i j ∈ S := by
  have hperm := hS.2.2.1 (Equiv.swap i j) (fiber_preserving_swap i j hij)
  have hleft := (hS.2.2.2.1 _ (hS.2.1 i) _ hperm).2
  have hboth := (hS.2.2.2.1 _ hleft _ (hS.2.1 j)).2
  rw [matrix_unit_sandwich i j (Equiv.swap i j) (by simp)] at hboth
  exact hboth

/-- Every fiber-closed matrix belongs to every set with the generator laws. -/
theorem fiberClosed_mem_generatorClosed {n : ℕ} {Q : Type*} {q : Fin n → Q}
    {a : Mat n} (ha : FiberClosed q a) {S : Set (Mat n)} (hS : GeneratorClosed q S) :
    a ∈ S := by
  have hsum : ∀ (t : Finset (Fin n)) (f : Fin n → Mat n),
      (∀ i ∈ t, f i ∈ S) → (∑ i ∈ t, f i) ∈ S := by
    intro t f
    induction t using Finset.induction_on with
    | empty =>
      intro _hf
      simpa using hS.1
    | @insert i t hi ih =>
      intro hf
      rw [Finset.sum_insert hi]
      exact (hS.2.2.2.1 _ (hf i (Finset.mem_insert_self i t)) _
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))).1
  rw [Matrix.matrix_eq_sum_single a]
  apply hsum Finset.univ
  intro i hi
  apply hsum Finset.univ
  intro j hj
  by_cases hij : q i = q j
  · rw [OperatorKO7.Meta.Physics.BuschGleasonFinite.single_eq_smul]
    exact hS.2.2.2.2.2 (a i j) _ (generatorClosed_contains_units hS i j hij)
  · rw [ha i j hij, Matrix.single_zero]
    exact hS.1

/-- Full BlockGenerationGoal: both directions quantify over every input matrix. -/
theorem generated_iff_fiberClosed {n : ℕ} {Q : Type*} (q : Fin n → Q) (a : Mat n) :
    Generated q a ↔ FiberClosed q a := by
  constructor
  · intro h
    apply h {b | FiberClosed q b}
    refine ⟨fiberClosed_zero q, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact fiberClosed_unitEntry i i rfl
    · exact fiberClosed_permutation
    · intro b hb c hc
      exact ⟨fiberClosed_add hb hc, fiberClosed_mul hb hc⟩
    · intro b hb
      exact fiberClosed_adjoint hb
    · intro z b hb
      exact fiberClosed_smul z hb
  · intro ha S hS
    exact fiberClosed_mem_generatorClosed ha hS

/-- Actual generators for the native star-algebra closure. -/
def fiberGenerators {n : ℕ} {Q : Type*} (q : Fin n → Q) : Set (Mat n) :=
  {a | (∃ i, a = unitEntry i i) ∨
    ∃ s : Equiv.Perm (Fin n), (∀ i, q (s i) = q i) ∧ a = permutationMat s}

/-- Native star-adjoin equals the full fiber algebra, not only its generator set. -/
theorem star_adjoin_fiberGenerators {n : ℕ} {Q : Type*} (q : Fin n → Q) :
    StarAlgebra.adjoin ℂ (fiberGenerators q) = fiberAlgebra q := by
  apply le_antisymm
  · apply StarAlgebra.adjoin_le
    intro a ha
    rcases ha with ⟨i, rfl⟩ | ⟨s, hs, rfl⟩
    · exact fiberClosed_unitEntry i i rfl
    · exact fiberClosed_permutation s hs
  · intro a ha
    apply fiberClosed_mem_generatorClosed ha
    let S := StarAlgebra.adjoin ℂ (fiberGenerators q)
    change GeneratorClosed q (S : Set (Mat n))
    refine ⟨zero_mem S, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact StarAlgebra.subset_adjoin ℂ (fiberGenerators q) (Or.inl ⟨i, rfl⟩)
    · intro s hs
      exact StarAlgebra.subset_adjoin ℂ (fiberGenerators q) (Or.inr ⟨s, hs, rfl⟩)
    · intro b hb c hc
      exact ⟨add_mem hb hc, mul_mem hb hc⟩
    · intro b hb
      exact star_mem hb
    · intro z b hb
      exact S.smul_mem hb z

/-! ## Block restriction and zero extension -/

abbrev Fiber {n : ℕ} {Q : Type*} (q : Fin n → Q) (y : Q) :=
  {i : Fin n // q i = y}

abbrev BlockFamily {n : ℕ} {Q : Type*} (q : Fin n → Q) :=
  (y : Q) → Matrix (Fiber q y) (Fiber q y) ℂ

def blockRestriction {n : ℕ} {Q : Type*} (q : Fin n → Q) (a : Mat n) :
    BlockFamily q := fun _ i j => a i.val j.val

/-- Original within-block occurrence indices; cross-block entries are zero. -/
def blockExtension {n : ℕ} {Q : Type*} {q : Fin n → Q} (b : BlockFamily q) : Mat n :=
  Matrix.of fun i j => if h : q i = q j then
    b (q i) ⟨i, rfl⟩ ⟨j, h.symm⟩ else 0

theorem blockExtension_fiberClosed {n : ℕ} {Q : Type*} {q : Fin n → Q}
    (b : BlockFamily q) : FiberClosed q (blockExtension b) := by
  intro i j h
  simp [blockExtension, h]

theorem blockExtension_blockRestriction {n : ℕ} {Q : Type*} {q : Fin n → Q}
    (a : Mat n) (ha : FiberClosed q a) : blockExtension (blockRestriction q a) = a := by
  ext i j
  by_cases h : q i = q j
  · simp [blockExtension, blockRestriction, h]
  · simp [blockExtension, h, ha i j h]

theorem blockRestriction_blockExtension {n : ℕ} {Q : Type*} {q : Fin n → Q}
    (b : BlockFamily q) : blockRestriction q (blockExtension b) = b := by
  funext y
  ext i j
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  subst y
  simp [blockRestriction, blockExtension, hj]

/-- Full-carrier sums equal fiber sums when every excluded term vanishes. -/
theorem sum_over_fiber {n : ℕ} {Q : Type*} (q : Fin n → Q) (y : Q)
    (f : Fin n → ℂ) (hf : ∀ k, q k ≠ y → f k = 0) :
    (∑ k, f k) = ∑ k : Fiber q y, f k.val := by
  let s := Finset.univ.filter (fun k => q k = y)
  calc
    (∑ k, f k) = ∑ k ∈ s, f k := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k hk hks
      apply hf k
      intro h
      exact hks (Finset.mem_filter.mpr ⟨hk, h⟩)
    _ = ∑ k : Fiber q y, f k.val :=
      Finset.sum_subtype s (by intro k; simp [s]) f

/-- The omitted terms in native matrix multiplication are proved zero. -/
theorem blockRestriction_mul {n : ℕ} {Q : Type*} {q : Fin n → Q}
    {a : Mat n} (ha : FiberClosed q a) (b : Mat n) :
    blockRestriction q (a * b) = blockRestriction q a * blockRestriction q b := by
  funext y
  ext i j
  change (∑ k : Fin n, a i.val k * b k j.val) =
    ∑ k : Fiber q y, a i.val k.val * b k.val j.val
  apply sum_over_fiber q y
  intro k hk
  have hik : q i.val ≠ q k := by
    intro h
    exact hk (h.symm.trans i.property)
  rw [ha i.val k hik, zero_mul]

/-- Native star-algebra equivalence with explicit mutually inverse maps. -/
def fiberBlockEquiv {n : ℕ} {Q : Type*} (q : Fin n → Q) :
    fiberAlgebra q ≃⋆ₐ[ℂ] BlockFamily q where
  toFun a := blockRestriction q a.val
  invFun b := ⟨blockExtension b, blockExtension_fiberClosed b⟩
  left_inv a := Subtype.ext (blockExtension_blockRestriction a.val a.property)
  right_inv b := blockRestriction_blockExtension b
  map_add' _ _ := rfl
  map_mul' a b := blockRestriction_mul a.property b.val
  map_smul' _ _ := rfl
  map_star' _ := rfl

/-- Exact entry-preserving BlockDecompositionGoal, strengthened by fiberBlockEquiv. -/
theorem block_decomposition {n : ℕ} {Q : Type*} (q : Fin n → Q) :
    ∃ e : {a : Mat n // FiberClosed q a} ≃ BlockFamily q,
      ∀ a y i j, e a y i j = a.val i.val j.val :=
  ⟨(fiberBlockEquiv q).toRingEquiv.toEquiv, fun _ _ _ _ => rfl⟩

theorem blockEquiv_apply {n : ℕ} {Q : Type*} (q : Fin n → Q)
    (a : fiberAlgebra q) (y : Q) (i j : Fiber q y) :
    fiberBlockEquiv q a y i j = a.val i.val j.val := rfl

theorem blockEquiv_one {n : ℕ} {Q : Type*} (q : Fin n → Q) :
    fiberBlockEquiv q 1 = 1 := map_one (fiberBlockEquiv q)

theorem blockExtension_add {n : ℕ} {Q : Type*} {q : Fin n → Q}
    (a b : BlockFamily q) : blockExtension (a + b) = blockExtension a + blockExtension b := by
  exact congrArg Subtype.val ((fiberBlockEquiv q).symm.map_add a b)

theorem blockExtension_mul {n : ℕ} {Q : Type*} {q : Fin n → Q}
    (a b : BlockFamily q) : blockExtension (a * b) = blockExtension a * blockExtension b := by
  exact congrArg Subtype.val ((fiberBlockEquiv q).symm.map_mul a b)

theorem blockExtension_adjoint {n : ℕ} {Q : Type*} {q : Fin n → Q}
    (a : BlockFamily q) : blockExtension (star a) = dagger (blockExtension a) := by
  exact congrArg Subtype.val (map_star (fiberBlockEquiv q).symm a)

theorem blockExtension_smul {n : ℕ} {Q : Type*} {q : Fin n → Q}
    (z : ℂ) (a : BlockFamily q) : blockExtension (z • a) = z • blockExtension a := by
  exact congrArg Subtype.val (map_smul (fiberBlockEquiv q).symm z a)

theorem blockExtension_one {n : ℕ} {Q : Type*} (q : Fin n → Q) :
    blockExtension (1 : BlockFamily q) = 1 := by
  exact congrArg Subtype.val (map_one (fiberBlockEquiv q).symm)

/-- Empty blocks contribute no artificial degree of freedom. -/
theorem empty_fiber_block_unique {n : ℕ} {Q : Type*} {q : Fin n → Q}
    (y : Q) (hy : ∀ i, q i ≠ y) (a b : Matrix (Fiber q y) (Fiber q y) ℂ) : a = b := by
  ext i j
  exact False.elim (hy i.val i.property)

theorem zero_carrier_generated {Q : Type*} (q : Fin 0 → Q) (a : Mat 0) : Generated q a := by
  apply (generated_iff_fiberClosed q a).2
  intro i
  exact Fin.elim0 i

/-- Singleton observation fibers leave precisely the diagonal algebra. -/
theorem injective_fibers_iff_diagonal {n : ℕ} {Q : Type*} (q : Fin n → Q)
    (hq : Function.Injective q) (a : Mat n) :
    FiberClosed q a ↔ a = Matrix.diagonal a.diag := by
  constructor
  · intro ha
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · have hqij : q i ≠ q j := fun h => hij (hq h)
      simp [hij, ha i j hqij]
  · intro ha i j hqij
    have hij : i ≠ j := fun h => hqij (congrArg q h)
    rw [ha]
    simp [hij]

theorem constant_fiber_generates_all {n : ℕ} {Q : Type*} (y : Q) (a : Mat n) :
    Generated (fun _ : Fin n => y) a := by
  apply (generated_iff_fiberClosed _ a).2
  intro i j h
  exact False.elim (h rfl)

/-! ## Relabeling as conjugation -/

theorem permutationMat_mul_apply {n : ℕ} (s : Equiv.Perm (Fin n))
    (a : Mat n) (i j : Fin n) :
    (permutationMat s * a) i j = a (s.symm i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (s.symm i)]
  · simp [permutationMat]
  · intro k _hk hki
    have h : i ≠ s k := by
      intro e
      apply hki
      rw [e, s.symm_apply_apply]
    simp [permutationMat, h]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem mul_permutationMat_adjoint_apply {n : ℕ} (s : Equiv.Perm (Fin n))
    (a : Mat n) (i j : Fin n) :
    (a * dagger (permutationMat s)) i j = a i (s.symm j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (s.symm j)]
  · simp [permutationMat]
  · intro k _hk hkj
    have h : j ≠ s k := by
      intro e
      apply hkj
      rw [e, s.symm_apply_apply]
    simp [permutationMat, h]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem permutation_conjugation_apply {n : ℕ} (s : Equiv.Perm (Fin n))
    (a : Mat n) (i j : Fin n) :
    (permutationMat s * a * dagger (permutationMat s)) i j = a (s.symm i) (s.symm j) := by
  rw [mul_permutationMat_adjoint_apply, permutationMat_mul_apply]

theorem gauge_conjugation_preserves_fibers {n : ℕ} {Q : Type*} {q : Fin n → Q}
    (s : Equiv.Perm (Fin n)) (hs : ∀ i, q (s i) = q i)
    {a : Mat n} (ha : FiberClosed q a) :
    FiberClosed q (permutationMat s * a * dagger (permutationMat s)) := by
  intro i j hij
  rw [permutation_conjugation_apply]
  apply ha
  intro h
  have hi : q i = q (s.symm i) := by simpa using hs (s.symm i)
  have hj : q j = q (s.symm j) := by simpa using hs (s.symm j)
  exact hij (hi.trans (h.trans hj.symm))

/-! ## M5.2: entrywise/native positivity and density representation -/

/-- The specification's PSD convention, including its explicit double sum. -/
def EntrywisePSD {n : ℕ} (a : Mat n) : Prop :=
  a = dagger a ∧ ∀ v : Fin n → ℂ,
    0 ≤ (∑ i, ∑ j, star (v i) * a i j * v j).re

theorem form_eq_dotProduct {n : ℕ} (a : Mat n) (v w : Fin n → ℂ) :
    QuantumReconstruction.form a v w = star v ⬝ᵥ (a *ᵥ w) := by
  simp only [QuantumReconstruction.form, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum, mul_assoc]

theorem hermitian_iff_reportHermitian {n : ℕ} (a : Mat n) :
    a.IsHermitian ↔ QuantumReconstruction.Hermitian a := by
  constructor
  · intro h i j
    exact congrArg (fun b : Mat n => b j i) h.eq
  · intro h
    change a.conjTranspose = a
    ext i j
    exact h j i

theorem hermitian_quadratic_im_zero {n : ℕ} {a : Mat n}
    (ha : a.IsHermitian) (v : Fin n → ℂ) : (star v ⬝ᵥ (a *ᵥ v)).im = 0 := by
  have h : star (star v ⬝ᵥ (a *ᵥ v)) = star v ⬝ᵥ (a *ᵥ v) := by
    rw [← Matrix.star_dotProduct (a *ᵥ v) v, Matrix.star_mulVec,
      ha.eq, ← Matrix.dotProduct_mulVec]
  have him := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

/-- Both directions bridge the actual quadratic forms and the Hermitian condition. -/
theorem entrywisePSD_iff_posSemidef {n : ℕ} (a : Mat n) :
    EntrywisePSD a ↔ a.PosSemidef := by
  constructor
  · rintro ⟨hh, hp⟩
    have hherm : a.IsHermitian := hh.symm
    refine ⟨hherm, ?_⟩
    intro v
    apply Complex.nonneg_iff.mpr
    refine ⟨?_, (hermitian_quadratic_im_zero hherm v).symm⟩
    have hpv : 0 ≤ (QuantumReconstruction.form a v v).re := hp v
    simpa only [form_eq_dotProduct] using hpv
  · intro ha
    refine ⟨ha.1.eq.symm, ?_⟩
    intro v
    change 0 ≤ (QuantumReconstruction.form a v v).re
    rw [form_eq_dotProduct]
    exact (Complex.nonneg_iff.mp (ha.2 v)).1

abbrev Density (n : ℕ) :=
  {a : Mat n // OperatorKO7.Meta.Physics.BuschGleasonFinite.IsDensity a}

abbrev Effect (n : ℕ) :=
  {a : Mat n // OperatorKO7.Meta.Physics.BuschGleasonFinite.IsEffect a}

def EntrywiseDensity (n : ℕ) := {a : Mat n // EntrywisePSD a ∧ tr a = 1}
def EntrywiseEffect (n : ℕ) := {a : Mat n // EntrywisePSD a ∧ EntrywisePSD (1 - a)}

/-- Identity on entries; the native positivity convention is proved equivalent. -/
def densityConventionEquiv (n : ℕ) : EntrywiseDensity n ≃ Density n where
  toFun a := ⟨a.val, (entrywisePSD_iff_posSemidef a.val).mp a.property.1, a.property.2⟩
  invFun a := ⟨a.val, (entrywisePSD_iff_posSemidef a.val).mpr a.property.1, a.property.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def effectConventionEquiv (n : ℕ) : EntrywiseEffect n ≃ Effect n where
  toFun a := ⟨a.val, (entrywisePSD_iff_posSemidef a.val).mp a.property.1,
    (entrywisePSD_iff_posSemidef (1 - a.val)).mp a.property.2⟩
  invFun a := ⟨a.val, (entrywisePSD_iff_posSemidef a.val).mpr a.property.1,
    (entrywisePSD_iff_posSemidef (1 - a.val)).mpr a.property.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Source functional with the specification's real-part/imaginary-part positivity. -/
structure PositiveFunctional (n : ℕ) where
  value : Mat n →ₗ[ℂ] ℂ
  normalized : value 1 = 1
  positive : ∀ a, EntrywisePSD a → 0 ≤ (value a).re ∧ (value a).im = 0

theorem positiveFunctional_native {n : ℕ} (f : PositiveFunctional n) :
    OperatorKO7.Meta.Physics.BuschGleasonConverse.IsPositiveFunctional f.value := by
  intro a ha
  obtain ⟨hr, hi⟩ := f.positive a ((entrywisePSD_iff_posSemidef a).mpr ha)
  exact Complex.nonneg_iff.mpr ⟨hr, hi.symm⟩

/-- Source-read donor derives the density matrix; representation is not an input field. -/
theorem density_representation {n : ℕ} (f : PositiveFunctional n) :
    ∃! ρ : Density n, ∀ a, f.value a = tr (ρ.val * a) := by
  obtain ⟨ρ, hρ, hu⟩ :=
    OperatorKO7.Meta.Physics.BuschGleasonConverse.density_functional_correspondence
      f.value (positiveFunctional_native f) f.normalized
  refine ⟨⟨ρ, hρ.1⟩, fun a => (hρ.2 a).symm, ?_⟩
  intro σ hσ
  apply Subtype.ext
  exact hu σ.val ⟨σ.property, fun a => (hσ a).symm⟩

/-- Exact StateFunctionalGoal conclusion in the entrywise convention, for every matrix. -/
theorem entrywise_density_representation {n : ℕ} (f : PositiveFunctional n) :
    ∃! ρ : EntrywiseDensity n, ∀ a, f.value a = tr (ρ.val * a) := by
  obtain ⟨ρ, hρ, hu⟩ := density_representation f
  refine ⟨(densityConventionEquiv n).symm ρ, hρ, ?_⟩
  intro σ hσ
  apply (densityConventionEquiv n).injective
  simpa using hu (densityConventionEquiv n σ) hσ

/-- Probability from the same density and effect matrices. -/
def probability {n : ℕ} (ρ : Density n) (e : Effect n) : ℝ :=
  (tr (ρ.val * e.val)).re

theorem probability_mem_unitInterval {n : ℕ} (ρ : Density n) (e : Effect n) :
    0 ≤ probability ρ e ∧ probability ρ e ≤ 1 := by
  obtain ⟨hlo, hhi⟩ :=
    OperatorKO7.Meta.Physics.BuschGleasonFinite.bornMeasure_mem_unitInterval
      ρ.property e.property
  refine ⟨(Complex.nonneg_iff.mp hlo).1, ?_⟩
  have h := (Complex.nonneg_iff.mp (sub_nonneg.mpr hhi)).1
  change 0 ≤ (1 - tr (ρ.val * e.val)).re at h
  simp only [Complex.sub_re, Complex.one_re] at h
  change (tr (ρ.val * e.val)).re ≤ 1
  linarith

/-- Actual population and interference reports reconstruct every native density matrix. -/
theorem density_reconstruct_reports {n : ℕ} (ρ : Density n) :
    QuantumReconstruction.reconstruct (QuantumReconstruction.population ρ.val)
      (QuantumReconstruction.plusReport ρ.val) (QuantumReconstruction.phaseReport ρ.val) = ρ.val :=
  QuantumReconstruction.reconstruct_reports ρ.val
    ((hermitian_iff_reportHermitian ρ.val).mp ρ.property.1.1)

theorem density_eq_iff_reports {n : ℕ} (ρ σ : Density n) :
    ρ = σ ↔
      (∀ i, QuantumReconstruction.population ρ.val i = QuantumReconstruction.population σ.val i) ∧
      (∀ i j, i ≠ j → QuantumReconstruction.plusReport ρ.val i j =
        QuantumReconstruction.plusReport σ.val i j) ∧
      (∀ i j, i ≠ j → QuantumReconstruction.phaseReport ρ.val i j =
        QuantumReconstruction.phaseReport σ.val i j) := by
  constructor
  · intro h
    subst σ
    exact ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  · rintro ⟨hp, hr, hi⟩
    apply Subtype.ext
    exact QuantumReconstruction.reports_determine_state ρ.val σ.val
      ((hermitian_iff_reportHermitian ρ.val).mp ρ.property.1.1)
      ((hermitian_iff_reportHermitian σ.val).mp σ.property.1.1) hp hr hi

/-- Both phase controls are genuine native PSD, trace-one density matrices. -/
def phaseDensity (b : Bool) : Density 2 := by
  refine ⟨QuantumReconstruction.phaseMatrix b, ?_, ?_⟩
  · apply (entrywisePSD_iff_posSemidef _).mp
    refine ⟨?_, (QuantumReconstruction.phaseState b).positive⟩
    exact ((hermitian_iff_reportHermitian _).mpr
      (QuantumReconstruction.phaseMatrix_hermitian b)).eq.symm
  · change (∑ i : Fin 2, QuantumReconstruction.phaseMatrix b i i) = 1
    norm_num [QuantumReconstruction.phaseMatrix, Fin.sum_univ_two]

theorem phase_population_collision :
    (∀ i, QuantumReconstruction.population (phaseDensity true).val i =
      QuantumReconstruction.population (phaseDensity false).val i) ∧
    phaseDensity true ≠ phaseDensity false ∧
    QuantumReconstruction.plusReport (phaseDensity true).val 0 1 = 1 ∧
    QuantumReconstruction.plusReport (phaseDensity false).val 0 1 = 0 := by
  obtain ⟨hp, hne, hr, hs⟩ := QuantumReconstruction.populations_do_not_determine_state
  refine ⟨hp, ?_, hr, hs⟩
  intro h
  exact hne (congrArg Subtype.val h)

end OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction

/-! ## M5.6: finite spectral functions and physical entropy

Graph node M5_6. Source candidate; supervisor validation remains required.
The construction uses the native spectral theorem for every Hermitian matrix.
Entropy is measured in nats. No entropy law is stored as an input field.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Thermal

open scoped Kronecker

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A real spectrum embedded in the native complex diagonal matrix. -/
def realDiagonal (p : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => (p i : ℂ))

/-- Native unitary action, defined on every input matrix. -/
def rotate (u : Matrix.unitaryGroup ι ℂ) (a : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (u : Matrix ι ι ℂ) * a * star (u : Matrix ι ι ℂ)

/-- A matrix constructed from an actual unitary and its real spectral entries. -/
def spectralLift (u : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) : Matrix ι ι ℂ :=
  rotate u (realDiagonal p)

theorem rotate_trace (u : Matrix.unitaryGroup ι ℂ) (a : Matrix ι ι ℂ) :
    (rotate u a).trace = a.trace := by
  unfold rotate
  rw [Matrix.trace_mul_cycle, unitary.coe_star_mul_self, one_mul]

omit [Fintype ι] in
theorem realDiagonal_hermitian (p : ι → ℝ) : (realDiagonal p).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [realDiagonal]
  · simp [realDiagonal, hij, Ne.symm hij]

theorem rotate_hermitian (u : Matrix.unitaryGroup ι ℂ) {a : Matrix ι ι ℂ}
    (ha : a.IsHermitian) : (rotate u a).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose (u : Matrix ι ι ℂ) ha

theorem spectralLift_hermitian (u : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) :
    (spectralLift u p).IsHermitian := rotate_hermitian u (realDiagonal_hermitian p)

theorem spectralLift_trace_re (u : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) :
    (spectralLift u p).trace.re = ∑ i, p i := by
  rw [spectralLift, rotate_trace]
  simp [realDiagonal, Matrix.trace_diagonal]

/-- The spectral data are derived from the matrix, not supplied as a representation premise. -/
theorem spectralLift_eigenvalues {a : Matrix ι ι ℂ} (ha : a.IsHermitian) :
    spectralLift ha.eigenvectorUnitary ha.eigenvalues = a := by
  exact ha.spectral_theorem.symm

theorem eigenvalues_sum_trace {a : Matrix ι ι ℂ} (ha : a.IsHermitian) :
    (∑ i, ha.eigenvalues i) = a.trace.re := by
  rw [← spectralLift_trace_re ha.eigenvectorUnitary ha.eigenvalues,
    spectralLift_eigenvalues ha]

/-- The right inverse equation expressed on the underlying matrices. -/
theorem unitary_mul_adjoint (u : Matrix.unitaryGroup ι ℂ) :
    (u : Matrix ι ι ℂ) * star (u : Matrix ι ι ℂ) = 1 :=
  unitary.coe_mul_star_self u

/-- Real functional calculus from the native spectral theorem. -/
def spectralFunction {a : Matrix ι ι ℂ} (ha : a.IsHermitian) (f : ℝ → ℝ) :
    Matrix ι ι ℂ := spectralLift ha.eigenvectorUnitary (fun i => f (ha.eigenvalues i))

/-- Entropy of a Hermitian matrix; the zero extension outside that domain has no physical claim. -/
def entropy (a : Matrix ι ι ℂ) : ℝ :=
  if ha : a.IsHermitian then (spectralFunction ha Real.negMulLog).trace.re else 0

/-- The entropy is the full spectral sum, including zero eigenvalues. -/
theorem entropy_eq_eigenvalues {a : Matrix ι ι ℂ} (ha : a.IsHermitian) :
    entropy a = ∑ i, Real.negMulLog (ha.eigenvalues i) := by
  rw [entropy, dif_pos ha]
  exact spectralLift_trace_re _ _

/-- Total logarithm with log 0 = 0; relative entropy requires a separate support condition. -/
def matrixLog (a : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  if ha : a.IsHermitian then spectralFunction ha Real.log else 0

/-- Equal Hermitian representations give equal functions of the matrix, including repeated eigenvalues. -/
theorem spectralLift_function_congr (u v : Matrix.unitaryGroup ι ℂ) (p q : ι → ℝ)
    (h : spectralLift u p = spectralLift v q) (f : ℝ → ℝ) :
    spectralLift u (fun i => f (p i)) = spectralLift v (fun i => f (q i)) := by
  let t : Matrix ι ι ℂ := star (u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)
  have hinter : realDiagonal p * t = t * realDiagonal q := by
    calc
      realDiagonal p * t =
          (star (u : Matrix ι ι ℂ) * (u : Matrix ι ι ℂ)) * realDiagonal p * t := by
        rw [unitary.coe_star_mul_self, one_mul]
      _ = star (u : Matrix ι ι ℂ) * spectralLift u p * (v : Matrix ι ι ℂ) := by
        simp only [spectralLift, rotate, t, mul_assoc]
      _ = star (u : Matrix ι ι ℂ) * spectralLift v q * (v : Matrix ι ι ℂ) := by rw [h]
      _ = t * realDiagonal q := by
        simp only [spectralLift, rotate, t, mul_assoc, unitary.coe_star_mul_self, mul_one]
  have hf : realDiagonal (fun i => f (p i)) * t = t * realDiagonal (fun i => f (q i)) := by
    ext i j
    simp only [realDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have he : (p i : ℂ) * t i j = t i j * (q j : ℂ) := by
      simpa only [realDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal] using
        congrArg (fun a : Matrix ι ι ℂ => a i j) hinter
    by_cases hz : t i j = 0
    · simp [hz]
    · have hpqc : (p i : ℂ) = (q j : ℂ) :=
        mul_right_cancel₀ hz (he.trans (mul_comm _ _))
      have hpq : p i = q j := by simpa using congrArg Complex.re hpqc
      rw [hpq, mul_comm]
  calc
    spectralLift u (fun i => f (p i)) =
        (u : Matrix ι ι ℂ) * (realDiagonal (fun i => f (p i)) * t) *
          star (v : Matrix ι ι ℂ) := by
      simp only [spectralLift, rotate, t, mul_assoc, unitary_mul_adjoint, mul_one]
    _ = (u : Matrix ι ι ℂ) * (t * realDiagonal (fun i => f (q i))) *
          star (v : Matrix ι ι ℂ) := by rw [hf]
    _ = ((u : Matrix ι ι ℂ) * star (u : Matrix ι ι ℂ)) * (v : Matrix ι ι ℂ) *
          realDiagonal (fun i => f (q i)) * star (v : Matrix ι ι ℂ) := by
      simp only [t, mul_assoc]
    _ = spectralLift v (fun i => f (q i)) := by
      simp only [spectralLift, rotate, unitary_mul_adjoint, one_mul]

/-- The canonical spectral calculus agrees with every unitary diagonalization of the same matrix. -/
theorem spectralFunction_spectralLift (u : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ)
    (f : ℝ → ℝ) :
    spectralFunction (spectralLift_hermitian u p) f = spectralLift u (fun i => f (p i)) := by
  apply spectralLift_function_congr
  exact spectralLift_eigenvalues (spectralLift_hermitian u p)

theorem entropy_spectralLift (u : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) :
    entropy (spectralLift u p) = ∑ i, Real.negMulLog (p i) := by
  rw [entropy, dif_pos (spectralLift_hermitian u p), spectralFunction_spectralLift,
    spectralLift_trace_re]

theorem matrixLog_spectralLift (u : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) :
    matrixLog (spectralLift u p) = spectralLift u (fun i => Real.log (p i)) := by
  rw [matrixLog, dif_pos (spectralLift_hermitian u p), spectralFunction_spectralLift]

/-- Composition is proved for the native all-matrix action. -/
theorem rotate_spectralLift (u v : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) :
    rotate u (spectralLift v p) = spectralLift (u * v) p := by
  simp only [rotate, spectralLift, Matrix.UnitaryGroup.mul_val, StarMul.star_mul, mul_assoc]

/-- Entropy invariance is derived from spectral-calculus independence and trace invariance. -/
theorem entropy_rotate (u : Matrix.unitaryGroup ι ℂ) {a : Matrix ι ι ℂ}
    (ha : a.IsHermitian) : entropy (rotate u a) = entropy a := by
  calc
    entropy (rotate u a) =
        entropy (rotate u (spectralLift ha.eigenvectorUnitary ha.eigenvalues)) := by
      rw [spectralLift_eigenvalues ha]
    _ = ∑ i, Real.negMulLog (ha.eigenvalues i) := by
      rw [rotate_spectralLift, entropy_spectralLift]
    _ = entropy a := (entropy_eq_eigenvalues ha).symm

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Native complex Kronecker product commutes with the adjoint. -/
theorem star_tensor (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ) :
    star (a ⊗ₖ b) = star a ⊗ₖ star b := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.star_apply, Matrix.kronecker_apply, StarMul.star_mul]
  exact mul_comm _ _

/-- The tensor unitary is constructed and both inverse equations are proved. -/
def tensorUnitary (u : Matrix.unitaryGroup ι ℂ) (v : Matrix.unitaryGroup κ ℂ) :
    Matrix.unitaryGroup (ι × κ) ℂ := by
  refine ⟨(u : Matrix ι ι ℂ) ⊗ₖ (v : Matrix κ κ ℂ), ?_, ?_⟩
  · rw [star_tensor, ← Matrix.mul_kronecker_mul, unitary.coe_star_mul_self,
      unitary.coe_star_mul_self, Matrix.one_kronecker_one]
  · rw [star_tensor, ← Matrix.mul_kronecker_mul, unitary_mul_adjoint,
      unitary_mul_adjoint, Matrix.one_kronecker_one]

/-- Tensor spectra are derived for the actual Kronecker product, not assigned independently. -/
theorem tensor_spectralLift (u : Matrix.unitaryGroup ι ℂ) (v : Matrix.unitaryGroup κ ℂ)
    (p : ι → ℝ) (q : κ → ℝ) :
    spectralLift u p ⊗ₖ spectralLift v q =
      spectralLift (tensorUnitary u v) (fun x => p x.1 * q x.2) := by
  simp only [spectralLift, rotate, tensorUnitary, realDiagonal,
    Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal, star_tensor,
    Complex.ofReal_mul]

/-- Tensor entropy follows from the actual product spectrum, including every zero case. -/
theorem entropy_tensor_spectralLift (u : Matrix.unitaryGroup ι ℂ)
    (v : Matrix.unitaryGroup κ ℂ) (p : ι → ℝ) (q : κ → ℝ) :
    entropy (spectralLift u p ⊗ₖ spectralLift v q) =
      (∑ j, q j) * (∑ i, Real.negMulLog (p i)) +
        (∑ i, p i) * (∑ j, Real.negMulLog (q j)) := by
  rw [tensor_spectralLift, entropy_spectralLift, Fintype.sum_prod_type]
  calc
    (∑ i, ∑ j, Real.negMulLog (p i * q j)) =
        ∑ i, ((∑ j, q j) * Real.negMulLog (p i) +
          p i * (∑ j, Real.negMulLog (q j))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp_rw [OperatorKO7.Meta.ReverseBridge.QMLaw_EntropyLaws.negMulLog_mul_total]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

/-- The trace-weighted tensor identity is proved for all Hermitian input matrices. -/
theorem entropy_tensor {a : Matrix ι ι ℂ} {b : Matrix κ κ ℂ}
    (ha : a.IsHermitian) (hb : b.IsHermitian) :
    entropy (a ⊗ₖ b) = b.trace.re * entropy a + a.trace.re * entropy b := by
  calc
    entropy (a ⊗ₖ b) =
        entropy (spectralLift ha.eigenvectorUnitary ha.eigenvalues ⊗ₖ
          spectralLift hb.eigenvectorUnitary hb.eigenvalues) := by
      rw [spectralLift_eigenvalues ha, spectralLift_eigenvalues hb]
    _ = (∑ j, hb.eigenvalues j) * (∑ i, Real.negMulLog (ha.eigenvalues i)) +
        (∑ i, ha.eigenvalues i) * (∑ j, Real.negMulLog (hb.eigenvalues j)) :=
      entropy_tensor_spectralLift _ _ _ _
    _ = _ := by
      rw [eigenvalues_sum_trace ha, eigenvalues_sum_trace hb,
        ← entropy_eq_eigenvalues ha, ← entropy_eq_eigenvalues hb]

/-- Product-state entropy additivity follows from unit trace, not an entropy-balance premise. -/
theorem entropy_tensor_trace_one {a : Matrix ι ι ℂ} {b : Matrix κ κ ℂ}
    (ha : a.IsHermitian) (hb : b.IsHermitian) (hta : a.trace = 1) (htb : b.trace = 1) :
    entropy (a ⊗ₖ b) = entropy a + entropy b := by
  rw [entropy_tensor ha hb, hta, htb]
  simp

/-- Squared overlap of two coordinate rays, taken from the actual matrix entry. -/
def basisWeight (t : Matrix ι ι ℂ) (i j : ι) : ℝ :=
  (t i j * star (t i j)).re

omit [Fintype ι] [DecidableEq ι] in
theorem basisWeight_nonneg (t : Matrix ι ι ℂ) (i j : ι) : 0 ≤ basisWeight t i j := by
  unfold basisWeight
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (t i j).re, sq_nonneg (t i j).im]

/-- Row normalization is a consequence of the unitary inverse equation. -/
theorem basisWeight_row_sum (t : Matrix.unitaryGroup ι ℂ) (i : ι) :
    (∑ j, basisWeight (t : Matrix ι ι ℂ) i j) = 1 := by
  have h := congrArg (fun a : Matrix ι ι ℂ => (a i i).re)
    (unitary.coe_mul_star_self t)
  simpa [basisWeight, Matrix.mul_apply] using h

/-- Column normalization uses the other unitary inverse equation. -/
theorem basisWeight_col_sum (t : Matrix.unitaryGroup ι ℂ) (j : ι) :
    (∑ i, basisWeight (t : Matrix ι ι ℂ) i j) = 1 := by
  have h := congrArg (fun a : Matrix ι ι ℂ => (a j j).re)
    (unitary.coe_star_mul_self t)
  simpa [basisWeight, Matrix.mul_apply, mul_comm] using h

/-- The mixed spectral trace is expanded from native multiplication, with no commutativity premise on matrices. -/
theorem diagonalSandwich_trace_re (t : Matrix ι ι ℂ) (p q : ι → ℝ) :
    (realDiagonal p * t * realDiagonal q * star t).trace.re =
      ∑ i, ∑ j, p i * q j * basisWeight t i j := by
  change Complex.reAddGroupHom
    (∑ i, ∑ j, (realDiagonal p * t * realDiagonal q) i j * star (t i j)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  change Complex.reAddGroupHom
    (∑ j, (realDiagonal p * t * realDiagonal q) i j * star (t i j)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  change ((realDiagonal p * t * realDiagonal q) i j * star (t i j)).re = _
  simp only [realDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  calc
    ((p i : ℂ) * t i j * (q j : ℂ) * star (t i j)).re =
        (((p i * q j : ℝ) : ℂ) * (t i j * star (t i j))).re := by
      congr 1
      rw [Complex.ofReal_mul]
      ring
    _ = _ := Complex.re_ofReal_mul _ _

/-- The cross trace retains the actual relative eigenbasis U-adjoint V. -/
theorem spectralLift_cross_trace_re (u v : Matrix.unitaryGroup ι ℂ) (p q : ι → ℝ) :
    (spectralLift u p * spectralLift v q).trace.re =
      ∑ i, ∑ j, p i * q j *
        basisWeight (star (u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)) i j := by
  calc
    (spectralLift u p * spectralLift v q).trace.re =
        ((u : Matrix ι ι ℂ) * (realDiagonal p *
          (star (u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)) * realDiagonal q *
          star (v : Matrix ι ι ℂ))).trace.re := by
      congr 2
      simp only [spectralLift, rotate, mul_assoc]
    _ = ((realDiagonal p * (star (u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)) *
        realDiagonal q * star (v : Matrix ι ι ℂ)) * (u : Matrix ι ι ℂ)).trace.re := by
      rw [Matrix.trace_mul_comm]
    _ = (realDiagonal p * (star (u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)) *
        realDiagonal q * star (star (u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ))).trace.re := by
      congr 2
      simp only [StarMul.star_mul, star_star, mul_assoc]
    _ = _ := diagonalSandwich_trace_re _ _ _

/-- Finite Gibbs terms yield the spectral inequality for the actual unitary overlap.
The zero-support premise is explicit and is discharged from matrix kernels below. -/
theorem unitary_weighted_gibbs (t : Matrix.unitaryGroup ι ℂ) (p q : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ j, 0 ≤ q j)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ j, q j = 1)
    (habs : ∀ i j, q j = 0 → p i * basisWeight (t : Matrix ι ι ℂ) i j = 0) :
    0 ≤ -(∑ i, Real.negMulLog (p i)) -
      ∑ i, ∑ j, p i * Real.log (q j) * basisWeight (t : Matrix ι ι ℂ) i j := by
  have hterm : ∀ i j,
      basisWeight (t : Matrix ι ι ℂ) i j *
          (Real.negMulLog (p i) + p i * Real.log (q j)) ≤
        basisWeight (t : Matrix ι ι ℂ) i j * (q j - p i) := by
    intro i j
    by_cases hw : basisWeight (t : Matrix ι ι ℂ) i j = 0
    · simp [hw]
    · have hz : q j = 0 → p i = 0 := fun hq =>
        (mul_eq_zero.mp (habs i j hq)).resolve_right hw
      exact mul_le_mul_of_nonneg_left
        (OperatorKO7.Meta.ReverseBridge.QMLaw_EntropyLaws.gibbs_term
          (p i) (q j) (hp0 i) (hq0 j) hz) (basisWeight_nonneg _ i j)
  have hpsum : (∑ i, ∑ j, basisWeight (t : Matrix ι ι ℂ) i j * p i) = 1 := by
    simp_rw [← Finset.sum_mul, basisWeight_row_sum, one_mul]
    exact hp1
  have hqsum : (∑ i, ∑ j, basisWeight (t : Matrix ι ι ℂ) i j * q j) = 1 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, basisWeight_col_sum, one_mul]
    exact hq1
  have hentropy :
      (∑ i, ∑ j, basisWeight (t : Matrix ι ι ℂ) i j * Real.negMulLog (p i)) =
        ∑ i, Real.negMulLog (p i) := by
    simp_rw [← Finset.sum_mul, basisWeight_row_sum, one_mul]
  have hcross :
      (∑ i, ∑ j, basisWeight (t : Matrix ι ι ℂ) i j * (p i * Real.log (q j))) =
        ∑ i, ∑ j, p i * Real.log (q j) * basisWeight (t : Matrix ι ι ℂ) i j := by
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    exact mul_comm _ _
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _hi => Finset.sum_le_sum (s := (Finset.univ : Finset ι))
      (fun j _hj => hterm i j))
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [hentropy, hcross, hqsum, hpsum] at hsum
  linarith

/-- Products of spectral functions of the same matrix use the same native unitary. -/
theorem spectralLift_mul (u : Matrix.unitaryGroup ι ℂ) (p q : ι → ℝ) :
    spectralLift u p * spectralLift u q = spectralLift u (fun i => p i * q i) := by
  calc
    spectralLift u p * spectralLift u q =
        (u : Matrix ι ι ℂ) * (realDiagonal p *
          (star (u : Matrix ι ι ℂ) * (u : Matrix ι ι ℂ)) * realDiagonal q) *
          star (u : Matrix ι ι ℂ) := by
      simp only [spectralLift, rotate, mul_assoc]
    _ = spectralLift u (fun i => p i * q i) := by
      rw [unitary.coe_star_mul_self, mul_one]
      simp only [spectralLift, rotate, realDiagonal, Matrix.diagonal_mul_diagonal,
        Complex.ofReal_mul]

/-- Support inclusion is expressed by the actual matrix kernels. -/
def SupportLE (a b : Matrix ι ι ℂ) : Prop :=
  ∀ x : ι → ℂ, b *ᵥ x = 0 → a *ᵥ x = 0

/-- Kernel inclusion forces the zero-reference terms in the relative eigenbasis to vanish. -/
theorem support_spectral_weights (u v : Matrix.unitaryGroup ι ℂ) (p q : ι → ℝ)
    (hker : SupportLE (spectralLift u p) (spectralLift v q)) (i j : ι) (hq : q j = 0) :
    p i * basisWeight (star (u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)) i j = 0 := by
  have hv : spectralLift v q * (v : Matrix ι ι ℂ) =
      (v : Matrix ι ι ℂ) * realDiagonal q := by
    change ((v : Matrix ι ι ℂ) * realDiagonal q * star (v : Matrix ι ι ℂ)) *
      (v : Matrix ι ι ℂ) = _
    rw [mul_assoc, unitary.coe_star_mul_self, mul_one]
  have hbzero : spectralLift v q *ᵥ ((v : Matrix ι ι ℂ) *ᵥ Pi.single j (1 : ℂ)) = 0 := by
    rw [Matrix.mulVec_mulVec, hv, ← Matrix.mulVec_mulVec]
    have hd : realDiagonal q *ᵥ Pi.single j (1 : ℂ) = 0 := by
      simp [realDiagonal, hq]
    rw [hd, Matrix.mulVec_zero]
  have hazero := hker _ hbzero
  have hleft := congrArg (fun x : ι → ℂ => star (u : Matrix ι ι ℂ) *ᵥ x) hazero
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at hleft
  have hred : star (u : Matrix ι ι ℂ) * (spectralLift u p * (v : Matrix ι ι ℂ)) =
      realDiagonal p * (star (u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)) := by
    calc
      _ = (star (u : Matrix ι ι ℂ) * (u : Matrix ι ι ℂ)) *
          realDiagonal p * (star (u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)) := by
        simp only [spectralLift, rotate, mul_assoc]
      _ = _ := by rw [unitary.coe_star_mul_self, one_mul]
  rw [hred] at hleft
  have he := congrArg (fun x : ι → ℂ => x i) hleft
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, realDiagonal,
    Matrix.diagonal_mul, Pi.zero_apply] at he
  rcases mul_eq_zero.mp he with hp | ht
  · have hpzero : p i = 0 := Complex.ofReal_eq_zero.mp hp
    rw [hpzero, zero_mul]
  · simp [basisWeight, ht]

/-- Spectral entropy equals the native logarithmic trace; zero eigenvalues are included. -/
theorem entropy_eq_neg_trace_mul_log {a : Matrix ι ι ℂ} (ha : a.IsHermitian) :
    entropy a = -(a * matrixLog a).trace.re := by
  calc
    entropy a = ∑ i, Real.negMulLog (ha.eigenvalues i) := entropy_eq_eigenvalues ha
    _ = -(∑ i, ha.eigenvalues i * Real.log (ha.eigenvalues i)) := by
      simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
    _ = -(spectralLift ha.eigenvectorUnitary ha.eigenvalues *
        matrixLog (spectralLift ha.eigenvectorUnitary ha.eigenvalues)).trace.re := by
      rw [matrixLog_spectralLift, spectralLift_mul, spectralLift_trace_re]
    _ = -(a * matrixLog a).trace.re := by rw [spectralLift_eigenvalues ha]

/-- Finite quantum relative entropy as a trace of native matrix logarithms.
Its finite physical interpretation requires SupportLE for singular references. -/
def relativeEntropy (a b : Matrix ι ι ℂ) : ℝ :=
  (a * (matrixLog a - matrixLog b)).trace.re

theorem relativeEntropy_eq {a : Matrix ι ι ℂ} (ha : a.IsHermitian) (b : Matrix ι ι ℂ) :
    relativeEntropy a b = -entropy a - (a * matrixLog b).trace.re := by
  rw [relativeEntropy, mul_sub, Matrix.trace_sub, Complex.sub_re,
    entropy_eq_neg_trace_mul_log ha, neg_neg]

/-- Noncommuting relative entropy has the derived unitary-overlap formula. -/
theorem relativeEntropy_spectralLift (u v : Matrix.unitaryGroup ι ℂ) (p q : ι → ℝ) :
    relativeEntropy (spectralLift u p) (spectralLift v q) =
      -(∑ i, Real.negMulLog (p i)) - ∑ i, ∑ j, p i * Real.log (q j) *
        basisWeight (star (u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)) i j := by
  rw [relativeEntropy_eq (spectralLift_hermitian u p), entropy_spectralLift,
    matrixLog_spectralLift, spectralLift_cross_trace_re]

/-- Quantum relative entropy is nonnegative for arbitrary finite density matrices
with actual support inclusion. No common eigenbasis or positive-definite reference is required. -/
theorem relativeEntropy_nonneg {a b : Matrix ι ι ℂ}
    (ha : a.PosSemidef) (hb : b.PosSemidef) (hta : a.trace = 1) (htb : b.trace = 1)
    (hker : SupportLE a b) : 0 ≤ relativeEntropy a b := by
  let u := ha.1.eigenvectorUnitary
  let v := hb.1.eigenvectorUnitary
  let p := ha.1.eigenvalues
  let q := hb.1.eigenvalues
  have hpa : spectralLift u p = a := spectralLift_eigenvalues ha.1
  have hqb : spectralLift v q = b := spectralLift_eigenvalues hb.1
  have hp1 : (∑ i, p i) = 1 :=
    (eigenvalues_sum_trace ha.1).trans (congrArg Complex.re hta)
  have hq1 : (∑ j, q j) = 1 :=
    (eigenvalues_sum_trace hb.1).trans (congrArg Complex.re htb)
  have hker' : SupportLE (spectralLift u p) (spectralLift v q) := by
    simpa only [hpa, hqb] using hker
  have hineq := unitary_weighted_gibbs (star u * v) p q
    (fun i => ha.eigenvalues_nonneg i) (fun j => hb.eigenvalues_nonneg j) hp1 hq1
    (fun i j hqzero => support_spectral_weights u v p q hker' i j hqzero)
  rw [← hpa, ← hqb, relativeEntropy_spectralLift]
  exact hineq

/-- Partition sum: beta has inverse-energy units and energy has joule units. -/
def partition (β : ℝ) (energy : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (-β * energy i)

omit [DecidableEq ι] in
/-- A nonempty finite reservoir has a strictly positive partition sum. -/
theorem partition_pos [Nonempty ι] (β : ℝ) (energy : ι → ℝ) :
    0 < partition β energy := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  unfold partition
  exact lt_of_lt_of_le (Real.exp_pos (-β * energy i))
    (Finset.single_le_sum (fun j _hj => (Real.exp_pos (-β * energy j)).le)
      (Finset.mem_univ i))

/-- Reservoir probabilities are computed from the Hamiltonian spectrum. -/
def gibbsWeight (β : ℝ) (energy : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (-β * energy i) / partition β energy

omit [DecidableEq ι] in
theorem gibbsWeight_pos [Nonempty ι] (β : ℝ) (energy : ι → ℝ) (i : ι) :
    0 < gibbsWeight β energy i :=
  div_pos (Real.exp_pos _) (partition_pos β energy)

omit [DecidableEq ι] in
/-- Normalization follows from the same partition sum used in each weight. -/
theorem gibbsWeight_sum [Nonempty ι] (β : ℝ) (energy : ι → ℝ) :
    (∑ i, gibbsWeight β energy i) = 1 := by
  unfold gibbsWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos β energy))

omit [DecidableEq ι] in
/-- The logarithmic Gibbs formula follows from positive weights and the exponential. -/
theorem log_gibbsWeight [Nonempty ι] (β : ℝ) (energy : ι → ℝ) (i : ι) :
    Real.log (gibbsWeight β energy i) = -β * energy i - Real.log (partition β energy) := by
  rw [gibbsWeight, Real.log_div (ne_of_gt (Real.exp_pos _))
    (ne_of_gt (partition_pos β energy)), Real.log_exp]

/-- The Gibbs matrix is constructed from the native spectral theorem of the Hamiltonian. -/
def gibbsState {h : Matrix ι ι ℂ} (hh : h.IsHermitian) (β : ℝ) : Matrix ι ι ℂ :=
  spectralLift hh.eigenvectorUnitary (gibbsWeight β hh.eigenvalues)

theorem gibbsState_hermitian {h : Matrix ι ι ℂ} (hh : h.IsHermitian) (β : ℝ) :
    (gibbsState hh β).IsHermitian := spectralLift_hermitian _ _

/-- The constructed Gibbs state has unit trace. -/
theorem gibbsState_trace [Nonempty ι] {h : Matrix ι ι ℂ} (hh : h.IsHermitian) (β : ℝ) :
    (gibbsState hh β).trace = 1 := by
  rw [gibbsState, spectralLift, rotate_trace, realDiagonal, Matrix.trace_diagonal]
  have hs := congrArg Complex.ofReal (gibbsWeight_sum β hh.eigenvalues)
  simpa using hs

/-- Strict positivity is derived from the positive Gibbs spectrum and the unitary basis. -/
theorem gibbsState_posDef [Nonempty ι] {h : Matrix ι ι ℂ} (hh : h.IsHermitian) (β : ℝ) :
    (gibbsState hh β).PosDef := by
  change ((hh.eigenvectorUnitary : Matrix ι ι ℂ) *
    realDiagonal (gibbsWeight β hh.eigenvalues) *
      (hh.eigenvectorUnitary : Matrix ι ι ℂ).conjTranspose).PosDef
  apply Matrix.PosDef.mul_mul_conjTranspose_same
  · apply Matrix.PosDef.diagonal
    intro i
    simpa using gibbsWeight_pos β hh.eigenvalues i
  · apply Matrix.vecMul_injective_of_isUnit
    exact (Group.isUnit hh.eigenvectorUnitary).map (Matrix.unitaryGroup ι ℂ).subtype

/-- The matrix Gibbs logarithm is derived in the same Hamiltonian eigenbasis. -/
theorem gibbsState_log [Nonempty ι] {h : Matrix ι ι ℂ} (hh : h.IsHermitian) (β : ℝ) :
    matrixLog (gibbsState hh β) =
      ((-β : ℝ) : ℂ) • h - (Real.log (partition β hh.eigenvalues) : ℂ) • 1 := by
  rw [gibbsState, matrixLog_spectralLift]
  simp_rw [log_gibbsWeight]
  have hd : realDiagonal (fun i => -β * hh.eigenvalues i - Real.log (partition β hh.eigenvalues)) =
      ((-β : ℝ) : ℂ) • realDiagonal hh.eigenvalues -
        (Real.log (partition β hh.eigenvalues) : ℂ) • 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [realDiagonal, Complex.ofReal_sub, Complex.ofReal_mul]
    · simp [realDiagonal, hij]
  calc
    spectralLift hh.eigenvectorUnitary
        (fun i => -β * hh.eigenvalues i - Real.log (partition β hh.eigenvalues)) =
        ((-β : ℝ) : ℂ) • spectralLift hh.eigenvectorUnitary hh.eigenvalues -
          (Real.log (partition β hh.eigenvalues) : ℂ) • 1 := by
      simp only [spectralLift, rotate, hd, mul_sub, sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, mul_one, unitary_mul_adjoint]
    _ = _ := by rw [spectralLift_eigenvalues hh]

/-- Every matrix has support inside the constructed finite-temperature Gibbs state. -/
theorem support_gibbsState [Nonempty ι] {h : Matrix ι ι ℂ} (hh : h.IsHermitian)
    (β : ℝ) (a : Matrix ι ι ℂ) : SupportLE a (gibbsState hh β) := by
  intro x hx
  have hinj := Matrix.mulVec_injective_of_isUnit (gibbsState_posDef hh β).isUnit
  have hxzero : x = 0 := hinj (hx.trans (Matrix.mulVec_zero _).symm)
  rw [hxzero, Matrix.mulVec_zero]

/-- Expected energy in joules for a Hamiltonian expressed in joules. -/
def meanEnergy (h a : Matrix ι ι ℂ) : ℝ := (h * a).trace.re

/-- The Gibbs cross-entropy formula is derived from the matrix logarithm and unit trace. -/
theorem relativeEntropy_gibbs_eq [Nonempty ι] {h a : Matrix ι ι ℂ}
    (hh : h.IsHermitian) (β : ℝ) (ha : a.IsHermitian) (hta : a.trace = 1) :
    relativeEntropy a (gibbsState hh β) =
      -entropy a + β * meanEnergy h a + Real.log (partition β hh.eigenvalues) := by
  rw [relativeEntropy_eq ha, gibbsState_log]
  simp only [mul_sub, Matrix.mul_smul, mul_one, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul, hta, Complex.ofReal_re, meanEnergy]
  rw [Matrix.trace_mul_comm a h]
  ring

/-- Gibbs entropy is computed from its Hamiltonian and its partition sum. -/
theorem gibbsState_entropy [Nonempty ι] {h : Matrix ι ι ℂ} (hh : h.IsHermitian) (β : ℝ) :
    entropy (gibbsState hh β) =
      β * meanEnergy h (gibbsState hh β) + Real.log (partition β hh.eigenvalues) := by
  have he := relativeEntropy_gibbs_eq hh β (gibbsState_hermitian hh β) (gibbsState_trace hh β)
  have hz : relativeEntropy (gibbsState hh β) (gibbsState hh β) = 0 := by
    simp [relativeEntropy]
  rw [hz] at he
  linarith

omit [DecidableEq ι] in
theorem meanEnergy_sub (h a b : Matrix ι ι ℂ) :
    meanEnergy h (a - b) = meanEnergy h a - meanEnergy h b := by
  simp only [meanEnergy, mul_sub, Matrix.trace_sub, Complex.sub_re]

/-- Exact reservoir entropy/heat balance with a nonnegative relative-entropy remainder.
Heat is the change of the same reservoir Hamiltonian's expected energy, in joules. -/
theorem gibbs_bath_balance [Nonempty ι] {h a : Matrix ι ι ℂ}
    (hh : h.IsHermitian) (β : ℝ) (ha : a.PosSemidef) (hta : a.trace = 1) :
    (β * meanEnergy h (a - gibbsState hh β) =
      entropy a - entropy (gibbsState hh β) + relativeEntropy a (gibbsState hh β)) ∧
    0 ≤ relativeEntropy a (gibbsState hh β) := by
  constructor
  · have he := relativeEntropy_gibbs_eq hh β ha.1 hta
    have hg := gibbsState_entropy hh β
    rw [meanEnergy_sub, mul_sub]
    linarith
  · exact relativeEntropy_nonneg ha (gibbsState_posDef hh β).posSemidef hta
      (gibbsState_trace hh β) (support_gibbsState hh β a)

/-! ## Joint states and their actual partial traces -/

/-- Sum the reservoir coordinate of the given joint matrix. -/
def marginalLeft (a : Matrix (ι × κ) (ι × κ) ℂ) : Matrix ι ι ℂ :=
  fun i j => ∑ r, a (i, r) (j, r)

/-- Sum the system coordinate of the same joint matrix. -/
def marginalRight (a : Matrix (ι × κ) (ι × κ) ℂ) : Matrix κ κ ℂ :=
  fun r s => ∑ i, a (i, r) (i, s)

omit [DecidableEq ι] in
/-- A finite sum of positive matrices is positive. -/
theorem psd_sum {J : Type} (s : Finset J) (a : J → Matrix ι ι ℂ)
    (ha : ∀ j ∈ s, (a j).PosSemidef) : (∑ j ∈ s, a j).PosSemidef := by
  induction s using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef)
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (ha j (Finset.mem_insert_self j s)).add
      (ih (fun k hk => ha k (Finset.mem_insert_of_mem hk)))

omit [DecidableEq ι] [DecidableEq κ] in
/-- Each marginal is a sum of positive principal submatrices. -/
theorem marginalLeft_posSemidef {a : Matrix (ι × κ) (ι × κ) ℂ}
    (ha : a.PosSemidef) : (marginalLeft a).PosSemidef := by
  have he : marginalLeft a = ∑ r : κ, a.submatrix (fun i => (i, r)) (fun i => (i, r)) := by
    ext i j
    simp only [marginalLeft, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [he]
  exact psd_sum Finset.univ _ (fun r _ => ha.submatrix (fun i => (i, r)))

omit [DecidableEq ι] [DecidableEq κ] in
theorem marginalRight_posSemidef {a : Matrix (ι × κ) (ι × κ) ℂ}
    (ha : a.PosSemidef) : (marginalRight a).PosSemidef := by
  have he : marginalRight a = ∑ i : ι, a.submatrix (fun r => (i, r)) (fun r => (i, r)) := by
    ext r s
    simp only [marginalRight, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [he]
  exact psd_sum Finset.univ _ (fun i _ => ha.submatrix (fun r => (i, r)))

omit [DecidableEq ι] [DecidableEq κ] in
/-- The two partial traces retain the trace of the same joint matrix. -/
theorem marginalLeft_trace (a : Matrix (ι × κ) (ι × κ) ℂ) :
    (marginalLeft a).trace = a.trace := by
  simp only [Matrix.trace, marginalLeft, Matrix.diag, Fintype.sum_prod_type]

omit [DecidableEq ι] [DecidableEq κ] in
theorem marginalRight_trace (a : Matrix (ι × κ) (ι × κ) ℂ) :
    (marginalRight a).trace = a.trace := by
  simp only [Matrix.trace, marginalRight, Matrix.diag, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [DecidableEq ι] [DecidableEq κ] in
/-- Tensor positivity follows from the square-root factorization of both matrices. -/
theorem tensor_posSemidef {a : Matrix ι ι ℂ} {b : Matrix κ κ ℂ}
    (ha : a.PosSemidef) (hb : b.PosSemidef) : (a ⊗ₖ b).PosSemidef := by
  obtain ⟨r, hr⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp ha
  obtain ⟨s, hs⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hb
  rw [hr, hs, Matrix.mul_kronecker_mul]
  have he : r.conjTranspose ⊗ₖ s.conjTranspose = (r ⊗ₖ s).conjTranspose :=
    (star_tensor r s).symm
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- A positive matrix remains positive under the actual joint unitary. -/
theorem rotate_posSemidef (u : Matrix.unitaryGroup ι ℂ) {a : Matrix ι ι ℂ}
    (ha : a.PosSemidef) : (rotate u a).PosSemidef :=
  ha.mul_mul_conjTranspose_same (u : Matrix ι ι ℂ)

omit [DecidableEq ι] in
/-- Testing a system matrix in the joint state equals testing its system marginal. -/
theorem trace_tensor_left (a : Matrix (ι × κ) (ι × κ) ℂ) (b : Matrix ι ι ℂ) :
    (a * (b ⊗ₖ (1 : Matrix κ κ ℂ))).trace = (marginalLeft a * b).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [marginalLeft, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

omit [DecidableEq κ] in
/-- The reservoir identity uses the other marginal of the same joint state. -/
theorem trace_tensor_right (a : Matrix (ι × κ) (ι × κ) ℂ) (b : Matrix κ κ ℂ) :
    (a * ((1 : Matrix ι ι ℂ) ⊗ₖ b)).trace = (marginalRight a * b).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite,
    mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [marginalRight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  exact Finset.sum_comm

omit [DecidableEq ι] in
/-- A zero quadratic form is a kernel vector for a positive joint state. -/
theorem psd_kernel_of_quadratic_zero {a : Matrix ι ι ℂ} (ha : a.PosSemidef)
    (v : ι → ℂ) (hv : star v ⬝ᵥ (a *ᵥ v) = 0) : a *ᵥ v = 0 :=
  (ha.dotProduct_mulVec_zero_iff v).mp hv

/-- A zero diagonal entry of a positive matrix forces its entire column to vanish. -/
theorem psd_column_zero {a : Matrix ι ι ℂ} (ha : a.PosSemidef) (j : ι)
    (hj : a j j = 0) : ∀ i, a i j = 0 := by
  have hq : star (Pi.single j (1 : ℂ)) ⬝ᵥ (a *ᵥ Pi.single j 1) = 0 := by
    simpa only [Matrix.mulVec_single_one, ← Pi.single_star, star_one,
      single_dotProduct, one_mul, Matrix.col_apply] using hj
  have hk := psd_kernel_of_quadratic_zero ha (Pi.single j 1) hq
  intro i
  simpa using congrFun hk i

/-! ## Reading in an orthonormal basis and entropy -/

/-- The projector onto one vector of the supplied orthonormal basis. -/
def basisProjector (u : Matrix.unitaryGroup ι ℂ) (j : ι) : Matrix ι ι ℂ :=
  spectralLift u (fun i => if i = j then 1 else 0)

/-- The probability of this basis outcome in the given input matrix. -/
def diagonalLaw (a : Matrix ι ι ℂ) (u : Matrix.unitaryGroup ι ℂ) (j : ι) : ℝ :=
  (a * basisProjector u j).trace.re

/-- The probabilities use the actual overlaps of the two orthonormal bases. -/
theorem diagonalLaw_spectralLift (v u : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) (j : ι) :
    diagonalLaw (spectralLift v p) u j =
      ∑ i, p i * basisWeight (star (v : Matrix ι ι ℂ) * (u : Matrix ι ι ℂ)) i j := by
  simp [diagonalLaw, basisProjector, spectralLift_cross_trace_re]

/-- In its eigenbasis the probabilities are the eigenvalues of the given matrix. -/
theorem diagonalLaw_own_basis (u : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) (j : ι) :
    diagonalLaw (spectralLift u p) u j = p j := by
  rw [diagonalLaw, basisProjector, spectralLift_mul, spectralLift_trace_re]
  simp

/-- Every basis report of a positive matrix is nonnegative. -/
theorem diagonalLaw_nonnegative {a : Matrix ι ι ℂ} (ha : a.PosSemidef)
    (u : Matrix.unitaryGroup ι ℂ) (j : ι) : 0 ≤ diagonalLaw a u j := by
  rw [← spectralLift_eigenvalues ha.1, diagonalLaw_spectralLift]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (ha.eigenvalues_nonneg i)
    (basisWeight_nonneg _ i j))

/-- A basis measurement has the same total mass as the input state. -/
theorem diagonalLaw_total {a : Matrix ι ι ℂ} (ha : a.IsHermitian)
    (u : Matrix.unitaryGroup ι ℂ) : (∑ j, diagonalLaw a u j) = a.trace.re := by
  rw [← spectralLift_eigenvalues ha]
  simp only [diagonalLaw_spectralLift]
  rw [Finset.sum_comm]
  calc
    (∑ i, ∑ j, ha.eigenvalues i *
        basisWeight (star (ha.eigenvectorUnitary : Matrix ι ι ℂ) * (u : Matrix ι ι ℂ)) i j) =
        ∑ i, ha.eigenvalues i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum]
      have hs := basisWeight_row_sum (star ha.eigenvectorUnitary * u) i
      change (∑ j, basisWeight
        (star (ha.eigenvectorUnitary : Matrix ι ι ℂ) * (u : Matrix ι ι ℂ)) i j) = 1 at hs
      rw [hs, mul_one]
    _ = _ := (spectralLift_trace_re _ _).symm

/-- Reading in a basis cannot lower the spectral entropy of a density matrix. -/
theorem entropy_le_basis_entropy {a : Matrix ι ι ℂ} (ha : a.PosSemidef)
    (hta : a.trace = 1) (u : Matrix.unitaryGroup ι ℂ) :
    entropy a ≤ ∑ j, Real.negMulLog (diagonalLaw a u j) := by
  let v := ha.1.eigenvectorUnitary
  let p := ha.1.eigenvalues
  let d := diagonalLaw a u
  let t : Matrix.unitaryGroup ι ℂ := star v * u
  have hd (j : ι) : d j = ∑ i, p i * basisWeight (t : Matrix ι ι ℂ) i j := by
    change diagonalLaw a u j = _
    rw [← spectralLift_eigenvalues ha.1, diagonalLaw_spectralLift]
    rfl
  have hp : (∑ i, p i) = 1 :=
    (eigenvalues_sum_trace ha.1).trans (congrArg Complex.re hta)
  have hd1 : (∑ j, d j) = 1 :=
    (diagonalLaw_total ha.1 u).trans (congrArg Complex.re hta)
  have hz (i j : ι) (hj : d j = 0) : p i * basisWeight (t : Matrix ι ι ℂ) i j = 0 := by
    have hle := Finset.single_le_sum (s := Finset.univ)
      (fun r _ => mul_nonneg (ha.eigenvalues_nonneg r)
        (basisWeight_nonneg (t : Matrix ι ι ℂ) r j))
      (Finset.mem_univ i)
    rw [← hd j, hj] at hle
    exact le_antisymm hle
      (mul_nonneg (ha.eigenvalues_nonneg i) (basisWeight_nonneg _ i j))
  have hg := unitary_weighted_gibbs t p d (fun i => ha.eigenvalues_nonneg i)
    (diagonalLaw_nonnegative ha u) hp hd1 hz
  have hx : (∑ i, ∑ j, p i * Real.log (d j) * basisWeight (t : Matrix ι ι ℂ) i j) =
      ∑ j, d j * Real.log (d j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [hd j, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hx] at hg
  have hs : (∑ j, d j * Real.log (d j)) = -(∑ j, Real.negMulLog (d j)) := by
    simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
  rw [hs] at hg
  rw [entropy_eq_eigenvalues ha.1]
  linarith

/-- Basis projectors sum to the identity on the original finite carrier. -/
theorem basisProjector_sum (u : Matrix.unitaryGroup ι ℂ) :
    (∑ j, basisProjector u j) = 1 := by
  have hd : (∑ j : ι, realDiagonal (fun i => if i = j then (1 : ℝ) else 0)) = 1 := by
    ext i k
    by_cases hik : i = k
    · subst k
      simp [Matrix.sum_apply, realDiagonal, apply_ite]
    · simp [Matrix.sum_apply, realDiagonal, hik]
  simp only [basisProjector, spectralLift, rotate, ← Finset.sum_mul, ← Matrix.mul_sum]
  rw [hd, mul_one, unitary_mul_adjoint]

/-- Tensor basis projectors use the original tensor unitary. -/
theorem basisProjector_tensor (u : Matrix.unitaryGroup ι ℂ) (v : Matrix.unitaryGroup κ ℂ)
    (i : ι) (j : κ) :
    basisProjector (tensorUnitary u v) (i, j) = basisProjector u i ⊗ₖ basisProjector v j := by
  simp only [basisProjector, tensor_spectralLift]
  apply congrArg (spectralLift (tensorUnitary u v))
  funext x
  rcases x with ⟨r, s⟩
  by_cases hr : r = i <;> by_cases hs : s = j <;> simp [hr, hs]

omit [DecidableEq ι] in
/-- A finite sum of tested matrices is tested by the sum of their expectations. -/
theorem trace_expectation_sum {J : Type} [Fintype J] (a : Matrix ι ι ℂ)
    (b : J → Matrix ι ι ℂ) :
    (∑ j, (a * b j).trace.re) = (a * ∑ j, b j).trace.re := by
  rw [Matrix.mul_sum, Matrix.trace_sum]
  exact (map_sum Complex.reAddGroupHom _ _).symm

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Tensor multiplication distributes over the recorded outcome sum. -/
theorem tensor_sum_right {J : Type} [Fintype J] (a : Matrix ι ι ℂ)
    (b : J → Matrix κ κ ℂ) :
    a ⊗ₖ (∑ j, b j) = ∑ j, a ⊗ₖ b j := by
  ext x y
  simp [Matrix.sum_apply, Finset.mul_sum]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem tensor_sum_left {J : Type} [Fintype J] (a : J → Matrix ι ι ℂ)
    (b : Matrix κ κ ℂ) :
    (∑ j, a j) ⊗ₖ b = ∑ j, a j ⊗ₖ b := by
  ext x y
  simp [Matrix.sum_apply, Finset.sum_mul]

/-- The first marginal of the product-basis law is the system basis law. -/
theorem diagonalLaw_marginalLeft (a : Matrix (ι × κ) (ι × κ) ℂ)
    (u : Matrix.unitaryGroup ι ℂ) (v : Matrix.unitaryGroup κ ℂ) (i : ι) :
    (∑ j, diagonalLaw a (tensorUnitary u v) (i, j)) = diagonalLaw (marginalLeft a) u i := by
  simp only [diagonalLaw, basisProjector_tensor]
  rw [trace_expectation_sum, ← tensor_sum_right, basisProjector_sum, trace_tensor_left]

/-- The second marginal is the reservoir basis law of the same input state. -/
theorem diagonalLaw_marginalRight (a : Matrix (ι × κ) (ι × κ) ℂ)
    (u : Matrix.unitaryGroup ι ℂ) (v : Matrix.unitaryGroup κ ℂ) (j : κ) :
    (∑ i, diagonalLaw a (tensorUnitary u v) (i, j)) = diagonalLaw (marginalRight a) v j := by
  simp only [diagonalLaw, basisProjector_tensor]
  rw [trace_expectation_sum, ← tensor_sum_left, basisProjector_sum, trace_tensor_right]

/-- Quantum subadditivity follows from basis entropy and the actual two marginal spectra. -/
theorem entropy_subadditive {a : Matrix (ι × κ) (ι × κ) ℂ}
    (ha : a.PosSemidef) (hta : a.trace = 1) :
    entropy a ≤ entropy (marginalLeft a) + entropy (marginalRight a) := by
  have hl := marginalLeft_posSemidef ha
  have hr := marginalRight_posSemidef ha
  let u := hl.1.eigenvectorUnitary
  let v := hr.1.eigenvectorUnitary
  let d := diagonalLaw a (tensorUnitary u v)
  have hdl (i : ι) : (∑ j, d (i, j)) = hl.1.eigenvalues i := by
    rw [diagonalLaw_marginalLeft]
    calc
      diagonalLaw (marginalLeft a) u i = diagonalLaw (spectralLift u hl.1.eigenvalues) u i :=
        congrArg (fun b => diagonalLaw b u i) (spectralLift_eigenvalues hl.1).symm
      _ = _ := diagonalLaw_own_basis u hl.1.eigenvalues i
  have hdr (j : κ) : (∑ i, d (i, j)) = hr.1.eigenvalues j := by
    rw [diagonalLaw_marginalRight]
    calc
      diagonalLaw (marginalRight a) v j = diagonalLaw (spectralLift v hr.1.eigenvalues) v j :=
        congrArg (fun b => diagonalLaw b v j) (spectralLift_eigenvalues hr.1).symm
      _ = _ := diagonalLaw_own_basis v hr.1.eigenvalues j
  have hn : ∀ x, 0 ≤ d x := diagonalLaw_nonnegative ha _
  have ht : (∑ x, d x) = 1 := (diagonalLaw_total ha.1 _).trans (congrArg Complex.re hta)
  have hc := OperatorKO7.Meta.ReverseBridge.QMLaw_EntropyLaws.entropy_subadditive d hn ht
  change (∑ x, Real.negMulLog (d x)) ≤
    (∑ i, Real.negMulLog (∑ j, d (i, j))) + ∑ j, Real.negMulLog (∑ i, d (i, j)) at hc
  simp only [hdl, hdr] at hc
  rw [← entropy_eq_eigenvalues hl.1, ← entropy_eq_eigenvalues hr.1] at hc
  exact (entropy_le_basis_entropy ha hta _).trans hc

/-- Correlation is evaluated from the two actual partial traces. -/
noncomputable def mutualInfo (a : Matrix (ι × κ) (ι × κ) ℂ) : ℝ :=
  entropy (marginalLeft a) + entropy (marginalRight a) - entropy a

/-- Correlation is nonnegative for arbitrary finite joint density matrices. -/
theorem mutualInfo_nonnegative {a : Matrix (ι × κ) (ι × κ) ℂ}
    (ha : a.PosSemidef) (hta : a.trace = 1) : 0 ≤ mutualInfo a :=
  sub_nonneg.mpr (entropy_subadditive ha hta)

/-- The physical joint process uses the declared unitary and the Gibbs state of its Hamiltonian. -/
noncomputable def thermalJoint [Nonempty κ] (u : Matrix.unitaryGroup (ι × κ) ℂ)
    (rho : Matrix ι ι ℂ) {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) :
    Matrix (ι × κ) (ι × κ) ℂ := rotate u (rho ⊗ₖ gibbsState hh β)

/-- The joint physical process produces a positive trace-one matrix. -/
theorem thermalJoint_density [Nonempty κ] (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef) (htr : rho.trace = 1)
    {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) :
    (thermalJoint u rho hh β).PosSemidef ∧ (thermalJoint u rho hh β).trace = 1 := by
  constructor
  · exact rotate_posSemidef u (tensor_posSemidef hrho (gibbsState_posDef hh β).posSemidef)
  · rw [thermalJoint, rotate_trace, Matrix.trace_kronecker, htr, gibbsState_trace, one_mul]

/-- The joint entropy is fixed by the input product law and its unitary evolution. -/
theorem thermalJoint_entropy [Nonempty κ] (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef) (htr : rho.trace = 1)
    {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) :
    entropy (thermalJoint u rho hh β) = entropy rho + entropy (gibbsState hh β) := by
  rw [thermalJoint, entropy_rotate u (tensor_posSemidef hrho (gibbsState_posDef hh β).posSemidef).1]
  exact entropy_tensor_trace_one hrho.1 (gibbsState_posDef hh β).posSemidef.1 htr (gibbsState_trace hh β)

/-- Heat is the energy increase of the declared reservoir, in joules. -/
noncomputable def reservoirHeat [Nonempty κ] (u : Matrix.unitaryGroup (ι × κ) ℂ)
    (rho : Matrix ι ι ℂ) {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) : ℝ :=
  meanEnergy h (marginalRight (thermalJoint u rho hh β) - gibbsState hh β)

/-- The finite physical balance is derived from one unitary, product input and Gibbs reservoir.
Entropy is in nats, beta is in inverse joules, and heat is the reservoir energy change. -/
theorem thermal_information_balance [Nonempty κ] (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef) (htr : rho.trace = 1)
    {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) :
    let tau := thermalJoint u rho hh β
    β * reservoirHeat u rho hh β =
      entropy rho - entropy (marginalLeft tau) + mutualInfo tau +
        relativeEntropy (marginalRight tau) (gibbsState hh β) ∧
    0 ≤ mutualInfo tau ∧
    0 ≤ relativeEntropy (marginalRight tau) (gibbsState hh β) := by
  dsimp only
  obtain ⟨htp, htt⟩ := thermalJoint_density u hrho htr hh β
  have hrt : (marginalRight (thermalJoint u rho hh β)).trace = 1 :=
    (marginalRight_trace _).trans htt
  obtain ⟨hb, hd⟩ := gibbs_bath_balance hh β (marginalRight_posSemidef htp) hrt
  have he := thermalJoint_entropy u hrho htr hh β
  refine ⟨?_, mutualInfo_nonnegative htp htt, hd⟩
  unfold reservoirHeat mutualInfo
  linarith

/-- The lower bound uses the derived nonnegative correlation and Gibbs remainders. -/
theorem landauer_from_unitary [Nonempty κ] (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef) (htr : rho.trace = 1)
    {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) (hβ : 0 < β) :
    (entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) / β ≤
      reservoirHeat u rho hh β := by
  obtain ⟨hb, hi, hd⟩ := thermal_information_balance u hrho htr hh β
  apply (div_le_iff₀ hβ).mpr
  linarith

/-! ## A retained binary outcome from the same thermal operation -/

/-- Gibbs normalization and the matrix state agree in every diagonalizing basis. -/
theorem gibbsState_spectralLift (u : Matrix.unitaryGroup ι ℂ) (energy : ι → ℝ) (β : ℝ) :
    gibbsState (spectralLift_hermitian u energy) β = spectralLift u (gibbsWeight β energy) := by
  let hh := spectralLift_hermitian u energy
  have hs := spectralFunction_spectralLift u energy (fun t => Real.exp (-β * t))
  have hp : partition β hh.eigenvalues = partition β energy := by
    have ht := congrArg (fun a : Matrix ι ι ℂ => a.trace.re) hs
    simpa only [spectralFunction, spectralLift_trace_re, partition] using ht
  unfold gibbsState gibbsWeight
  simp only [hp]
  exact spectralLift_function_congr hh.eigenvectorUnitary u hh.eigenvalues energy
    (spectralLift_eigenvalues hh) (fun t => Real.exp (-β * t) / partition β energy)

/-- Equal Hamiltonians give the same Gibbs state independently of their Hermitian proofs. -/
theorem gibbsState_congr {a b : Matrix ι ι ℂ} (ha : a.IsHermitian) (hb : b.IsHermitian)
    (hab : a = b) (β : ℝ) : gibbsState ha β = gibbsState hb β := by
  subst b
  rfl

/-- A zero Hamiltonian has the uniform Gibbs law at every inverse temperature. -/
theorem gibbsState_zero (β : ℝ) :
    gibbsState (Matrix.isHermitian_zero : (0 : Matrix Bool Bool ℂ).IsHermitian) β =
      realDiagonal (fun _ : Bool => (1 : ℝ) / 2) := by
  have hz : spectralLift (1 : Matrix.unitaryGroup Bool ℂ) (fun _ : Bool => (0 : ℝ)) = 0 := by
    simp [spectralLift, rotate, realDiagonal]
  have hg := gibbsState_spectralLift (1 : Matrix.unitaryGroup Bool ℂ)
    (fun _ : Bool => (0 : ℝ)) β
  have hw : gibbsWeight β (fun _ : Bool => (0 : ℝ)) = (fun _ : Bool => (1 : ℝ) / 2) := by
    funext i
    norm_num [gibbsWeight, partition]
  rw [hw] at hg
  calc
    gibbsState (Matrix.isHermitian_zero : (0 : Matrix Bool Bool ℂ).IsHermitian) β =
        gibbsState (spectralLift_hermitian (1 : Matrix.unitaryGroup Bool ℂ)
          (fun _ : Bool => (0 : ℝ))) β :=
      (gibbsState_congr _ _ hz β).symm
    _ = spectralLift (1 : Matrix.unitaryGroup Bool ℂ) (fun _ : Bool => (1 : ℝ) / 2) := hg
    _ = _ := by simp [spectralLift, rotate]

/-- The reservoir state is fixed by its zero Hamiltonian. -/
def bitBath : Matrix Bool Bool ℂ := realDiagonal (fun _ => (1 : ℝ) / 2)

/-- A controlled binary permutation acts on the stated system and reservoir coordinates. -/
def controlledNotMatrix : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun i j => if i.1 = j.1 ∧ i.2 = Bool.xor j.1 j.2 then 1 else 0

/-- Both unitary equations are checked on the complete four-dimensional carrier. -/
def controlledNotUnitary : Matrix.unitaryGroup (Bool × Bool) ℂ := by
  refine ⟨controlledNotMatrix, ?_, ?_⟩
  · ext ⟨i, r⟩ ⟨j, s⟩
    cases i <;> cases r <;> cases j <;> cases s <;>
      norm_num [Matrix.mul_apply, Matrix.star_apply, controlledNotMatrix, Fintype.sum_prod_type]
  · ext ⟨i, r⟩ ⟨j, s⟩
    cases i <;> cases r <;> cases j <;> cases s <;>
      norm_num [Matrix.mul_apply, Matrix.star_apply, controlledNotMatrix, Fintype.sum_prod_type]

/-- The source channel retains precisely the population entries. -/
def bitDephase (a : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ := Matrix.diagonal (fun i => a i i)

/-- The unitary and reservoir implement the complete dephasing operation on every matrix. -/
theorem controlledNot_realizes_dephasing (a : Matrix Bool Bool ℂ) :
    marginalLeft (rotate controlledNotUnitary (a ⊗ₖ bitBath)) = bitDephase a := by
  ext i j
  cases i <;> cases j <;>
    norm_num [marginalLeft, rotate, controlledNotUnitary, controlledNotMatrix,
      Matrix.mul_apply, Matrix.star_apply, Matrix.kronecker_apply, Fintype.sum_prod_type,
      bitBath, realDiagonal, bitDephase] <;> ring

/-- The same all-input operation returns the reservoir state multiplied by the input trace. -/
theorem controlledNot_reservoir (a : Matrix Bool Bool ℂ) :
    marginalRight (rotate controlledNotUnitary (a ⊗ₖ bitBath)) = a.trace • bitBath := by
  ext i j
  cases i <;> cases j <;>
    norm_num [marginalRight, rotate, controlledNotUnitary, controlledNotMatrix,
      Matrix.mul_apply, Matrix.star_apply, Matrix.kronecker_apply, Fintype.sum_prod_type,
      bitBath, realDiagonal, Matrix.trace, Matrix.diag] <;> ring

/-- The recorded branch is the projection onto its retained binary label. -/
def bitProjector (y : Bool) : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun i => if i = y then 1 else 0)

def bitBranch (y : Bool) (a : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  bitProjector y * a * bitProjector y

/-- Summing the recorded branches produces the same source channel. -/
theorem bitBranch_total (a : Matrix Bool Bool ℂ) :
    (∑ y : Bool, bitBranch y a) = bitDephase a := by
  ext i j
  cases i <;> cases j <;>
    simp [bitBranch, bitProjector, bitDephase, Matrix.mul_apply, Matrix.sum_apply]

/-- Reading an output label of the thermal channel gives its stated branch on every input. -/
theorem controlledNot_recorded_branch (a : Matrix Bool Bool ℂ) (y : Bool) :
    bitProjector y * marginalLeft (rotate controlledNotUnitary (a ⊗ₖ bitBath)) * bitProjector y =
      bitBranch y a := by
  rw [controlledNot_realizes_dephasing]
  ext i j
  cases i <;> cases j <;> cases y <;>
    simp [bitBranch, bitProjector, bitDephase, Matrix.mul_apply]

/-- The same channel is obtained from the declared Gibbs state and unitary at positive temperature. -/
theorem thermalControlledNot_channel (a : Matrix Bool Bool ℂ) (β : ℝ) :
    marginalLeft (thermalJoint controlledNotUnitary a Matrix.isHermitian_zero β) = bitDephase a := by
  rw [thermalJoint, gibbsState_zero]
  exact controlledNot_realizes_dephasing a

/-- The zero Hamiltonian makes heat zero for this particular operation. -/
theorem thermalControlledNot_heat (a : Matrix Bool Bool ℂ) (β : ℝ) :
    reservoirHeat controlledNotUnitary a Matrix.isHermitian_zero β = 0 := by
  simp [reservoirHeat, meanEnergy]

/-- Population agreement at one state cannot identify the operation. -/
theorem endpoint_agreement_does_not_identify_channel :
    bitDephase bitBath = bitBath ∧
      bitDephase (fun i j : Bool => if i = false ∧ j = true then 1 else 0) ≠
        (fun i j : Bool => if i = false ∧ j = true then 1 else 0) := by
  constructor
  · ext i j
    cases i <;> cases j <;> simp [bitDephase, bitBath, realDiagonal]
  · intro h
    have he := congrFun (congrFun h false) true
    norm_num [bitDephase] at he

end OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Thermal

/-! ## M5.3: the operational source, stated before any representation

Graph nodes M5_3 and M5_4. The definitions in this namespace copy the specification text of
UniversalObservationSpec.lean. `OperationalData`, `OperationalLaws` and `SelectionConditions`
mention no matrix, no Hilbert space and no complex scalar. Matrices enter only through the
representation target `QuantumRealization`, which is a structure to construct and never a
field of a framework predicate.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

/-- Specification positivity convention, with its explicit double sum. -/
def PSD {n : ℕ} (a : Mat n) : Prop :=
  a = dagger a ∧ ∀ v : Fin n → ℂ,
    0 ≤ (∑ i, ∑ j, star (v i) * a i j * v j).re

def Density (n : ℕ) := {a : Mat n // PSD a ∧ tr a = 1}
def Effect (n : ℕ) := {a : Mat n // PSD a ∧ PSD (1-a)}

/-- The specification convention and the native Mathlib positivity agree on every matrix. -/
theorem psd_iff_posSemidef {n : ℕ} (a : Mat n) : PSD a ↔ a.PosSemidef :=
  entrywisePSD_iff_posSemidef a

/-- An operational source, before any Hilbert-space representation. -/
structure OperationalData where
  Obj : Type
  State : Obj → Type
  Test : Obj → Type
  Process : Obj → Obj → Type
  tensor : Obj → Obj → Obj
  prob : {A : Obj} → Test A → State A → ℝ
  mix : {A : Obj} → ℝ → State A → State A → State A
  act : {A B : Obj} → Process A B → State A → State B
  weight : {A B : Obj} → Process A B → State A → ℝ
  ident : (A : Obj) → Process A A
  compose : {A B C : Obj} → Process B C → Process A B → Process A C
  unitTest : (A : Obj) → Test A
  deterministicTest : {A : Obj} → Test A → Prop
  jointTest : {A B : Obj} → Test A → Test B → Test (tensor A B)
  productState : {A B : Obj} → State A → State B → State (tensor A B)
  parallel : {A B C E : Obj} → Process A B → Process C E →
    Process (tensor A C) (tensor B E)
  marginal : {A B : Obj} → State (tensor A B) → State A
  actRight : {A B : Obj} → Process B B → State (tensor A B) → State (tensor A B)
  condition : {A B : Obj} → Test A → State (tensor A B) → Option (State B)

/-- D5: positive outcomes have normalized conditional states with the same joint statistics. -/
def ConditioningLaws (D : OperationalData) : Prop :=
  (∀ (A B : D.Obj) (s : D.State (D.tensor A B)) (e : D.Test A),
    let p := D.prob (D.jointTest e (D.unitTest B)) s
    (D.condition e s = none ↔ p = 0) ∧
    (0 < p → ∃ t, D.condition e s = some t) ∧
    ∀ t, D.condition e s = some t → 0 < p ∧
      ∀ f : D.Test B, p * D.prob f t = D.prob (D.jointTest e f) s) ∧
  (∀ (A B : D.Obj) (s : D.State (D.tensor A B)) (e : D.Test A),
    D.prob (D.jointTest e (D.unitTest B)) s = D.prob e (D.marginal s)) ∧
  (∀ (A B : D.Obj) (s : D.State A) (t : D.State B) (e : D.Test A) (f : D.Test B),
    D.prob (D.jointTest e f) (D.productState s t) = D.prob e s * D.prob f t)

/-- Basic consistency laws still require their own source construction. -/
def OperationalLaws (D : OperationalData) : Prop :=
  ConditioningLaws D ∧
  (∀ (A : D.Obj) (s : D.State A) (e : D.Test A),
    0 ≤ D.prob e s ∧ D.prob e s ≤ 1) ∧
  (∀ (A : D.Obj) (s : D.State A), D.prob (D.unitTest A) s = 1) ∧
  (∀ (A : D.Obj) (s t : D.State A),
    (∀ e, D.prob e s = D.prob e t) → s = t) ∧
  (∀ (A : D.Obj) (s t : D.State A) (p : ℝ), 0 ≤ p → p ≤ 1 →
    ∀ e, D.prob e (D.mix p s t) = p * D.prob e s + (1-p) * D.prob e t) ∧
  (∀ (A : D.Obj) (s : D.State A), D.act (D.ident A) s = s) ∧
  (∀ (A B C : D.Obj) (f : D.Process A B) (g : D.Process B C) (s : D.State A),
    D.act (D.compose g f) s = D.act g (D.act f s)) ∧
  (∀ (A B : D.Obj) (f : D.Process A B) (s : D.State A),
    0 ≤ D.weight f s ∧ D.weight f s ≤ 1) ∧
  (∀ (A B C : D.Obj) (f : D.Process A B) (g : D.Process B C) (s : D.State A),
    D.weight (D.compose g f) s = D.weight f s * D.weight g (D.act f s))

def Pure (D : OperationalData) {A : D.Obj} (s : D.State A) : Prop :=
  ∀ (p : ℝ) (a b : D.State A), 0 < p → p < 1 →
    D.mix p a b = s → a = s ∧ b = s

def InFace (D : OperationalData) {A : D.Obj} (s t : D.State A) : Prop :=
  ∃ (p : ℝ) (u : D.State A), 0 < p ∧ p ≤ 1 ∧ D.mix p t u = s

def Reversible (D : OperationalData) {A : D.Obj} (f : D.Process A A) : Prop :=
  ∃ g : D.Process A A, (∀ s, D.weight f s = 1 ∧ D.weight g s = 1) ∧
    (∀ s, D.act g (D.act f s) = s) ∧ ∀ s, D.act f (D.act g s) = s

def Causality (D : OperationalData) : Prop :=
  ∀ (A : D.Obj) (e : D.Test A), D.deterministicTest e →
    ∀ s, D.prob e s = D.prob (D.unitTest A) s

def PerfectDistinguishability (D : OperationalData) : Prop :=
  ∀ (A : D.Obj) (s : D.State A), (∃ t, ¬ InFace D s t) →
    ∃ (t : D.State A) (e : D.Test A), D.prob e s = 1 ∧ D.prob e t = 0

def IdealCompression (D : OperationalData) : Prop :=
  ∀ (A : D.Obj) (s : D.State A), ∃ (B : D.Obj) (enc : D.Process A B)
    (dec : D.Process B A),
    (∀ t, D.weight enc t = 1) ∧ (∀ u, D.weight dec u = 1) ∧
    (∀ t, InFace D s t → D.act dec (D.act enc t) = t) ∧
    ∀ u : D.State B, ∃ t, InFace D s t ∧ D.act enc t = u

def LocalTomography (D : OperationalData) : Prop :=
  ∀ (A B : D.Obj) (s t : D.State (D.tensor A B)),
    (∀ (e : D.Test A) (f : D.Test B),
      D.prob (D.jointTest e f) s = D.prob (D.jointTest e f) t) → s = t

/-- Atomicity expressed through positive decompositions, not an uninterpreted name. -/
def AtomicTest (D : OperationalData) {A : D.Obj} (e : D.Test A) : Prop :=
  (∃ s, D.prob e s ≠ 0) ∧
  ∀ (f g : D.Test A), (∀ s, D.prob e s = D.prob f s + D.prob g s) →
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ ∀ s, D.prob f s = p * D.prob e s

def PureConditioning (D : OperationalData) : Prop :=
  ∀ (A B : D.Obj) (s : D.State (D.tensor A B)) (e : D.Test A),
    Pure D s → AtomicTest D e → 0 < D.prob (D.jointTest e (D.unitTest B)) s →
    ∃ t : D.State B, D.condition e s = some t ∧ Pure D t

def Purification (D : OperationalData) : Prop :=
  (∀ (A : D.Obj) (s : D.State A), ∃ (B : D.Obj) (t : D.State (D.tensor A B)),
    Pure D t ∧ D.marginal t = s) ∧
  (∀ (A B : D.Obj) (s t : D.State (D.tensor A B)),
    Pure D s → Pure D t → D.marginal s = D.marginal t →
    ∃ u : D.Process B B, Reversible D u ∧ D.actRight u s = t)

/-- Reversible maps between two source systems must have probability one. -/
def ReversibleBetween (D : OperationalData) {A B : D.Obj} (f : D.Process A B) : Prop :=
  ∃ g : D.Process B A,
    (∀ s, D.weight f s = 1) ∧ (∀ t, D.weight g t = 1) ∧
    (∀ s, D.act g (D.act f s) = s) ∧ (∀ t, D.act f (D.act g t) = t)

/-- Deterministic process dilation with a genuinely pure environment.
The equivalence with purification is an obligation, not a definition. -/
def PureDilationGoal (D : OperationalData) : Prop :=
  ∀ (A B : D.Obj) (f : D.Process A B), (∀ s, D.weight f s = 1) →
    ∃ (E F : D.Obj) (η : D.State E) (u : D.Process (D.tensor A E) (D.tensor B F)),
      Pure D η ∧ ReversibleBetween D u ∧
      ∀ s, D.marginal (D.act u (D.productState s η)) = D.act f s

/-- These six candidates require full operational-framework alignment in M5.3.
They are not asserted here to suffice with the minimal OperationalLaws above. -/
def SelectionConditions (D : OperationalData) : Prop :=
  Causality D ∧ PerfectDistinguishability D ∧ IdealCompression D ∧
    LocalTomography D ∧ PureConditioning D ∧ Purification D

/-- A real target: onto states and effects with preserved probabilities. -/
def StateEffectRepresentationGoal (D : OperationalData) : Prop :=
  ∃ (dim : D.Obj → ℕ), (∀ A, 0 < dim A) ∧
    ∃ (states : (A : D.Obj) → D.State A ≃ Density (dim A))
      (effects : (A : D.Obj) → D.Test A ≃ Effect (dim A)),
      ∀ (A : D.Obj) (s : D.State A) (e : D.Test A),
        D.prob e s = (tr ((states A s).val * (effects A e).val)).re

/-- Complete positivity is ancillary positivity for every finite ancillary size. -/
def amplify {n m : ℕ} (f : Mat n →ₗ[ℂ] Mat m) (r : ℕ)
    (a : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    Matrix (Fin r × Fin m) (Fin r × Fin m) ℂ :=
  fun i j => f (fun x y => a (i.1,x) (j.1,y)) i.2 j.2

def GeneralPSD {I : Type} [Fintype I] (a : Matrix I I ℂ) : Prop :=
  (∀ i j, a i j = star (a j i)) ∧
  ∀ v : I → ℂ, 0 ≤ (∑ i, ∑ j, star (v i) * a i j * v j).re

def CompletelyPositive {n m : ℕ} (f : Mat n →ₗ[ℂ] Mat m) : Prop :=
  ∀ (r : ℕ) (a : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ),
    GeneralPSD a → GeneralPSD (amplify f r a)

def TraceNonIncreasing {n m : ℕ} (f : Mat n →ₗ[ℂ] Mat m) : Prop :=
  ∀ a, PSD a → (tr (f a)).re ≤ (tr a).re

/-- Equality of processes is tested with every source ancillary system.
Zero-weight branches are compared only through their weighted statistics. -/
def ProcessEquivalent (D : OperationalData) {A B : D.Obj}
    (f g : D.Process A B) : Prop :=
  ∀ (C : D.Obj) (s : D.State (D.tensor A C)) (e : D.Test (D.tensor B C)),
    D.weight (D.parallel f (D.ident C)) s * D.prob e (D.act (D.parallel f (D.ident C)) s) =
    D.weight (D.parallel g (D.ident C)) s * D.prob e (D.act (D.parallel g (D.ident C)) s)

/-- Constructing this structure is the representation target, not a hypothesis
that can stand in for its proof. Full source-framework alignment is M5.3. -/
structure QuantumRealization (D : OperationalData) where
  dim : D.Obj → ℕ
  dimension_positive : ∀ A, 0 < dim A
  states : (A : D.Obj) → D.State A ≃ Density (dim A)
  effects : (A : D.Obj) → D.Test A ≃ Effect (dim A)
  probabilities : ∀ A s e, D.prob e s = (tr ((states A s).val * (effects A e).val)).re
  maps : (A B : D.Obj) → D.Process A B → (Mat (dim A) →ₗ[ℂ] Mat (dim B))
  positivity : ∀ A B f, CompletelyPositive (maps A B f)
  trace_bound : ∀ A B f, TraceNonIncreasing (maps A B f)
  source_action : ∀ A B f s, maps A B f (states A s).val =
    (D.weight f s : ℂ) • (states B (D.act f s)).val
  composition : ∀ A B C f g, maps A C (D.compose g f) = (maps B C g).comp (maps A B f)
  operation_fullness : ∀ A B (f : Mat (dim A) →ₗ[ℂ] Mat (dim B)),
    CompletelyPositive f → TraceNonIncreasing f → ∃ g, maps A B g = f
  operation_faithfulness : ∀ A B (f g : D.Process A B),
    maps A B f = maps A B g ↔ ProcessEquivalent D f g
  pairIndex : (A B : D.Obj) → Fin (dim (D.tensor A B)) ≃ (Fin (dim A) × Fin (dim B))
  product_states : ∀ A B (s : D.State A) (t : D.State B) i j,
    (states (D.tensor A B) (D.productState s t)).val i j =
      (states A s).val (pairIndex A B i).1 (pairIndex A B j).1 *
      (states B t).val (pairIndex A B i).2 (pairIndex A B j).2
  product_effects : ∀ A B (e : D.Test A) (f : D.Test B) i j,
    (effects (D.tensor A B) (D.jointTest e f)).val i j =
      (effects A e).val (pairIndex A B i).1 (pairIndex A B j).1 *
      (effects B f).val (pairIndex A B i).2 (pairIndex A B j).2
  parallel_on_products : ∀ A B C E (f : D.Process A B) (g : D.Process C E)
      (a : Mat (dim A)) (b : Mat (dim C)) i j,
    maps (D.tensor A C) (D.tensor B E) (D.parallel f g)
      (fun r s => a (pairIndex A C r).1 (pairIndex A C s).1 *
        b (pairIndex A C r).2 (pairIndex A C s).2) i j =
      maps A B f a (pairIndex B E i).1 (pairIndex B E j).1 *
      maps C E g b (pairIndex B E i).2 (pairIndex B E j).2

/-- M5.3 supplies a fully defined operational framework before this implication is used.
Framework is an unresolved operational-premise specification, not an alias for realization.
Neither implication is proved by declaring this target. -/
def ReconstructionFromFrameworkGoal (framework : OperationalData → Prop) : Prop :=
  (∀ D, framework D → OperationalLaws D ∧ SelectionConditions D) ∧
  (∀ D, framework D → Nonempty (QuantumRealization D)) ∧
  ∃ D, framework D ∧ ∃ (A : D.Obj) (s t : D.State A), s ≠ t ∧ Pure D s ∧ Pure D t

/-! ### The six conditions and the minimal laws do not select quantum theory

A theory with one state, one test and one process per system satisfies every conjunct of
`OperationalLaws` and of `SelectionConditions`. Its test space is a single point, while every
positive dimension carries the two distinct effects `0` and `1`, so no realization exists.
The framework of M5.4 therefore needs operational premises beyond these two predicates.
-/

/-- The one-state theory: a single state, test and process on the single system. -/
def trivialData : OperationalData where
  Obj := Unit
  State _ := Unit
  Test _ := Unit
  Process _ _ := Unit
  tensor _ _ := ()
  prob _ _ := 1
  mix _ _ _ := ()
  act _ _ := ()
  weight _ _ := 1
  ident _ := ()
  compose _ _ := ()
  unitTest _ := ()
  deterministicTest _ := True
  jointTest _ _ := ()
  productState _ _ := ()
  parallel _ _ := ()
  marginal _ := ()
  actRight _ _ := ()
  condition _ _ := some ()

theorem trivialData_conditioningLaws : ConditioningLaws trivialData := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B s e
    show ((some () : Option Unit) = none ↔ (1 : ℝ) = 0) ∧
      ((0 : ℝ) < 1 → ∃ t : Unit, (some () : Option Unit) = some t) ∧
      ∀ t : Unit, (some () : Option Unit) = some t → (0 : ℝ) < 1 ∧
        ∀ _f : Unit, (1 : ℝ) * 1 = 1
    exact ⟨⟨fun h => Option.noConfusion h, fun h => absurd h one_ne_zero⟩,
      fun _ => ⟨(), rfl⟩, fun _ _ => ⟨one_pos, fun _ => mul_one 1⟩⟩
  · intro A B s e
    rfl
  · intro A B s t e f
    show (1 : ℝ) = 1 * 1
    rw [mul_one]

theorem trivialData_operationalLaws : OperationalLaws trivialData := by
  refine ⟨trivialData_conditioningLaws, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A s e
    exact ⟨zero_le_one, le_rfl⟩
  · intro A s
    rfl
  · intro A s t _h
    rfl
  · intro A s t p _hp0 _hp1 e
    show (1 : ℝ) = p * 1 + (1 - p) * 1
    ring
  · intro A s
    rfl
  · intro A B C f g s
    rfl
  · intro A B f s
    exact ⟨zero_le_one, le_rfl⟩
  · intro A B C f g s
    show (1 : ℝ) = 1 * 1
    rw [mul_one]

theorem trivialData_pure {A : trivialData.Obj} (s : trivialData.State A) :
    Pure trivialData s :=
  fun _ _ _ _ _ _ => ⟨rfl, rfl⟩

theorem trivialData_inFace {A : trivialData.Obj} (s t : trivialData.State A) :
    InFace trivialData s t :=
  ⟨1, (), one_pos, le_rfl, rfl⟩

theorem trivialData_selectionConditions : SelectionConditions trivialData := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A e _he s
    rfl
  · intro A s hs
    obtain ⟨t, ht⟩ := hs
    exact absurd (trivialData_inFace s t) ht
  · intro A s
    exact ⟨(), (), (), fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
      fun _ => ⟨(), trivialData_inFace s (), rfl⟩⟩
  · intro A B s t _h
    rfl
  · intro A B s e _hs _he _hp
    exact ⟨(), rfl, trivialData_pure ()⟩
  · intro A s
    exact ⟨(), (), trivialData_pure (), rfl⟩
  · intro A B s t _hs _ht _hm
    exact ⟨(), ⟨(), fun _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩, rfl⟩

/-- The zero matrix is an effect in every dimension. -/
def zeroEffect (n : ℕ) : Effect n :=
  ⟨0, (psd_iff_posSemidef 0).mpr Matrix.PosSemidef.zero,
    (psd_iff_posSemidef (1 - 0)).mpr (by rw [sub_zero]; exact Matrix.PosSemidef.one)⟩

/-- The unit matrix is an effect in every dimension. -/
def unitEffect (n : ℕ) : Effect n :=
  ⟨1, (psd_iff_posSemidef 1).mpr Matrix.PosSemidef.one,
    (psd_iff_posSemidef (1 - 1)).mpr (by rw [sub_self]; exact Matrix.PosSemidef.zero)⟩

theorem zeroEffect_ne_unitEffect {n : ℕ} (hn : 0 < n) : zeroEffect n ≠ unitEffect n := by
  intro h
  have he := congrArg (fun e : Effect n => e.val ⟨0, hn⟩ ⟨0, hn⟩) h
  change (0 : Mat n) ⟨0, hn⟩ ⟨0, hn⟩ = (1 : Mat n) ⟨0, hn⟩ ⟨0, hn⟩ at he
  rw [Matrix.zero_apply, Matrix.one_apply_eq] at he
  exact zero_ne_one he

/-- The one-state theory has no quantum realization in any positive dimension. -/
theorem trivialData_no_realization : ¬ Nonempty (QuantumRealization trivialData) := by
  rintro ⟨r⟩
  have hpos := r.dimension_positive ()
  have hsame : (r.effects ()).symm (zeroEffect (r.dim ())) =
      (r.effects ()).symm (unitEffect (r.dim ())) := rfl
  exact zeroEffect_ne_unitEffect hpos ((r.effects ()).symm.injective hsame)

/-- STATEMENT CHANGE evidence for M5.4: the framework made of the minimal laws and the six
selection conditions fails the reconstruction target, through its realization clause. -/
theorem minimalFramework_not_reconstruction :
    ¬ ReconstructionFromFrameworkGoal (fun D => OperationalLaws D ∧ SelectionConditions D) := by
  rintro ⟨_, hreal, _⟩
  exact trivialData_no_realization
    (hreal trivialData ⟨trivialData_operationalLaws, trivialData_selectionConditions⟩)

end OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

/-! ## M5.3 and M5.4: ray tests separate states and effects

A nonzero vector `v` gives the rank-one matrix `v v*`, normalized by its squared length.
That matrix is a density and an effect at once. Its tests read the quadratic form of a
Hermitian matrix at `v`, so the ray tests determine every Hermitian matrix. These lemmas
supply the separation steps of the probability rule.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

/-- The rank-one matrix of a column vector. -/
def ray {n : ℕ} (v : Fin n → ℂ) : Mat n := Matrix.vecMulVec v (star v)

theorem ray_apply {n : ℕ} (v : Fin n → ℂ) (i j : Fin n) :
    ray v i j = v i * star (v j) := rfl

theorem ray_mulVec {n : ℕ} (v x : Fin n → ℂ) : ray v *ᵥ x = (star v ⬝ᵥ x) • v := by
  ext i
  simp only [Matrix.mulVec, dotProduct, ray_apply, Pi.smul_apply, smul_eq_mul,
    Pi.star_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

theorem ray_quadratic {n : ℕ} (v x : Fin n → ℂ) :
    star x ⬝ᵥ (ray v *ᵥ x) = star (star v ⬝ᵥ x) * (star v ⬝ᵥ x) := by
  rw [ray_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.star_dotProduct, mul_comm]

theorem ray_posSemidef {n : ℕ} (v : Fin n → ℂ) : (ray v).PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    rw [Matrix.conjTranspose_apply, ray_apply, ray_apply, star_mul', star_star, mul_comm]
  · rw [ray_quadratic]
    exact star_mul_self_nonneg _

theorem trace_ray_mul {n : ℕ} (v : Fin n → ℂ) (X : Mat n) :
    (ray v * X).trace = star v ⬝ᵥ (X *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ray_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem ray_mul_ray {n : ℕ} (v : Fin n → ℂ) : ray v * ray v = (star v ⬝ᵥ v) • ray v := by
  ext i j
  simp only [Matrix.mul_apply, ray_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
    Pi.star_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- A nonnegative real multiple of a positive matrix is positive. -/
theorem posSemidef_real_smul {n : ℕ} {a : Mat n} (ha : a.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    ((c : ℂ) • a).PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · change ((c : ℂ) • a)ᴴ = (c : ℂ) • a
    rw [Matrix.conjTranspose_smul, ha.1.eq, Complex.star_def, Complex.conj_ofReal]
  · rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg (Complex.zero_le_real.mpr hc) (ha.2 x)

/-- The squared length of a vector, read as a real number. -/
def sqLength {n : ℕ} (v : Fin n → ℂ) : ℝ := (star v ⬝ᵥ v).re

theorem dotProduct_self_eq_sqLength {n : ℕ} (v : Fin n → ℂ) :
    star v ⬝ᵥ v = (sqLength v : ℂ) := by
  have h := Complex.nonneg_iff.mp (dotProduct_star_self_nonneg v)
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im]
    exact h.2.symm

theorem sqLength_pos {n : ℕ} {v : Fin n → ℂ} (hv : v ≠ 0) : 0 < sqLength v :=
  (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hv)).1

/-- The normalized ray matrix. -/
def normRay {n : ℕ} (v : Fin n → ℂ) : Mat n := (((sqLength v)⁻¹ : ℝ) : ℂ) • ray v

theorem normRay_posSemidef {n : ℕ} (v : Fin n → ℂ) : (normRay v).PosSemidef :=
  posSemidef_real_smul (ray_posSemidef v)
    (inv_nonneg.mpr (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg v)).1)

theorem trace_normRay_mul {n : ℕ} (v : Fin n → ℂ) (X : Mat n) :
    (normRay v * X).trace = (((sqLength v)⁻¹ : ℝ) : ℂ) * (star v ⬝ᵥ (X *ᵥ v)) := by
  rw [normRay, Matrix.smul_mul, Matrix.trace_smul, trace_ray_mul, smul_eq_mul]

theorem re_trace_normRay_mul {n : ℕ} (v : Fin n → ℂ) (X : Mat n) :
    (normRay v * X).trace.re = (sqLength v)⁻¹ * (star v ⬝ᵥ (X *ᵥ v)).re := by
  rw [trace_normRay_mul, Complex.re_ofReal_mul]

theorem normRay_trace {n : ℕ} {v : Fin n → ℂ} (hv : v ≠ 0) : (normRay v).trace = 1 := by
  have h := trace_normRay_mul v 1
  rw [Matrix.mul_one, Matrix.one_mulVec, dotProduct_self_eq_sqLength, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (sqLength_pos hv).ne', Complex.ofReal_one] at h
  exact h

theorem normRay_idempotent {n : ℕ} {v : Fin n → ℂ} (hv : v ≠ 0) :
    normRay v * normRay v = normRay v := by
  have hs : (sqLength v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sqLength_pos hv).ne'
  simp only [normRay, Matrix.smul_mul, Matrix.mul_smul, ray_mul_ray, smul_smul,
    dotProduct_self_eq_sqLength, Complex.ofReal_inv]
  congr 1
  field_simp

theorem one_sub_normRay_posSemidef {n : ℕ} {v : Fin n → ℂ} (hv : v ≠ 0) :
    (1 - normRay v).PosSemidef := by
  have hh : (normRay v)ᴴ = normRay v := (normRay_posSemidef v).1.eq
  have he : (1 - normRay v)ᴴ * (1 - normRay v) = 1 - normRay v := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hh, sub_mul, mul_sub, mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, normRay_idempotent hv]
    abel
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The normalized ray as a density. -/
def rayState {n : ℕ} (v : Fin n → ℂ) (hv : v ≠ 0) : Density n :=
  ⟨normRay v, (psd_iff_posSemidef _).mpr (normRay_posSemidef v), normRay_trace hv⟩

/-- The normalized ray as an effect. -/
def rayEffect {n : ℕ} (v : Fin n → ℂ) (hv : v ≠ 0) : Effect n :=
  ⟨normRay v, (psd_iff_posSemidef _).mpr (normRay_posSemidef v),
    (psd_iff_posSemidef _).mpr (one_sub_normRay_posSemidef hv)⟩

/-- Quadratic forms at every vector determine a Hermitian matrix. -/
theorem hermitian_eq_of_forms {n : ℕ} {X Y : Mat n} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (h : ∀ v : Fin n → ℂ, (star v ⬝ᵥ (X *ᵥ v)).re = (star v ⬝ᵥ (Y *ᵥ v)).re) : X = Y := by
  apply QuantumReconstruction.reports_determine_state X Y
    ((hermitian_iff_reportHermitian X).mp hX) ((hermitian_iff_reportHermitian Y).mp hY)
  · intro i
    simp only [QuantumReconstruction.population, form_eq_dotProduct]
    exact h _
  · intro i j _hij
    simp only [QuantumReconstruction.plusReport, form_eq_dotProduct]
    rw [h]
  · intro i j _hij
    simp only [QuantumReconstruction.phaseReport, form_eq_dotProduct]
    rw [h]

/-- The normalized ray tests determine a Hermitian matrix. -/
theorem hermitian_eq_of_ray_tests {n : ℕ} {X Y : Mat n} (hX : X.IsHermitian)
    (hY : Y.IsHermitian)
    (h : ∀ v : Fin n → ℂ, (hv : v ≠ 0) → (normRay v * X).trace.re = (normRay v * Y).trace.re) :
    X = Y := by
  apply hermitian_eq_of_forms hX hY
  intro v
  by_cases hv : v = 0
  · subst hv
    rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
  · have hvt := h v hv
    rw [re_trace_normRay_mul, re_trace_normRay_mul] at hvt
    exact mul_left_cancel₀ (inv_ne_zero (sqLength_pos hv).ne') hvt

/-- Hermitian matrices with equal statistics in every density are equal. -/
theorem hermitian_eq_of_density_tests {n : ℕ} {X Y : Mat n} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (h : ∀ ρ : Density n, (tr (ρ.val * X)).re = (tr (ρ.val * Y)).re) :
    X = Y :=
  hermitian_eq_of_ray_tests hX hY (fun v hv => h (rayState v hv))

/-- Hermitian matrices with equal statistics on every effect are equal. -/
theorem hermitian_eq_of_effect_tests {n : ℕ} {X Y : Mat n} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (h : ∀ e : Effect n, (tr (X * e.val)).re = (tr (Y * e.val)).re) :
    X = Y := by
  apply hermitian_eq_of_ray_tests hX hY
  intro v hv
  rw [Matrix.trace_mul_comm (normRay v) X, Matrix.trace_mul_comm (normRay v) Y]
  exact h (rayEffect v hv)

theorem density_hermitian {n : ℕ} (ρ : Density n) : ρ.val.IsHermitian :=
  ((psd_iff_posSemidef _).mp ρ.property.1).1

theorem effect_hermitian {n : ℕ} (e : Effect n) : e.val.IsHermitian :=
  ((psd_iff_posSemidef _).mp e.property.1).1

/-- Densities are separated by effects. -/
theorem density_ext_of_effects {n : ℕ} (ρ σ : Density n)
    (h : ∀ e : Effect n, (tr (ρ.val * e.val)).re = (tr (σ.val * e.val)).re) : ρ = σ :=
  Subtype.ext (hermitian_eq_of_effect_tests (density_hermitian ρ) (density_hermitian σ) h)

/-- Effects are separated by densities. -/
theorem effect_ext_of_densities {n : ℕ} (e f : Effect n)
    (h : ∀ ρ : Density n, (tr (ρ.val * e.val)).re = (tr (ρ.val * f.val)).re) : e = f :=
  Subtype.ext (hermitian_eq_of_density_tests (effect_hermitian e) (effect_hermitian f) h)

/-! ### Consequences of a realization of a lawful operational source

These theorems read off the probability rule. They hold for every operational source with
`OperationalLaws` and a `QuantumRealization`, so each states a necessary condition that any
operational framework selecting quantum theory must satisfy.
-/

section RealizationConsequences

variable {D : OperationalData}

/-- The probability rule read at an arbitrary density of the realized system. -/
theorem realization_prob_symm (r : QuantumRealization D) (A : D.Obj) (ρ : Density (r.dim A))
    (e : D.Test A) :
    D.prob e ((r.states A).symm ρ) = (tr (ρ.val * (r.effects A e).val)).re := by
  rw [r.probabilities, Equiv.apply_symm_apply]

/-- The unit test is represented by the unit matrix. -/
theorem realization_unit_effect (hL : OperationalLaws D) (r : QuantumRealization D)
    (A : D.Obj) : (r.effects A (D.unitTest A)).val = 1 := by
  apply hermitian_eq_of_density_tests (effect_hermitian _) Matrix.isHermitian_one
  intro ρ
  rw [← realization_prob_symm r A ρ, hL.2.2.1, Matrix.mul_one, ρ.property.2, Complex.one_re]

/-- Operationally identical raw tests are equal: a realization forces effect extensionality.
A source that duplicates a test while keeping its statistics has no realization. -/
theorem realization_effect_ext (r : QuantumRealization D) (A : D.Obj) (e f : D.Test A)
    (h : ∀ s, D.prob e s = D.prob f s) : e = f := by
  apply (r.effects A).injective
  apply effect_ext_of_densities
  intro ρ
  rw [← realization_prob_symm r A ρ, ← realization_prob_symm r A ρ]
  exact h _

/-- Mixing is represented by the convex combination of density matrices. -/
theorem realization_mix (hL : OperationalLaws D) (r : QuantumRealization D) (A : D.Obj)
    (s t : D.State A) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (r.states A (D.mix p s t)).val =
      (p : ℂ) • (r.states A s).val + ((1 - p : ℝ) : ℂ) • (r.states A t).val := by
  have hherm : ((p : ℂ) • (r.states A s).val + ((1 - p : ℝ) : ℂ) • (r.states A t).val).IsHermitian :=
    ((posSemidef_real_smul ((psd_iff_posSemidef _).mp (r.states A s).property.1) hp0).add
      (posSemidef_real_smul ((psd_iff_posSemidef _).mp (r.states A t).property.1)
        (sub_nonneg.mpr hp1))).1
  apply hermitian_eq_of_effect_tests (density_hermitian _) hherm
  intro e
  have h := hL.2.2.2.2.1 A s t p hp0 hp1 ((r.effects A).symm e)
  rw [r.probabilities, r.probabilities, r.probabilities, Equiv.apply_symm_apply] at h
  rw [h]
  simp only [tr, Matrix.add_mul, Matrix.trace_add, Complex.add_re, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- The state map of a realization is injective on operational states. -/
theorem realization_states_val_injective (r : QuantumRealization D) (A : D.Obj)
    {s t : D.State A} (h : (r.states A s).val = (r.states A t).val) : s = t :=
  (r.states A).injective (Subtype.ext h)

end RealizationConsequences

end OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

/-! ## M5.4 composites: paired indices, partial trace and local tomography

`pairMatrix π a b` is the Kronecker product read through an index pairing `π`. A realization
uses its `pairIndex` this way for product states and product effects. Rays span all matrices
over the complex numbers, so product ray tests separate joint Hermitian matrices. Hence every
lawful source with a realization is locally tomographic.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

/-- The Kronecker product of two matrices read through a pairing of joint indices. -/
def pairMatrix {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (a : Mat n) (b : Mat m) : Mat N :=
  fun i j => a (π i).1 (π j).1 * b (π i).2 (π j).2

/-- Partial trace over the second factor of a paired joint index. -/
def traceRight {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (x : Mat N) : Mat n :=
  fun i j => ∑ k, x (π.symm (i, k)) (π.symm (j, k))

theorem sum_pair {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (g : Fin N → ℂ) :
    (∑ p, g p) = ∑ i, ∑ k, g (π.symm (i, k)) := by
  rw [← Equiv.sum_comp π.symm g, Fintype.sum_prod_type]

/-- The trace of a joint matrix against a paired product, expanded on the factor indices. -/
theorem trace_mul_pairMatrix {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (x : Mat N)
    (a : Mat n) (b : Mat m) :
    (x * pairMatrix π a b).trace =
      ∑ i, ∑ k, ∑ j, ∑ l, x (π.symm (i, k)) (π.symm (j, l)) * (a j i * b l k) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [sum_pair π]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro k _hk
  rw [sum_pair π]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro l _hl
  simp only [pairMatrix, Equiv.apply_symm_apply]

/-- Testing a joint matrix with a first-factor effect reads its partial trace. -/
theorem trace_mul_pairMatrix_one {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (x : Mat N)
    (a : Mat n) : (x * pairMatrix π a 1).trace = (traceRight π x * a).trace := by
  rw [trace_mul_pairMatrix]
  have hinner : ∀ i k j, (∑ l, x (π.symm (i, k)) (π.symm (j, l)) * (a j i * (1 : Mat m) l k)) =
      x (π.symm (i, k)) (π.symm (j, k)) * a j i := by
    intro i k j
    rw [Finset.sum_eq_single k]
    · rw [Matrix.one_apply_eq, mul_one]
    · intro l _hl hlk
      rw [Matrix.one_apply_ne hlk, mul_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  simp only [hinner]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceRight, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  exact Finset.sum_comm

theorem pairMatrix_smul {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (c d : ℂ) (a : Mat n)
    (b : Mat m) : pairMatrix π (c • a) (d • b) = (c * d) • pairMatrix π a b := by
  ext i j
  simp only [pairMatrix, Matrix.smul_apply, smul_eq_mul]
  ring

theorem pairMatrix_add_left {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (a a' : Mat n)
    (b : Mat m) : pairMatrix π (a + a') b = pairMatrix π a b + pairMatrix π a' b := by
  ext i j
  simp only [pairMatrix, Matrix.add_apply, add_mul]

theorem pairMatrix_add_right {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (a : Mat n)
    (b b' : Mat m) : pairMatrix π a (b + b') = pairMatrix π a b + pairMatrix π a b' := by
  ext i j
  simp only [pairMatrix, Matrix.add_apply, mul_add]

theorem pairMatrix_smul_left {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (c : ℂ) (a : Mat n)
    (b : Mat m) : pairMatrix π (c • a) b = c • pairMatrix π a b := by
  ext i j
  simp only [pairMatrix, Matrix.smul_apply, smul_eq_mul, mul_assoc]

theorem pairMatrix_smul_right {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (c : ℂ) (a : Mat n)
    (b : Mat m) : pairMatrix π a (c • b) = c • pairMatrix π a b := by
  ext i j
  simp only [pairMatrix, Matrix.smul_apply, smul_eq_mul]
  ring

theorem pairMatrix_hermitian {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) {a : Mat n} {b : Mat m}
    (ha : a.IsHermitian) (hb : b.IsHermitian) : (pairMatrix π a b).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  simp only [pairMatrix]
  rw [star_mul', ← Matrix.conjTranspose_apply a, ← Matrix.conjTranspose_apply b, ha.eq, hb.eq]

theorem traceRight_hermitian {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) {x : Mat N}
    (hx : x.IsHermitian) : (traceRight π x).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  simp only [traceRight, star_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [← Matrix.conjTranspose_apply x, hx.eq]

/-- The trace of a product of two Hermitian matrices is real. -/
theorem trace_mul_hermitian_im {N : ℕ} {x y : Mat N} (hx : x.IsHermitian) (hy : y.IsHermitian) :
    (x * y).trace.im = 0 := by
  have h : star ((x * y).trace) = (x * y).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hx.eq, hy.eq,
      Matrix.trace_mul_comm]
  have him := congrArg Complex.im h
  rw [Complex.star_def, Complex.conj_im] at him
  linarith

/-! ### Rays span every matrix -/

theorem vecMulVec_eq_rays {n : ℕ} (v w : Fin n → ℂ) :
    Matrix.vecMulVec v (star w) =
      (1 / 2 : ℂ) • (ray (v + w) - ray v - ray w) +
        (Complex.I / 2) • (ray (v + Complex.I • w) - ray v - ray w) := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, ray_apply, Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add, star_mul',
    Complex.star_def, Complex.conj_I]
  linear_combination ((1 / 2 : ℂ) * v a * (starRingEnd ℂ) (w b) -
    (1 / 2 : ℂ) * w a * (starRingEnd ℂ) (v b) +
    (Complex.I / 2) * w a * (starRingEnd ℂ) (w b)) * Complex.I_sq

theorem single_one_apply {n : ℕ} (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) c d = if a = c ∧ b = d then 1 else 0 := rfl

theorem single_eq_vecMulVec {n : ℕ} (i j : Fin n) :
    Matrix.single i j (1 : ℂ) = Matrix.vecMulVec (Pi.single i 1) (star (Pi.single j 1)) := by
  ext a b
  rw [single_one_apply, Matrix.vecMulVec_apply, Pi.star_apply, Pi.single_apply, Pi.single_apply]
  by_cases ha : a = i
  · subst ha
    by_cases hb : b = j
    · subst hb
      simp
    · simp [hb, Ne.symm hb]
  · simp [ha, Ne.symm ha]

/-- A joint matrix entry is read by a product of matrix units. -/
theorem trace_mul_pairMatrix_single {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (x : Mat N)
    (i j : Fin n) (k l : Fin m) :
    (x * pairMatrix π (Matrix.single j i 1) (Matrix.single l k 1)).trace =
      x (π.symm (i, k)) (π.symm (j, l)) := by
  rw [trace_mul_pairMatrix]
  rw [Fintype.sum_eq_single i (fun i' hi' => by
    apply Finset.sum_eq_zero
    intro k' _hk'
    apply Finset.sum_eq_zero
    intro j' _hj'
    apply Finset.sum_eq_zero
    intro l' _hl'
    rw [single_one_apply, if_neg (fun h => hi' h.2.symm), zero_mul, mul_zero])]
  rw [Fintype.sum_eq_single k (fun k' hk' => by
    apply Finset.sum_eq_zero
    intro j' _hj'
    apply Finset.sum_eq_zero
    intro l' _hl'
    rw [single_one_apply l k, if_neg (fun h => hk' h.2.symm), mul_zero, mul_zero])]
  rw [Fintype.sum_eq_single j (fun j' hj' => by
    apply Finset.sum_eq_zero
    intro l' _hl'
    rw [single_one_apply j i, if_neg (fun h => hj' h.1.symm), zero_mul, mul_zero])]
  rw [Fintype.sum_eq_single l (fun l' hl' => by
    rw [single_one_apply l k, if_neg (fun h => hl' h.1.symm), mul_zero, mul_zero])]
  rw [single_one_apply, single_one_apply, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, mul_one,
    mul_one]

/-- An additive, complex-homogeneous function that vanishes on every ray vanishes everywhere. -/
theorem vanish_of_rays {n : ℕ} (f : Mat n → ℂ) (hadd : ∀ a b, f (a + b) = f a + f b)
    (hsmul : ∀ (c : ℂ) a, f (c • a) = c * f a) (hray : ∀ v, f (ray v) = 0) (a : Mat n) :
    f a = 0 := by
  let F : Mat n →+ ℂ := AddMonoidHom.mk' f hadd
  have hsub : ∀ a b, f (a - b) = f a - f b := fun a b => map_sub F a b
  have hvw : ∀ v w : Fin n → ℂ, f (Matrix.vecMulVec v (star w)) = 0 := by
    intro v w
    rw [vecMulVec_eq_rays, hadd, hsmul, hsmul, hsub, hsub, hsub, hsub, hray, hray, hray, hray]
    ring
  have hsingle : ∀ i j, f (Matrix.single i j (1 : ℂ)) = 0 := by
    intro i j
    rw [single_eq_vecMulVec]
    exact hvw _ _
  rw [Matrix.matrix_eq_sum_single a]
  change F (∑ i, ∑ j, Matrix.single i j (a i j)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _hj
  change f (Matrix.single i j (a i j)) = 0
  rw [OperatorKO7.Meta.Physics.BuschGleasonFinite.single_eq_smul, hsmul, hsingle, mul_zero]

/-- Product ray tests determine a joint Hermitian matrix: complex local tomography. -/
theorem hermitian_eq_of_product_rays {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) {x y : Mat N}
    (hx : x.IsHermitian) (hy : y.IsHermitian)
    (h : ∀ (v : Fin n → ℂ) (w : Fin m → ℂ), v ≠ 0 → w ≠ 0 →
      (x * pairMatrix π (normRay v) (normRay w)).trace.re =
        (y * pairMatrix π (normRay v) (normRay w)).trace.re) : x = y := by
  set d := x - y with hd
  have hdh : d.IsHermitian := hx.sub hy
  have hA : ∀ (v : Fin n → ℂ) (w : Fin m → ℂ),
      (d * pairMatrix π (ray v) (ray w)).trace = 0 := by
    intro v w
    by_cases hv : v = 0
    · subst hv
      have hz : ray (0 : Fin n → ℂ) = 0 := by
        ext a b
        rw [ray_apply]
        simp
      rw [hz, show pairMatrix π (0 : Mat n) (ray w) = 0 by
        ext a b
        simp [pairMatrix], Matrix.mul_zero, Matrix.trace_zero]
    by_cases hw : w = 0
    · subst hw
      have hz : ray (0 : Fin m → ℂ) = 0 := by
        ext a b
        rw [ray_apply]
        simp
      rw [hz, show pairMatrix π (ray v) (0 : Mat m) = 0 by
        ext a b
        simp [pairMatrix], Matrix.mul_zero, Matrix.trace_zero]
    have hre : (d * pairMatrix π (normRay v) (normRay w)).trace.re = 0 := by
      rw [hd, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, h v w hv hw, sub_self]
    have him : (d * pairMatrix π (normRay v) (normRay w)).trace.im = 0 :=
      trace_mul_hermitian_im hdh
        (pairMatrix_hermitian π (normRay_posSemidef v).1 (normRay_posSemidef w).1)
    have hz : (d * pairMatrix π (normRay v) (normRay w)).trace = 0 := Complex.ext hre him
    rw [normRay, normRay, pairMatrix_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      at hz
    rcases mul_eq_zero.mp hz with hc | hc
    · exfalso
      rw [← Complex.ofReal_mul, Complex.ofReal_eq_zero] at hc
      exact (mul_ne_zero (inv_ne_zero (sqLength_pos hv).ne')
        (inv_ne_zero (sqLength_pos hw).ne')) hc
    · exact hc
  have hB : ∀ (a : Mat n) (w : Fin m → ℂ), (d * pairMatrix π a (ray w)).trace = 0 := by
    intro a w
    apply vanish_of_rays (fun a => (d * pairMatrix π a (ray w)).trace)
    · intro a b
      simp only [pairMatrix_add_left, Matrix.mul_add, Matrix.trace_add]
    · intro c a
      simp only [pairMatrix_smul_left, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    · intro v
      exact hA v w
  have hC : ∀ (a : Mat n) (b : Mat m), (d * pairMatrix π a b).trace = 0 := by
    intro a b
    apply vanish_of_rays (fun b => (d * pairMatrix π a b).trace)
    · intro b b'
      simp only [pairMatrix_add_right, Matrix.mul_add, Matrix.trace_add]
    · intro c b
      simp only [pairMatrix_smul_right, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    · intro w
      exact hB a w
  have hentry : ∀ i k j l, d (π.symm (i, k)) (π.symm (j, l)) = 0 := by
    intro i k j l
    have h0 := hC (Matrix.single j i 1) (Matrix.single l k 1)
    rw [trace_mul_pairMatrix_single] at h0
    exact h0
  have hd0 : d = 0 := by
    ext p q
    have := hentry (π p).1 (π p).2 (π q).1 (π q).2
    simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using this
  exact sub_eq_zero.mp hd0

section RealizationComposites

variable {D : OperationalData}

/-- Joint effects of a realization are paired Kronecker products. -/
theorem realization_joint_effect (r : QuantumRealization D) (A B : D.Obj) (e : D.Test A)
    (f : D.Test B) :
    (r.effects (D.tensor A B) (D.jointTest e f)).val =
      pairMatrix (r.pairIndex A B) (r.effects A e).val (r.effects B f).val := by
  ext i j
  exact r.product_effects A B e f i j

/-- The marginal of a realized joint state is the partial trace of its density matrix. -/
theorem realization_marginal (hL : OperationalLaws D) (r : QuantumRealization D) (A B : D.Obj)
    (s : D.State (D.tensor A B)) :
    (r.states A (D.marginal s)).val =
      traceRight (r.pairIndex A B) (r.states (D.tensor A B) s).val := by
  apply hermitian_eq_of_effect_tests (density_hermitian _)
    (traceRight_hermitian _ (density_hermitian _))
  intro e
  have h := hL.1.2.1 A B s ((r.effects A).symm e)
  rw [r.probabilities, r.probabilities, realization_joint_effect,
    realization_unit_effect hL r B, Equiv.apply_symm_apply] at h
  simp only [tr] at h
  rw [trace_mul_pairMatrix_one] at h
  exact h.symm

/-- Every lawful source with a quantum realization is locally tomographic. -/
theorem realization_localTomography (r : QuantumRealization D) : LocalTomography D := by
  intro A B s t h
  apply realization_states_val_injective r
  apply hermitian_eq_of_product_rays (r.pairIndex A B) (density_hermitian _)
    (density_hermitian _)
  intro v w hv hw
  have hst := h ((r.effects A).symm (rayEffect v hv)) ((r.effects B).symm (rayEffect w hw))
  rw [r.probabilities, r.probabilities, realization_joint_effect, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply] at hst
  exact hst

end RealizationComposites

end OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

/-! ## M5.3 nonvacuity, part 1: complete positivity and processes on matrices

These constructions prepare the finite quantum operational source. Complete positivity is
the specification's ancillary positivity; `cp_ampl` transfers it to every finite ancilla type.
A process carries its linear map and the normalized output assigned to each input density,
so normalized action composes exactly, including zero-weight outcomes.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

open scoped Kronecker

section QuantumModelInfrastructure

theorem quadratic_im_zero_of_hermitian {I : Type} [Fintype I] {a : Matrix I I ℂ}
    (ha : a.IsHermitian) (v : I → ℂ) : (star v ⬝ᵥ (a *ᵥ v)).im = 0 := by
  have h : star (star v ⬝ᵥ (a *ᵥ v)) = star v ⬝ᵥ (a *ᵥ v) := by
    rw [← Matrix.star_dotProduct (a *ᵥ v) v, Matrix.star_mulVec, ha.eq,
      ← Matrix.dotProduct_mulVec]
  have him := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

/-- The specification's general positivity agrees with native positivity on every index type. -/
theorem generalPSD_iff_posSemidef {I : Type} [Fintype I] (a : Matrix I I ℂ) :
    GeneralPSD a ↔ a.PosSemidef := by
  have hform : ∀ v : I → ℂ,
      (∑ i, ∑ j, star (v i) * a i j * v j) = star v ⬝ᵥ (a *ᵥ v) := by
    intro v
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  constructor
  · rintro ⟨hh, hp⟩
    have hherm : a.IsHermitian := by
      ext i j
      rw [Matrix.conjTranspose_apply]
      exact (hh i j).symm
    refine ⟨hherm, fun v => Complex.nonneg_iff.mpr
      ⟨?_, (quadratic_im_zero_of_hermitian hherm v).symm⟩⟩
    rw [← hform]
    exact hp v
  · intro ha
    refine ⟨fun i j => ?_, fun v => ?_⟩
    · have h := congrArg (fun b : Matrix I I ℂ => b i j) ha.1.eq
      simp only [Matrix.conjTranspose_apply] at h
      exact h.symm
    · rw [hform]
      exact (Complex.nonneg_iff.mp (ha.2 v)).1

/-- Ancillary action on an arbitrary finite ancilla type. -/
def ampl {n m : ℕ} (f : Mat n →ₗ[ℂ] Mat m) (I : Type) (X : Matrix (I × Fin n) (I × Fin n) ℂ) :
    Matrix (I × Fin m) (I × Fin m) ℂ :=
  fun p q => f (fun x y => X (p.1, x) (q.1, y)) p.2 q.2

/-- Complete positivity holds with every finite ancilla type, not only `Fin r`. -/
theorem cp_ampl {n m : ℕ} {f : Mat n →ₗ[ℂ] Mat m} (hf : CompletelyPositive f) (I : Type)
    [Fintype I] {X : Matrix (I × Fin n) (I × Fin n) ℂ} (hX : X.PosSemidef) :
    (ampl f I X).PosSemidef := by
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let σ : Fin (Fintype.card I) × Fin n ≃ I × Fin n := e.symm.prodCongr (Equiv.refl _)
  let τ : Fin (Fintype.card I) × Fin m ≃ I × Fin m := e.symm.prodCongr (Equiv.refl _)
  have hX' : (X.submatrix σ σ).PosSemidef := hX.submatrix σ
  have h := (generalPSD_iff_posSemidef _).mp
    (hf _ _ ((generalPSD_iff_posSemidef _).mpr hX'))
  have heq : amplify f (Fintype.card I) (X.submatrix σ σ) = (ampl f I X).submatrix τ τ := by
    ext p q
    rfl
  rw [heq] at h
  exact (Matrix.posSemidef_submatrix_equiv τ).mp h

/-- Complete positivity contains positivity. -/
theorem cp_positive {n m : ℕ} {f : Mat n →ₗ[ℂ] Mat m} (hf : CompletelyPositive f) {a : Mat n}
    (ha : a.PosSemidef) : (f a).PosSemidef := by
  have hX : (a.submatrix (Prod.snd : Unit × Fin n → Fin n) Prod.snd).PosSemidef :=
    ha.submatrix Prod.snd
  have h := (cp_ampl hf Unit hX).submatrix (fun i : Fin m => ((), i))
  have heq : (ampl f Unit (a.submatrix Prod.snd Prod.snd)).submatrix
      (fun i : Fin m => ((), i)) (fun i : Fin m => ((), i)) = f a := by
    ext i j
    rfl
  rw [heq] at h
  exact h

theorem trace_submatrix_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β)
    (x : Matrix β β ℂ) : (x.submatrix e e).trace = x.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun z => x z z)

theorem posSemidef_diag_nonneg {I : Type} [Fintype I] [DecidableEq I] {a : Matrix I I ℂ}
    (ha : a.PosSemidef) (i : I) : 0 ≤ a i i := by
  have h := ha.2 (Pi.single i 1)
  simpa only [Matrix.mulVec_single_one, ← Pi.single_star, star_one, single_dotProduct,
    one_mul, Matrix.col_apply] using h

theorem posSemidef_trace_re_nonneg {I : Type} [Fintype I] [DecidableEq I] {a : Matrix I I ℂ}
    (ha : a.PosSemidef) : 0 ≤ a.trace.re := by
  rw [Matrix.trace, Complex.re_sum]
  exact Finset.sum_nonneg (fun i _ => (Complex.nonneg_iff.mp (posSemidef_diag_nonneg ha i)).1)

/-- A positive matrix with zero trace is the zero matrix. -/
theorem posSemidef_eq_zero_of_trace_re {I : Type} [Fintype I] [DecidableEq I]
    {a : Matrix I I ℂ} (ha : a.PosSemidef) (h : a.trace.re = 0) : a = 0 := by
  rw [Matrix.trace, Complex.re_sum] at h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => (Complex.nonneg_iff.mp (posSemidef_diag_nonneg ha i)).1)).mp h
  have hdiag : ∀ i, a i i = 0 := by
    intro i
    have hn := Complex.nonneg_iff.mp (posSemidef_diag_nonneg ha i)
    apply Complex.ext
    · exact hz i (Finset.mem_univ i)
    · rw [Complex.zero_im]
      exact hn.2.symm
  ext k i
  exact Thermal.psd_column_zero ha i (hdiag i) k

/-- The trace of a positive matrix is the real number of its real part. -/
theorem posSemidef_trace_ofReal {I : Type} [Fintype I] {a : Matrix I I ℂ}
    (ha : a.PosSemidef) : a.trace = ((a.trace.re : ℝ) : ℂ) := by
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im]
    have h : star a.trace = a.trace := by
      rw [← Matrix.trace_conjTranspose, ha.1.eq]
    have him := congrArg Complex.im h
    rw [Complex.star_def, Complex.conj_im] at him
    linarith

/-! ### Paired products of positive matrices -/

theorem pairMatrix_eq_submatrix {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (a : Mat n)
    (b : Mat m) : pairMatrix π a b = (a ⊗ₖ b).submatrix π π := by
  ext i j
  rfl

theorem pairMatrix_posSemidef {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) {a : Mat n} {b : Mat m}
    (ha : a.PosSemidef) (hb : b.PosSemidef) : (pairMatrix π a b).PosSemidef := by
  rw [pairMatrix_eq_submatrix]
  exact (Thermal.tensor_posSemidef ha hb).submatrix π

theorem pairMatrix_trace {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (a : Mat n) (b : Mat m) :
    (pairMatrix π a b).trace = a.trace * b.trace := by
  rw [pairMatrix_eq_submatrix, trace_submatrix_equiv, Matrix.trace_kronecker]

theorem pairMatrix_mul {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (a c : Mat n) (b d : Mat m) :
    pairMatrix π a b * pairMatrix π c d = pairMatrix π (a * c) (b * d) := by
  ext i j
  simp only [Matrix.mul_apply, pairMatrix]
  rw [sum_pair π]
  simp only [Equiv.apply_symm_apply, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro y _hy
  ring

theorem pairMatrix_one {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) :
    pairMatrix π (1 : Mat n) (1 : Mat m) = 1 := by
  ext i j
  simp only [pairMatrix, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : π i ≠ π j := fun e => h (π.injective e)
    rw [if_neg h]
    by_cases h1 : (π i).1 = (π j).1
    · have h2 : (π i).2 ≠ (π j).2 := fun e2 => h' (Prod.ext h1 e2)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

theorem pairMatrix_sub_left {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (a a' : Mat n)
    (b : Mat m) : pairMatrix π (a - a') b = pairMatrix π a b - pairMatrix π a' b := by
  ext i j
  simp only [pairMatrix, Matrix.sub_apply, sub_mul]

theorem pairMatrix_sub_right {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (a : Mat n)
    (b b' : Mat m) : pairMatrix π a (b - b') = pairMatrix π a b - pairMatrix π a b' := by
  ext i j
  simp only [pairMatrix, Matrix.sub_apply, mul_sub]

/-- `1 - E ⊗ F` is the sum of the two positive pieces `(1 - E) ⊗ F` and `1 ⊗ (1 - F)`. -/
theorem one_sub_pairMatrix_posSemidef {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) {a : Mat n}
    {b : Mat m} (hb : b.PosSemidef) (ha' : (1 - a).PosSemidef) (hb' : (1 - b).PosSemidef) :
    (1 - pairMatrix π a b).PosSemidef := by
  have he : 1 - pairMatrix π a b = pairMatrix π (1 - a) b + pairMatrix π 1 (1 - b) := by
    rw [pairMatrix_sub_left, pairMatrix_sub_right, pairMatrix_one]
    abel
  rw [he]
  exact (pairMatrix_posSemidef π ha' hb).add (pairMatrix_posSemidef π Matrix.PosSemidef.one hb')

/-- Partial trace over the first factor of a paired joint index. -/
def traceLeft {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (x : Mat N) : Mat m :=
  fun k l => ∑ i, x (π.symm (i, k)) (π.symm (i, l))

theorem traceRight_eq_marginalLeft {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (x : Mat N) :
    traceRight π x = Thermal.marginalLeft (x.submatrix π.symm π.symm) := rfl

theorem traceLeft_eq_marginalRight {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (x : Mat N) :
    traceLeft π x = Thermal.marginalRight (x.submatrix π.symm π.symm) := rfl

theorem traceRight_posSemidef {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) {x : Mat N}
    (hx : x.PosSemidef) : (traceRight π x).PosSemidef := by
  rw [traceRight_eq_marginalLeft]
  exact Thermal.marginalLeft_posSemidef (hx.submatrix π.symm)

theorem traceLeft_posSemidef {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) {x : Mat N}
    (hx : x.PosSemidef) : (traceLeft π x).PosSemidef := by
  rw [traceLeft_eq_marginalRight]
  exact Thermal.marginalRight_posSemidef (hx.submatrix π.symm)

theorem traceRight_trace {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (x : Mat N) :
    (traceRight π x).trace = x.trace := by
  rw [traceRight_eq_marginalLeft, Thermal.marginalLeft_trace, trace_submatrix_equiv]

theorem traceLeft_trace {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (x : Mat N) :
    (traceLeft π x).trace = x.trace := by
  rw [traceLeft_eq_marginalRight, Thermal.marginalRight_trace, trace_submatrix_equiv]

/-- Testing a joint matrix with a second-factor effect reads its other partial trace. -/
theorem trace_mul_pairMatrix_one_left {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (x : Mat N)
    (b : Mat m) : (x * pairMatrix π 1 b).trace = (traceLeft π x * b).trace := by
  rw [trace_mul_pairMatrix]
  have hinner : ∀ i k, (∑ j, ∑ l, x (π.symm (i, k)) (π.symm (j, l)) *
      ((1 : Mat n) j i * b l k)) = ∑ l, x (π.symm (i, k)) (π.symm (i, l)) * b l k := by
    intro i k
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.one_apply_eq, one_mul]
    · intro j _hj hji
      apply Finset.sum_eq_zero
      intro l _hl
      rw [Matrix.one_apply_ne hji, zero_mul, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp only [hinner]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceLeft, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Finset.sum_comm]

/-! ### Processes of the finite quantum source -/

/-- A completely positive, trace-nonincreasing linear map with the normalized output assigned
to every input density; the output law ties the two together on every input. -/
structure QProc (n m : ℕ) where
  map : Mat n →ₗ[ℂ] Mat m
  cp : CompletelyPositive map
  tni : TraceNonIncreasing map
  out : Density n → Density m
  out_spec : ∀ ρ : Density n, map ρ.val = (((tr (map ρ.val)).re : ℝ) : ℂ) • (out ρ).val

theorem density_trace {n : ℕ} (ρ : Density n) : ρ.val.trace = 1 := ρ.property.2

theorem density_posSemidef {n : ℕ} (ρ : Density n) : ρ.val.PosSemidef :=
  (psd_iff_posSemidef _).mp ρ.property.1

theorem effect_posSemidef {n : ℕ} (e : Effect n) : e.val.PosSemidef :=
  (psd_iff_posSemidef _).mp e.property.1

theorem effect_compl_posSemidef {n : ℕ} (e : Effect n) : (1 - e.val).PosSemidef :=
  (psd_iff_posSemidef _).mp e.property.2

/-- The identity process. -/
def QProc.ident (n : ℕ) : QProc n n where
  map := LinearMap.id
  cp := by
    intro r a ha
    have heq : amplify (LinearMap.id : Mat n →ₗ[ℂ] Mat n) r a = a := by
      ext p q
      rfl
    rw [heq]
    exact ha
  tni := fun _ _ => le_rfl
  out := id
  out_spec ρ := by
    rw [LinearMap.id_apply, ρ.property.2, Complex.one_re, Complex.ofReal_one, one_smul]
    rfl

/-- Sequential composition: the maps compose and the normalized outputs compose. -/
def QProc.comp {n m k : ℕ} (g : QProc m k) (f : QProc n m) : QProc n k where
  map := g.map ∘ₗ f.map
  cp := by
    intro r a ha
    have heq : amplify (g.map ∘ₗ f.map) r a = amplify g.map r (amplify f.map r a) := rfl
    rw [heq]
    exact g.cp r _ (f.cp r a ha)
  tni := by
    intro a ha
    have hfa : PSD (f.map a) :=
      (psd_iff_posSemidef _).mpr (cp_positive f.cp ((psd_iff_posSemidef a).mp ha))
    exact (g.tni _ hfa).trans (f.tni a ha)
  out := fun ρ => g.out (f.out ρ)
  out_spec ρ := by
    have h1 := f.out_spec ρ
    have h2 := g.out_spec (f.out ρ)
    have hc : (g.map ∘ₗ f.map) ρ.val =
        (((tr (f.map ρ.val)).re * (tr (g.map (f.out ρ).val)).re : ℝ) : ℂ) •
          (g.out (f.out ρ)).val := by
      calc (g.map ∘ₗ f.map) ρ.val = g.map (f.map ρ.val) := rfl
        _ = g.map ((((tr (f.map ρ.val)).re : ℝ) : ℂ) • (f.out ρ).val) := congrArg g.map h1
        _ = (((tr (f.map ρ.val)).re : ℝ) : ℂ) • g.map (f.out ρ).val :=
          LinearMap.map_smul _ _ _
        _ = (((tr (f.map ρ.val)).re : ℝ) : ℂ) •
            ((((tr (g.map (f.out ρ).val)).re : ℝ) : ℂ) • (g.out (f.out ρ)).val) :=
          congrArg (fun z => (((tr (f.map ρ.val)).re : ℝ) : ℂ) • z) h2
        _ = _ := by rw [smul_smul, Complex.ofReal_mul]
    rw [hc]
    congr 1
    simp only [tr]
    rw [Matrix.trace_smul, density_trace, smul_eq_mul, mul_one, Complex.ofReal_re]

theorem pi_single_ne_zero {n : ℕ} (i : Fin n) : (Pi.single i (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
  intro h
  have hi := congrFun h i
  rw [Pi.single_eq_same, Pi.zero_apply] at hi
  exact one_ne_zero hi

/-- The basis density at the first index of a positive dimension. -/
def defaultDensity {m : ℕ} (hm : 0 < m) : Density m :=
  rayState (Pi.single ⟨0, hm⟩ 1) (pi_single_ne_zero _)

/-- The normalized output of a positive map; a zero-weight input receives the fixed basis
density, which carries zero weight in every statistic. -/
def normOut {n m : ℕ} (L : Mat n →ₗ[ℂ] Mat m) (hcp : CompletelyPositive L) (hm : 0 < m)
    (ρ : Density n) : Density m :=
  if h : 0 < (tr (L ρ.val)).re then
    ⟨((((tr (L ρ.val)).re)⁻¹ : ℝ) : ℂ) • L ρ.val,
      (psd_iff_posSemidef _).mpr (posSemidef_real_smul
        (cp_positive hcp (density_posSemidef ρ)) (inv_nonneg.mpr h.le)),
      by
        rw [tr, Matrix.trace_smul, posSemidef_trace_ofReal (cp_positive hcp (density_posSemidef ρ)),
          smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ h.ne', Complex.ofReal_one]⟩
  else defaultDensity hm

theorem normOut_spec {n m : ℕ} (L : Mat n →ₗ[ℂ] Mat m) (hcp : CompletelyPositive L)
    (hm : 0 < m) (ρ : Density n) :
    L ρ.val = (((tr (L ρ.val)).re : ℝ) : ℂ) • (normOut L hcp hm ρ).val := by
  by_cases h : 0 < (tr (L ρ.val)).re
  · rw [normOut, dif_pos h]
    change L ρ.val = (((tr (L ρ.val)).re : ℝ) : ℂ) •
      (((((tr (L ρ.val)).re)⁻¹ : ℝ) : ℂ) • L ρ.val)
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ h.ne', Complex.ofReal_one, one_smul]
  · have hpos := cp_positive hcp (density_posSemidef ρ)
    have hz : (tr (L ρ.val)).re = 0 :=
      le_antisymm (not_lt.mp h) (posSemidef_trace_re_nonneg hpos)
    rw [hz, Complex.ofReal_zero, zero_smul]
    exact posSemidef_eq_zero_of_trace_re hpos hz

/-- Every completely positive, trace-nonincreasing map into a positive dimension is a process. -/
def QProc.ofMap {n m : ℕ} (L : Mat n →ₗ[ℂ] Mat m) (hcp : CompletelyPositive L)
    (htni : TraceNonIncreasing L) (hm : 0 < m) : QProc n m where
  map := L
  cp := hcp
  tni := htni
  out := normOut L hcp hm
  out_spec := normOut_spec L hcp hm

end QuantumModelInfrastructure

end OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

/-! ## M5.3 nonvacuity, part 2: parallel composition of processes

`parMap f g` acts by `g` on the second tensor factor and then by `f` on the first. Its
ancillary amplification is, entry by entry, the amplification of `f` applied to a reindexed
amplification of `g`, so complete positivity of both factors gives complete positivity of the
parallel map. Trace nonincrease passes through the diagonal blocks of each factor.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

section Parallel

variable {n m k l N₁ N₂ : ℕ}

/-- The block of a joint matrix at first-factor indices `u, w`. -/
def blockL (πi : Fin N₁ ≃ Fin n × Fin k) (u w : Fin n) : Mat N₁ →ₗ[ℂ] Mat k where
  toFun x := fun p q => x (πi.symm (u, p)) (πi.symm (w, q))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The second factor transformed by `g` and read at entry `c, d`, as a first-factor matrix. -/
def innerL (g : Mat k →ₗ[ℂ] Mat l) (πi : Fin N₁ ≃ Fin n × Fin k) (c d : Fin l) :
    Mat N₁ →ₗ[ℂ] Mat n where
  toFun x := fun u w => g (blockL πi u w x) c d
  map_add' x y := by
    ext u w
    simp only [map_add, Matrix.add_apply]
  map_smul' z x := by
    ext u w
    simp only [map_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]

/-- Parallel composition of two linear maps on paired joint indices. -/
def parMap (f : Mat n →ₗ[ℂ] Mat m) (g : Mat k →ₗ[ℂ] Mat l) (πi : Fin N₁ ≃ Fin n × Fin k)
    (πo : Fin N₂ ≃ Fin m × Fin l) : Mat N₁ →ₗ[ℂ] Mat N₂ where
  toFun x := fun i j => f (innerL g πi (πo i).2 (πo j).2 x) (πo i).1 (πo j).1
  map_add' x y := by
    ext i j
    simp only [map_add, Matrix.add_apply]
  map_smul' z x := by
    ext i j
    simp only [map_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem blockL_pairMatrix (πi : Fin N₁ ≃ Fin n × Fin k) (a : Mat n) (b : Mat k) (u w : Fin n) :
    blockL πi u w (pairMatrix πi a b) = a u w • b := by
  ext p q
  simp only [blockL, LinearMap.coe_mk, AddHom.coe_mk, pairMatrix, Equiv.apply_symm_apply,
    Matrix.smul_apply, smul_eq_mul]

theorem innerL_pairMatrix (g : Mat k →ₗ[ℂ] Mat l) (πi : Fin N₁ ≃ Fin n × Fin k) (a : Mat n)
    (b : Mat k) (c d : Fin l) : innerL g πi c d (pairMatrix πi a b) = g b c d • a := by
  ext u w
  simp only [innerL, LinearMap.coe_mk, AddHom.coe_mk, blockL_pairMatrix, map_smul,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- On paired products the parallel map is the paired product of the two images. -/
theorem parMap_pairMatrix (f : Mat n →ₗ[ℂ] Mat m) (g : Mat k →ₗ[ℂ] Mat l)
    (πi : Fin N₁ ≃ Fin n × Fin k) (πo : Fin N₂ ≃ Fin m × Fin l) (a : Mat n) (b : Mat k) :
    parMap f g πi πo (pairMatrix πi a b) = pairMatrix πo (f a) (g b) := by
  ext i j
  simp only [parMap, LinearMap.coe_mk, AddHom.coe_mk, innerL_pairMatrix, map_smul,
    Matrix.smul_apply, smul_eq_mul, pairMatrix]
  ring

theorem parMap_cp {f : Mat n →ₗ[ℂ] Mat m} {g : Mat k →ₗ[ℂ] Mat l} (hfc : CompletelyPositive f)
    (hgc : CompletelyPositive g) (πi : Fin N₁ ≃ Fin n × Fin k) (πo : Fin N₂ ≃ Fin m × Fin l) :
    CompletelyPositive (parMap f g πi πo) := by
  intro r X hX
  have hXp := (generalPSD_iff_posSemidef X).mp hX
  let α : (Fin r × Fin n) × Fin k → Fin r × Fin N₁ := fun z => (z.1.1, πi.symm (z.1.2, z.2))
  let β : (Fin r × Fin l) × Fin n → (Fin r × Fin n) × Fin l := fun z => ((z.1.1, z.2), z.1.2)
  let σ : Fin r × Fin N₂ → (Fin r × Fin l) × Fin m := fun z => ((z.1, (πo z.2).2), (πo z.2).1)
  have hZ : (ampl f (Fin r × Fin l)
      ((ampl g (Fin r × Fin n) (X.submatrix α α)).submatrix β β)).PosSemidef :=
    cp_ampl hfc _ ((cp_ampl hgc _ (hXp.submatrix α)).submatrix β)
  have heq : amplify (parMap f g πi πo) r X = (ampl f (Fin r × Fin l)
      ((ampl g (Fin r × Fin n) (X.submatrix α α)).submatrix β β)).submatrix σ σ := by
    ext p q
    rfl
  rw [heq]
  exact (generalPSD_iff_posSemidef _).mpr (hZ.submatrix σ)

theorem parMap_tni {f : Mat n →ₗ[ℂ] Mat m} {g : Mat k →ₗ[ℂ] Mat l}
    (hft : TraceNonIncreasing f) (hgc : CompletelyPositive g) (hgt : TraceNonIncreasing g)
    (πi : Fin N₁ ≃ Fin n × Fin k) (πo : Fin N₂ ≃ Fin m × Fin l) :
    TraceNonIncreasing (parMap f g πi πo) := by
  intro x hx
  have hxp : x.PosSemidef := (psd_iff_posSemidef x).mp hx
  have hX' : (x.submatrix πi.symm πi.symm).PosSemidef := hxp.submatrix _
  have hY : (ampl g (Fin n) (x.submatrix πi.symm πi.symm)).PosSemidef := cp_ampl hgc (Fin n) hX'
  have hM : ∀ c : Fin l, (innerL g πi c c x).PosSemidef := by
    intro c
    exact hY.submatrix (fun u : Fin n => (u, c))
  have hB : ∀ u : Fin n, (blockL πi u u x).PosSemidef := by
    intro u
    exact hX'.submatrix (fun p : Fin k => (u, p))
  have htr1 : (parMap f g πi πo x).trace = ∑ c, (f (innerL g πi c c x)).trace := by
    simp only [Matrix.trace, Matrix.diag]
    rw [sum_pair πo]
    simp only [parMap, LinearMap.coe_mk, AddHom.coe_mk, Equiv.apply_symm_apply]
    exact Finset.sum_comm
  have htr2 : (∑ c, (innerL g πi c c x).trace) = ∑ u, (g (blockL πi u u x)).trace := by
    simp only [Matrix.trace, Matrix.diag, innerL, LinearMap.coe_mk, AddHom.coe_mk]
    exact Finset.sum_comm
  have htr3 : (∑ u, (blockL πi u u x).trace) = x.trace := by
    simp only [Matrix.trace, Matrix.diag, blockL, LinearMap.coe_mk, AddHom.coe_mk]
    exact (sum_pair πi (fun p => x p p)).symm
  change (parMap f g πi πo x).trace.re ≤ x.trace.re
  rw [htr1, ← htr3, Complex.re_sum, Complex.re_sum]
  calc ∑ c, (f (innerL g πi c c x)).trace.re ≤ ∑ c, (innerL g πi c c x).trace.re :=
        Finset.sum_le_sum (fun c _ => hft _ ((psd_iff_posSemidef _).mpr (hM c)))
    _ = ∑ u, (g (blockL πi u u x)).trace.re := by
        rw [← Complex.re_sum, htr2, Complex.re_sum]
    _ ≤ ∑ u, (blockL πi u u x).trace.re :=
        Finset.sum_le_sum (fun u _ => hgt _ ((psd_iff_posSemidef _).mpr (hB u)))

/-- Parallel composition of two processes into a positive output dimension. -/
def QProc.par (f : QProc n m) (g : QProc k l) (πi : Fin N₁ ≃ Fin n × Fin k)
    (πo : Fin N₂ ≃ Fin m × Fin l) (h : 0 < N₂) : QProc N₁ N₂ :=
  QProc.ofMap (parMap f.map g.map πi πo) (parMap_cp f.cp g.cp πi πo)
    (parMap_tni f.tni g.cp g.tni πi πo) h

end Parallel

end OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

/-! ## M5.3 nonvacuity, part 3: the finite quantum operational source

`quantumData` has one system for every positive dimension. Its states are density matrices,
its tests are effects, its processes are completely positive trace-nonincreasing maps with
their normalized outputs, joint systems use the standard index pairing, marginals are
partial traces and conditioning on an effect `E` uses `sqrt E ⊗ 1` on both sides. Every law of
`OperationalLaws` is proved for it, together with causality and two distinct pure states.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

section QuantumModel

theorem density_tr {n : ℕ} (ρ : Density n) : tr ρ.val = 1 := ρ.property.2

/-- Systems of the finite quantum source: the positive dimensions. -/
abbrev QSys := {n : ℕ // 0 < n}

/-- The joint system of two finite quantum systems. -/
def qtensor (A B : QSys) : QSys := ⟨A.1 * B.1, Nat.mul_pos A.2 B.2⟩

/-- The standard pairing of the joint index. -/
def qpair (A B : QSys) : Fin (qtensor A B).1 ≃ Fin A.1 × Fin B.1 := finProdFinEquiv.symm

/-- Convex mixing of two densities; parameters outside the unit interval return the first. -/
def densityMix {n : ℕ} (p : ℝ) (s t : Density n) : Density n :=
  if h : 0 ≤ p ∧ p ≤ 1 then
    ⟨(p : ℂ) • s.val + ((1 - p : ℝ) : ℂ) • t.val,
      (psd_iff_posSemidef _).mpr ((posSemidef_real_smul (density_posSemidef s) h.1).add
        (posSemidef_real_smul (density_posSemidef t) (sub_nonneg.mpr h.2))),
      by
        rw [tr, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, density_trace,
          density_trace, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
        push_cast
        ring⟩
  else s

theorem densityMix_val {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s t : Density n) :
    (densityMix p s t).val = (p : ℂ) • s.val + ((1 - p : ℝ) : ℂ) • t.val := by
  rw [densityMix, dif_pos ⟨hp0, hp1⟩]

/-- The paired product of two densities. -/
def pairState {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (s : Density n) (t : Density m) :
    Density N :=
  ⟨pairMatrix π s.val t.val,
    (psd_iff_posSemidef _).mpr (pairMatrix_posSemidef π (density_posSemidef s)
      (density_posSemidef t)),
    by rw [tr, pairMatrix_trace, density_trace, density_trace, mul_one]⟩

/-- The paired product of two effects. -/
def pairEffect {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (e : Effect n) (f : Effect m) :
    Effect N :=
  ⟨pairMatrix π e.val f.val,
    (psd_iff_posSemidef _).mpr (pairMatrix_posSemidef π (effect_posSemidef e)
      (effect_posSemidef f)),
    (psd_iff_posSemidef _).mpr (one_sub_pairMatrix_posSemidef π (effect_posSemidef f)
      (effect_compl_posSemidef e) (effect_compl_posSemidef f))⟩

/-- The first-factor marginal of a joint density. -/
def marginalState {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (s : Density N) : Density n :=
  ⟨traceRight π s.val, (psd_iff_posSemidef _).mpr (traceRight_posSemidef π (density_posSemidef s)),
    by rw [tr, traceRight_trace, density_trace]⟩

/-- The unnormalized conditional matrix of the second factor after the effect `e`. -/
def condMat {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (e : Effect n) (s : Density N) : Mat m :=
  traceLeft π (pairMatrix π (effect_posSemidef e).sqrt 1 * s.val *
    pairMatrix π (effect_posSemidef e).sqrt 1)

theorem condMat_posSemidef {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (e : Effect n)
    (s : Density N) : (condMat π e s).PosSemidef := by
  have hP : (pairMatrix π (effect_posSemidef e).sqrt (1 : Mat m)).IsHermitian :=
    pairMatrix_hermitian π (effect_posSemidef e).posSemidef_sqrt.1 Matrix.isHermitian_one
  have h := (density_posSemidef s).mul_mul_conjTranspose_same
    (pairMatrix π (effect_posSemidef e).sqrt (1 : Mat m))
  rw [hP.eq] at h
  exact traceLeft_posSemidef π h

/-- Testing the conditional matrix with `F` reads the joint statistic of `E ⊗ F`. -/
theorem condMat_trace_mul {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (e : Effect n)
    (s : Density N) (F : Mat m) :
    (condMat π e s * F).trace = (s.val * pairMatrix π e.val F).trace := by
  rw [condMat, ← trace_mul_pairMatrix_one_left]
  set P := pairMatrix π (effect_posSemidef e).sqrt (1 : Mat m)
  have hPQP : P * pairMatrix π 1 F * P = pairMatrix π e.val F := by
    rw [pairMatrix_mul, pairMatrix_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one,
      (effect_posSemidef e).sqrt_mul_self]
  calc (P * s.val * P * pairMatrix π 1 F).trace
      = ((P * s.val) * (P * pairMatrix π 1 F)).trace := by rw [Matrix.mul_assoc]
    _ = ((P * pairMatrix π 1 F) * (P * s.val)).trace := Matrix.trace_mul_comm _ _
    _ = ((P * pairMatrix π 1 F * P) * s.val).trace := by
      rw [Matrix.mul_assoc (P * pairMatrix π 1 F) P s.val]
    _ = (s.val * (P * pairMatrix π 1 F * P)).trace := Matrix.trace_mul_comm _ _
    _ = (s.val * pairMatrix π e.val F).trace := by rw [hPQP]

/-- Conditioning on an effect: defined exactly at positive probability. -/
def conditionState {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (e : Effect n) (s : Density N) :
    Option (Density m) :=
  if h : 0 < (tr (s.val * pairMatrix π e.val 1)).re then
    some ⟨((((tr (s.val * pairMatrix π e.val 1)).re)⁻¹ : ℝ) : ℂ) • condMat π e s,
      (psd_iff_posSemidef _).mpr (posSemidef_real_smul (condMat_posSemidef π e s)
        (inv_nonneg.mpr h.le)),
      by
        have ht := condMat_trace_mul π e s 1
        rw [Matrix.mul_one] at ht
        have hreal : (s.val * pairMatrix π e.val 1).trace =
            (((s.val * pairMatrix π e.val 1).trace.re : ℝ) : ℂ) :=
          Complex.ext rfl (by
            rw [Complex.ofReal_im]
            exact trace_mul_hermitian_im (density_hermitian s)
              (pairMatrix_hermitian π (effect_hermitian e) Matrix.isHermitian_one))
        rw [tr, Matrix.trace_smul, ht, hreal, smul_eq_mul, ← Complex.ofReal_mul]
        change ((((s.val * pairMatrix π e.val 1).trace.re)⁻¹ *
          (s.val * pairMatrix π e.val 1).trace.re : ℝ) : ℂ) = 1
        rw [inv_mul_cancel₀ h.ne', Complex.ofReal_one]⟩
  else none

/-- The finite quantum operational source. -/
def quantumData : OperationalData where
  Obj := QSys
  State A := Density A.1
  Test A := Effect A.1
  Process A B := QProc A.1 B.1
  tensor := qtensor
  prob e s := (tr (s.val * e.val)).re
  mix p s t := densityMix p s t
  act f s := f.out s
  weight f s := (tr (f.map s.val)).re
  ident A := QProc.ident A.1
  compose g f := QProc.comp g f
  unitTest A := unitEffect A.1
  deterministicTest e := e.val = 1
  jointTest := fun {A B} e f => pairEffect (qpair A B) e f
  productState := fun {A B} s t => pairState (qpair A B) s t
  parallel := fun {A B C E} f g => QProc.par f g (qpair A C) (qpair B E) (qtensor B E).2
  marginal := fun {A B} s => marginalState (qpair A B) s
  actRight := fun {A B} u s =>
    (QProc.par (QProc.ident A.1) u (qpair A B) (qpair A B) (qtensor A B).2).out s
  condition := fun {A B} e s => conditionState (qpair A B) e s

theorem qprob_mem_unitInterval {n : ℕ} (ρ : Density n) (e : Effect n) :
    0 ≤ (tr (ρ.val * e.val)).re ∧ (tr (ρ.val * e.val)).re ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := OperatorKO7.Meta.Physics.BuschGleasonFinite.bornMeasure_mem_unitInterval
    (⟨density_posSemidef ρ, density_trace ρ⟩ :
      OperatorKO7.Meta.Physics.BuschGleasonFinite.IsDensity ρ.val)
    (⟨effect_posSemidef e, effect_compl_posSemidef e⟩ :
      OperatorKO7.Meta.Physics.BuschGleasonFinite.IsEffect e.val)
  refine ⟨(Complex.nonneg_iff.mp hlo).1, ?_⟩
  have h := (Complex.nonneg_iff.mp (sub_nonneg.mpr hhi)).1
  change 0 ≤ (1 - tr (ρ.val * e.val)).re at h
  simp only [Complex.sub_re, Complex.one_re] at h
  linarith

/-- The composite map on a density is the product of the two weights times the final output. -/
theorem QProc.comp_map_density {n m k : ℕ} (g : QProc m k) (f : QProc n m) (ρ : Density n) :
    (QProc.comp g f).map ρ.val =
      (((tr (f.map ρ.val)).re * (tr (g.map (f.out ρ).val)).re : ℝ) : ℂ) •
        (g.out (f.out ρ)).val := by
  calc (QProc.comp g f).map ρ.val = g.map (f.map ρ.val) := rfl
    _ = g.map ((((tr (f.map ρ.val)).re : ℝ) : ℂ) • (f.out ρ).val) := congrArg g.map (f.out_spec ρ)
    _ = (((tr (f.map ρ.val)).re : ℝ) : ℂ) • g.map (f.out ρ).val := LinearMap.map_smul _ _ _
    _ = (((tr (f.map ρ.val)).re : ℝ) : ℂ) •
        ((((tr (g.map (f.out ρ).val)).re : ℝ) : ℂ) • (g.out (f.out ρ)).val) :=
      congrArg (fun z => (((tr (f.map ρ.val)).re : ℝ) : ℂ) • z) (g.out_spec (f.out ρ))
    _ = _ := by rw [smul_smul, Complex.ofReal_mul]

/-- The three conditioning laws for paired joint densities. -/
theorem conditionState_laws {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (s : Density N)
    (e : Effect n) :
    (conditionState π e s = none ↔ (tr (s.val * (pairEffect π e (unitEffect m)).val)).re = 0) ∧
    (0 < (tr (s.val * (pairEffect π e (unitEffect m)).val)).re →
      ∃ t, conditionState π e s = some t) ∧
    ∀ t, conditionState π e s = some t →
      0 < (tr (s.val * (pairEffect π e (unitEffect m)).val)).re ∧
      ∀ f : Effect m, (tr (s.val * (pairEffect π e (unitEffect m)).val)).re *
        (tr (t.val * f.val)).re = (tr (s.val * (pairEffect π e f).val)).re := by
  have hnn : 0 ≤ (tr (s.val * (pairEffect π e (unitEffect m)).val)).re :=
    (qprob_mem_unitInterval s (pairEffect π e (unitEffect m))).1
  change 0 ≤ (tr (s.val * pairMatrix π e.val 1)).re at hnn
  change (conditionState π e s = none ↔ (tr (s.val * pairMatrix π e.val 1)).re = 0) ∧
    (0 < (tr (s.val * pairMatrix π e.val 1)).re → ∃ t, conditionState π e s = some t) ∧
    ∀ t, conditionState π e s = some t → 0 < (tr (s.val * pairMatrix π e.val 1)).re ∧
      ∀ f : Effect m, (tr (s.val * pairMatrix π e.val 1)).re * (tr (t.val * f.val)).re =
        (tr (s.val * pairMatrix π e.val f.val)).re
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : 0 < (tr (s.val * pairMatrix π e.val 1)).re
    · rw [conditionState, dif_pos h]
      exact ⟨fun hc => Option.noConfusion hc, fun hz => absurd hz h.ne'⟩
    · rw [conditionState, dif_neg h]
      exact ⟨fun _ => le_antisymm (not_lt.mp h) hnn, fun _ => rfl⟩
  · intro h
    rw [conditionState, dif_pos h]
    exact ⟨_, rfl⟩
  · intro t ht
    by_cases h : 0 < (tr (s.val * pairMatrix π e.val 1)).re
    · rw [conditionState, dif_pos h] at ht
      refine ⟨h, fun f => ?_⟩
      rw [← Option.some_inj.mp ht]
      change (tr (s.val * pairMatrix π e.val 1)).re *
        (tr ((((((tr (s.val * pairMatrix π e.val 1)).re)⁻¹ : ℝ) : ℂ) •
          condMat π e s) * f.val)).re = _
      simp only [tr]
      rw [Matrix.smul_mul, Matrix.trace_smul, condMat_trace_mul, smul_eq_mul,
        Complex.re_ofReal_mul, ← mul_assoc, mul_inv_cancel₀ h.ne', one_mul]
    · rw [conditionState, dif_neg h] at ht
      exact Option.noConfusion ht

theorem marginalState_law {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (s : Density N)
    (e : Effect n) : (tr (s.val * (pairEffect π e (unitEffect m)).val)).re =
      (tr ((marginalState π s).val * e.val)).re := by
  change (tr (s.val * pairMatrix π e.val 1)).re = (tr (traceRight π s.val * e.val)).re
  rw [tr, tr, trace_mul_pairMatrix_one]

theorem pairState_law {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (s : Density n)
    (t : Density m) (e : Effect n) (f : Effect m) :
    (tr ((pairState π s t).val * (pairEffect π e f).val)).re =
      (tr (s.val * e.val)).re * (tr (t.val * f.val)).re := by
  change (tr (pairMatrix π s.val t.val * pairMatrix π e.val f.val)).re = _
  rw [tr, tr, tr, pairMatrix_mul, pairMatrix_trace, Complex.mul_re,
    trace_mul_hermitian_im (density_hermitian s) (effect_hermitian e), zero_mul, sub_zero]

theorem quantumData_conditioningLaws : ConditioningLaws quantumData :=
  ⟨fun A B s e => conditionState_laws (qpair A B) s e,
    fun A B s e => marginalState_law (qpair A B) s e,
    fun A B s t e f => pairState_law (qpair A B) s t e f⟩

theorem quantumData_operationalLaws : OperationalLaws quantumData := by
  refine ⟨quantumData_conditioningLaws, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A s e
    exact qprob_mem_unitInterval s e
  · intro A s
    show (tr (s.val * 1)).re = 1
    rw [Matrix.mul_one, density_tr, Complex.one_re]
  · intro A s t h
    exact density_ext_of_effects s t h
  · intro A s t p hp0 hp1 e
    show (tr ((densityMix p s t).val * e.val)).re =
      p * (tr (s.val * e.val)).re + (1 - p) * (tr (t.val * e.val)).re
    rw [densityMix_val hp0 hp1]
    simp only [tr, Matrix.add_mul, Matrix.trace_add, Complex.add_re, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  · intro A s
    rfl
  · intro A B C f g s
    rfl
  · intro A B f s
    refine ⟨posSemidef_trace_re_nonneg (cp_positive f.cp (density_posSemidef s)), ?_⟩
    have h := f.tni s.val s.property.1
    rw [density_tr, Complex.one_re] at h
    exact h
  · intro A B C f g s
    show (tr ((QProc.comp g f).map s.val)).re =
      (tr (f.map s.val)).re * (tr (g.map (f.out s).val)).re
    rw [QProc.comp_map_density, tr, Matrix.trace_smul, density_trace, smul_eq_mul, mul_one,
      Complex.ofReal_re]

theorem quantumData_causality : Causality quantumData := by
  intro A e he s
  show (tr (s.val * e.val)).re = (tr (s.val * 1)).re
  rw [show e.val = 1 from he]

/-! ### Basis states are pure -/

theorem sqLength_single {n : ℕ} (i : Fin n) : sqLength (Pi.single i (1 : ℂ)) = 1 := by
  simp [sqLength, dotProduct, Pi.single_apply]

theorem normRay_single {n : ℕ} (i : Fin n) :
    normRay (Pi.single i (1 : ℂ)) = Matrix.single i i 1 := by
  ext r c
  rw [normRay, sqLength_single, inv_one, Complex.ofReal_one, one_smul, ray_apply,
    single_one_apply, Pi.single_apply, Pi.single_apply]
  by_cases hr : r = i
  · subst hr
    by_cases hc : c = r
    · subst hc
      simp
    · simp [hc, Ne.symm hc]
  · simp [hr, Ne.symm hr]

/-- A density whose diagonal vanishes away from `i` is the basis projector at `i`. -/
theorem density_eq_single_of_diag {n : ℕ} (a : Density n) (i : Fin n)
    (hd : ∀ j, j ≠ i → a.val j j = 0) : a.val = Matrix.single i i 1 := by
  have hpsd := density_posSemidef a
  have hcol : ∀ j, j ≠ i → ∀ r, a.val r j = 0 :=
    fun j hj => Thermal.psd_column_zero hpsd j (hd j hj)
  have hii : a.val i i = 1 := by
    have ht := density_trace a
    rw [Matrix.trace, Finset.sum_eq_single i] at ht
    · exact ht
    · intro j _hj hji
      exact hd j hji
    · intro h
      exact absurd (Finset.mem_univ i) h
  ext r c
  rw [single_one_apply]
  by_cases hc : c = i
  · subst hc
    by_cases hr : r = c
    · subst hr
      rw [hii, if_pos ⟨rfl, rfl⟩]
    · have hrc : a.val r c = star (a.val c r) := by
        rw [← Matrix.conjTranspose_apply, (density_hermitian a).eq]
      rw [hrc, hcol r hr c, star_zero, if_neg (fun h => hr h.1.symm)]
  · rw [hcol c hc r, if_neg (fun h => hc h.2.symm)]

/-- A positive real combination with a vanishing entry forces both diagonal entries to vanish. -/
theorem diag_zero_of_mix {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (a b : Density n)
    (j : Fin n) (h : (p : ℂ) * a.val j j + ((1 - p : ℝ) : ℂ) * b.val j j = 0) :
    a.val j j = 0 ∧ b.val j j = 0 := by
  have ha := Complex.nonneg_iff.mp (posSemidef_diag_nonneg (density_posSemidef a) j)
  have hb := Complex.nonneg_iff.mp (posSemidef_diag_nonneg (density_posSemidef b) j)
  have hre := congrArg Complex.re h
  rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.zero_re] at hre
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have har : (a.val j j).re = 0 := by nlinarith [mul_nonneg hp0.le ha.1, mul_nonneg hq.le hb.1]
  have hbr : (b.val j j).re = 0 := by nlinarith [mul_nonneg hp0.le ha.1, mul_nonneg hq.le hb.1]
  exact ⟨Complex.ext har (by rw [Complex.zero_im]; exact ha.2.symm),
    Complex.ext hbr (by rw [Complex.zero_im]; exact hb.2.symm)⟩

/-- The basis density at index `i`. -/
def basisState (A : QSys) (i : Fin A.1) : quantumData.State A :=
  rayState (Pi.single i 1) (pi_single_ne_zero i)

theorem basisState_val (A : QSys) (i : Fin A.1) :
    (basisState A i : Density A.1).val = Matrix.single i i 1 :=
  normRay_single i

/-- Every basis density is a pure state of the quantum source. -/
theorem basisState_pure (A : QSys) (i : Fin A.1) : Pure quantumData (basisState A i) := by
  intro p a b hp0 hp1 hmix
  have hm : (p : ℂ) • (a : Density A.1).val + ((1 - p : ℝ) : ℂ) • (b : Density A.1).val =
      Matrix.single i i 1 := by
    rw [← densityMix_val hp0.le hp1.le, ← basisState_val A i]
    exact congrArg Subtype.val hmix
  have hd : ∀ j, j ≠ i → (a : Density A.1).val j j = 0 ∧ (b : Density A.1).val j j = 0 := by
    intro j hj
    apply diag_zero_of_mix hp0 hp1
    have he := congrArg (fun x : Mat A.1 => x j j) hm
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at he
    rw [he, single_one_apply, if_neg (fun h => hj h.1.symm)]
  constructor
  · apply Subtype.ext
    rw [basisState_val]
    exact density_eq_single_of_diag a i (fun j hj => (hd j hj).1)
  · apply Subtype.ext
    rw [basisState_val]
    exact density_eq_single_of_diag b i (fun j hj => (hd j hj).2)

/-- The qubit system of the quantum source. -/
def qubit : QSys := ⟨2, by norm_num⟩

/-- The two basis indices of the qubit. -/
def qubitZero : Fin qubit.1 := ⟨0, by show 0 < 2; norm_num⟩
def qubitOne : Fin qubit.1 := ⟨1, by show 1 < 2; norm_num⟩

/-- The quantum source has two distinct pure states on the qubit. -/
theorem quantumData_two_pure_states :
    ∃ (A : quantumData.Obj) (s t : quantumData.State A), s ≠ t ∧
      Pure quantumData s ∧ Pure quantumData t := by
  refine ⟨qubit, basisState qubit qubitZero, basisState qubit qubitOne, ?_,
    basisState_pure qubit qubitZero, basisState_pure qubit qubitOne⟩
  intro h
  have he := congrArg (fun s : Density qubit.1 => s.val qubitZero qubitZero) h
  norm_num [basisState_val, single_one_apply, qubitZero, qubitOne] at he

end QuantumModel

end OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

/-! ## M5.3 nonvacuity, part 4: the quantum source carries a full quantum realization

Every field of `QuantumRealization` is constructed for `quantumData`: bijections onto all
densities and all effects, the Born rule, completely positive trace-nonincreasing maps with
the weighted source action, composition, fullness over every such map, faithfulness against
every ancilla, and the product laws on the standard pairing. Faithfulness uses the
one-dimensional ancilla and the fact that densities span every matrix.
-/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

section QuantumModelRealization

/-- Weight times post-state statistic equals the statistic of the unnormalized output. -/
theorem QProc.weight_mul_prob {n m : ℕ} (P : QProc n m) (ρ : Density n) (E : Mat m) :
    (tr (P.map ρ.val)).re * (tr ((P.out ρ).val * E)).re = (tr (P.map ρ.val * E)).re := by
  have h := P.out_spec ρ
  calc (tr (P.map ρ.val)).re * (tr ((P.out ρ).val * E)).re
      = (((((tr (P.map ρ.val)).re : ℝ) : ℂ) • (P.out ρ).val * E).trace).re := by
        rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    _ = (tr (P.map ρ.val * E)).re := by rw [← h]

theorem ray_eq_smul_normRay {n : ℕ} {v : Fin n → ℂ} (hv : v ≠ 0) :
    ray v = ((sqLength v : ℝ) : ℂ) • normRay v := by
  rw [normRay, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (sqLength_pos hv).ne',
    Complex.ofReal_one, one_smul]

/-- Linear maps that agree on every density agree on every matrix. -/
theorem linearMap_eq_of_densities {n m : ℕ} (f g : Mat n →ₗ[ℂ] Mat m)
    (h : ∀ ρ : Density n, f ρ.val = g ρ.val) : f = g := by
  apply LinearMap.ext
  intro x
  ext i j
  have hz := vanish_of_rays (fun y : Mat n => f y i j - g y i j)
    (fun a b => by simp only [map_add, Matrix.add_apply]; ring)
    (fun c a => by simp only [map_smul, Matrix.smul_apply, smul_eq_mul]; ring)
    (fun v => by
      by_cases hv : v = 0
      · subst hv
        have h0 : ray (0 : Fin n → ℂ) = 0 := by
          ext a b
          rw [ray_apply]
          simp
        simp only [h0, map_zero, Matrix.zero_apply, sub_self]
      · have hr := h (rayState v hv)
        change f (normRay v) = g (normRay v) at hr
        simp only [ray_eq_smul_normRay hv, map_smul, Matrix.smul_apply, smul_eq_mul, hr,
          sub_self])
    x
  exact sub_eq_zero.mp hz

/-- Statistics of the parallel process with the one-dimensional ancilla determine the map. -/
theorem map_eq_of_par_tests {n m N₁ N₂ : ℕ} {f g : Mat n →ₗ[ℂ] Mat m}
    (hfc : CompletelyPositive f) (hgc : CompletelyPositive g)
    (πi : Fin N₁ ≃ Fin n × Fin 1) (πo : Fin N₂ ≃ Fin m × Fin 1)
    (h : ∀ (s : Density N₁) (E : Effect N₂),
      (tr (parMap f LinearMap.id πi πo s.val * E.val)).re =
        (tr (parMap g LinearMap.id πi πo s.val * E.val)).re) : f = g := by
  apply linearMap_eq_of_densities
  intro ρ
  let σ : Density 1 := defaultDensity one_pos
  apply hermitian_eq_of_effect_tests (cp_positive hfc (density_posSemidef ρ)).1
    (cp_positive hgc (density_posSemidef ρ)).1
  intro E
  have hE := h (pairState πi ρ σ) (pairEffect πo E (unitEffect 1))
  change (tr (parMap f LinearMap.id πi πo (pairMatrix πi ρ.val σ.val) *
      pairMatrix πo E.val 1)).re =
    (tr (parMap g LinearMap.id πi πo (pairMatrix πi ρ.val σ.val) *
      pairMatrix πo E.val 1)).re at hE
  rw [parMap_pairMatrix, parMap_pairMatrix, LinearMap.id_apply, pairMatrix_mul, pairMatrix_mul,
    tr, tr, pairMatrix_trace, pairMatrix_trace, Matrix.mul_one, density_trace, mul_one,
    mul_one] at hE
  exact hE

theorem par_faithful_forward {n m k N₁ N₂ : ℕ} {f g : QProc n m} (P : QProc k k)
    (πi : Fin N₁ ≃ Fin n × Fin k) (πo : Fin N₂ ≃ Fin m × Fin k) (h : 0 < N₂)
    (hfg : f.map = g.map) (s : Density N₁) (E : Effect N₂) :
    (tr ((QProc.par f P πi πo h).map s.val)).re *
        (tr (((QProc.par f P πi πo h).out s).val * E.val)).re =
      (tr ((QProc.par g P πi πo h).map s.val)).re *
        (tr (((QProc.par g P πi πo h).out s).val * E.val)).re := by
  rw [QProc.weight_mul_prob, QProc.weight_mul_prob]
  change (tr (parMap f.map P.map πi πo s.val * E.val)).re =
    (tr (parMap g.map P.map πi πo s.val * E.val)).re
  rw [hfg]

/-- The trivial system of the quantum source. -/
def qunit : QSys := ⟨1, one_pos⟩

theorem quantumData_faithful {A B : quantumData.Obj} (f g : quantumData.Process A B) :
    f.map = g.map ↔ ProcessEquivalent quantumData f g := by
  constructor
  · intro h C s e
    exact par_faithful_forward (QProc.ident C.1) (qpair A C) (qpair B C) (qtensor B C).2 h s e
  · intro h
    apply map_eq_of_par_tests f.cp g.cp (qpair A qunit) (qpair B qunit)
    intro s E
    have hs := h qunit s E
    change (tr ((QProc.par f (QProc.ident 1) (qpair A qunit) (qpair B qunit)
        (qtensor B qunit).2).map s.val)).re *
        (tr (((QProc.par f (QProc.ident 1) (qpair A qunit) (qpair B qunit)
          (qtensor B qunit).2).out s).val * E.val)).re =
      (tr ((QProc.par g (QProc.ident 1) (qpair A qunit) (qpair B qunit)
        (qtensor B qunit).2).map s.val)).re *
        (tr (((QProc.par g (QProc.ident 1) (qpair A qunit) (qpair B qunit)
          (qtensor B qunit).2).out s).val * E.val)).re at hs
    rw [QProc.weight_mul_prob, QProc.weight_mul_prob] at hs
    exact hs

/-- The finite quantum source has a quantum realization: the representation target is
nonvacuous on a source with two distinct pure states. -/
def quantumData_realization : QuantumRealization quantumData where
  dim A := A.1
  dimension_positive A := A.2
  states _ := Equiv.refl _
  effects _ := Equiv.refl _
  probabilities _ _ _ := rfl
  maps _ _ f := f.map
  positivity _ _ f := f.cp
  trace_bound _ _ f := f.tni
  source_action _ _ f s := f.out_spec s
  composition _ _ _ _ _ := rfl
  operation_fullness _ B L hcp htni := ⟨QProc.ofMap L hcp htni B.2, rfl⟩
  operation_faithfulness _ _ f g := quantumData_faithful f g
  pairIndex A B := qpair A B
  product_states _ _ _ _ _ _ := rfl
  product_effects _ _ _ _ _ _ := rfl
  parallel_on_products A B C E f g a b i j :=
    congrFun (congrFun (parMap_pairMatrix f.map g.map (qpair A C) (qpair B E) a b) i) j

theorem quantumData_has_realization : Nonempty (QuantumRealization quantumData) :=
  ⟨quantumData_realization⟩

/-- Local tomography of the quantum source, read off its realization. -/
theorem quantumData_localTomography : LocalTomography quantumData :=
  realization_localTomography quantumData_realization

end QuantumModelRealization

end OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

/-! Pure quantum states are exactly the rank-one densities. -/

namespace OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

section QuantumPurity

theorem mulVec_normRay {n : ℕ} (ψ x : Fin n → ℂ) :
    normRay ψ *ᵥ x = ((((sqLength ψ)⁻¹ : ℝ) : ℂ) * (star ψ ⬝ᵥ x)) • ψ := by
  rw [normRay, Matrix.smul_mulVec_assoc, ray_mulVec, smul_smul]

/-- Removing the component along a nonzero vector leaves an orthogonal residual. -/
theorem orth_residual {n : ℕ} {ψ : Fin n → ℂ} (hψ : ψ ≠ 0) (x : Fin n → ℂ) :
    star ψ ⬝ᵥ (x - ((((sqLength ψ)⁻¹ : ℝ) : ℂ) * (star ψ ⬝ᵥ x)) • ψ) = 0 := by
  rw [dotProduct_sub, dotProduct_smul, dotProduct_self_eq_sqLength, smul_eq_mul]
  have h : ((((sqLength ψ)⁻¹ : ℝ) : ℂ) * (star ψ ⬝ᵥ x)) * ((sqLength ψ : ℝ) : ℂ) =
      (star ψ ⬝ᵥ x) * ((((sqLength ψ)⁻¹ * sqLength ψ : ℝ)) : ℂ) := by
    rw [Complex.ofReal_mul]
    ring
  rw [h, inv_mul_cancel₀ (ne_of_gt (sqLength_pos hψ)), Complex.ofReal_one, mul_one,
    sub_self]

/-- A component of a convex decomposition of a rank-one density equals that density. -/
theorem eq_normRay_of_mix {n : ℕ} {ψ : Fin n → ℂ} (hψ : ψ ≠ 0) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (a b : Density n)
    (h : (p : ℂ) • a.val + ((1 - p : ℝ) : ℂ) • b.val = normRay ψ) : a.val = normRay ψ := by
  have hpa := density_posSemidef a
  have hpb := density_posSemidef b
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hker : ∀ v, star ψ ⬝ᵥ v = 0 → a.val *ᵥ v = 0 := by
    intro v hv
    have hz : star v ⬝ᵥ (normRay ψ *ᵥ v) = 0 := by
      rw [mulVec_normRay, hv, mul_zero, zero_smul, dotProduct_zero]
    rw [← h, Matrix.add_mulVec, Matrix.smul_mulVec_assoc, Matrix.smul_mulVec_assoc,
      dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hz
    have ha0 := Complex.nonneg_iff.mp (hpa.2 v)
    have hb0 := Complex.nonneg_iff.mp (hpb.2 v)
    have hre := congrArg Complex.re hz
    rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.zero_re] at hre
    have har : (star v ⬝ᵥ (a.val *ᵥ v)).re = 0 := by
      nlinarith [mul_nonneg hp0.le ha0.1, mul_nonneg hq.le hb0.1]
    have hzero : star v ⬝ᵥ (a.val *ᵥ v) = 0 :=
      Complex.ext (by rw [Complex.zero_re]; exact har)
        (by rw [Complex.zero_im]; exact ha0.2.symm)
    exact (hpa.dotProduct_mulVec_zero_iff v).mp hzero
  have hdecomp : ∀ x, a.val *ᵥ x =
      ((((sqLength ψ)⁻¹ : ℝ) : ℂ) * (star ψ ⬝ᵥ x)) • (a.val *ᵥ ψ) := by
    intro x
    have h0 := hker _ (orth_residual hψ x)
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_eq_zero] at h0
    exact h0
  let lam : ℂ := (((sqLength ψ)⁻¹ : ℝ) : ℂ) * (star ψ ⬝ᵥ (a.val *ᵥ ψ))
  have heig : a.val *ᵥ ψ = lam • ψ := by
    let w := a.val *ᵥ ψ - lam • ψ
    have hwψ : star ψ ⬝ᵥ w = 0 := orth_residual hψ (a.val *ᵥ ψ)
    have haw : a.val *ᵥ w = 0 := hker w hwψ
    have hstar : star w ᵥ* a.val = star (a.val *ᵥ w) := by
      rw [Matrix.star_mulVec, (density_hermitian a).eq]
    have hww : star w ⬝ᵥ w = 0 := by
      have e1 : star w ⬝ᵥ (a.val *ᵥ ψ) = 0 := by
        rw [Matrix.dotProduct_mulVec, hstar, haw, star_zero, zero_dotProduct]
      have e2 : star w ⬝ᵥ ψ = 0 := by
        rw [Matrix.star_dotProduct, hwψ, star_zero]
      calc
        star w ⬝ᵥ w = star w ⬝ᵥ (a.val *ᵥ ψ) - lam * (star w ⬝ᵥ ψ) := by
          change star w ⬝ᵥ (a.val *ᵥ ψ - lam • ψ) = _
          rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
        _ = 0 := by rw [e1, e2, mul_zero, sub_zero]
    exact sub_eq_zero.mp (dotProduct_star_self_eq_zero.mp hww)
  have hmat : a.val = lam • normRay ψ := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [Matrix.smul_mulVec_assoc, mulVec_normRay, hdecomp, heig, smul_smul, smul_smul,
      mul_comm]
  have htr := density_trace a
  rw [hmat, Matrix.trace_smul, normRay_trace hψ, smul_eq_mul, mul_one] at htr
  rw [hmat, htr, one_smul]

/-- Every rank-one density is a pure state of the quantum source. -/
theorem rayState_pure {A : QSys} (ψ : Fin A.1 → ℂ) (hψ : ψ ≠ 0) :
    Pure quantumData (rayState ψ hψ : quantumData.State A) := by
  intro p a b hp0 hp1 hmix
  have hm : (p : ℂ) • (a : Density A.1).val + ((1 - p : ℝ) : ℂ) • (b : Density A.1).val =
      normRay ψ := by
    rw [← densityMix_val hp0.le hp1.le]
    exact congrArg Subtype.val hmix
  have hm' : (((1 - p : ℝ)) : ℂ) • (b : Density A.1).val +
      ((1 - (1 - p) : ℝ) : ℂ) • (a : Density A.1).val = normRay ψ := by
    rw [sub_sub_cancel, add_comm]
    exact hm
  exact ⟨Subtype.ext (eq_normRay_of_mix hψ hp0 hp1 a b hm),
    Subtype.ext (eq_normRay_of_mix hψ (sub_pos.mpr hp1) (by linarith) b a hm')⟩

/-- The function ucol returns a column of a unitary matrix. -/
def ucol {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) : Fin n → ℂ :=
  fun r => (u : Mat n) r j

theorem sqLength_ucol {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    sqLength (ucol u j) = 1 := by
  have h := congrArg (fun a : Mat n => a j j) (unitary.coe_star_mul_self u)
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  rw [sqLength, dotProduct]
  simp only [Pi.star_apply, ucol]
  rw [h, Complex.one_re]

theorem ucol_ne_zero {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ucol u j ≠ 0 := by
  intro h
  have h1 := sqLength_ucol u j
  rw [h, sqLength, star_zero, zero_dotProduct, Complex.zero_re] at h1
  linarith

theorem basisProjector_eq_normRay {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    Thermal.basisProjector u j = normRay (ucol u j) := by
  rw [normRay, sqLength_ucol, inv_one, Complex.ofReal_one, one_smul]
  ext r c
  simp only [Thermal.basisProjector, Thermal.spectralLift, Thermal.rotate, Thermal.realDiagonal]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply, ray_apply, ucol]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, Complex.ofReal_one, mul_one]
  · intro b _hb hbj
    rw [if_neg hbj, Complex.ofReal_zero, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem spectralLift_eq_sum {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ) (p : Fin n → ℝ) :
    Thermal.spectralLift u p = ∑ j, ((p j : ℝ) : ℂ) • Thermal.basisProjector u j := by
  have hd : Thermal.realDiagonal p =
      ∑ j, ((p j : ℝ) : ℂ) • Thermal.realDiagonal (fun i => if i = j then (1 : ℝ) else 0) := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp only [Thermal.realDiagonal, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.diagonal_apply_eq, smul_eq_mul]
      rw [Finset.sum_eq_single a]
      · rw [if_pos rfl, Complex.ofReal_one, mul_one]
      · intro j _hj hja
        have haj : a ≠ j := fun h => hja h.symm
        rw [if_neg haj, Complex.ofReal_zero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ a) h
    · simp only [Thermal.realDiagonal, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.diagonal_apply, if_neg hab, smul_eq_mul, mul_zero, Finset.sum_const_zero]
  change (u : Mat n) * Thermal.realDiagonal p * star (u : Mat n) = _
  rw [hd, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  change _ = ((p j : ℝ) : ℂ) •
    ((u : Mat n) * Thermal.realDiagonal (fun i : Fin n => if i = j then (1 : ℝ) else 0) *
      star (u : Mat n))
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Every pure state of the quantum source is a rank-one density. -/
theorem quantumData_pure_ray {A : QSys} (s : quantumData.State A)
    (hs : Pure quantumData s) : ∃ (ψ : Fin A.1 → ℂ) (hψ : ψ ≠ 0), s = rayState ψ hψ := by
  have hpsd := density_posSemidef (s : Density A.1)
  set u := hpsd.1.eigenvectorUnitary with hu
  set p := hpsd.1.eigenvalues with hp
  have hnn : ∀ j, 0 ≤ p j := fun j => hpsd.eigenvalues_nonneg j
  have hsum : ∑ j, p j = 1 := by
    rw [hp, Thermal.eigenvalues_sum_trace hpsd.1, density_trace, Complex.one_re]
  have hspec : (s : Density A.1).val = ∑ j, ((p j : ℝ) : ℂ) • Thermal.basisProjector u j := by
    rw [← spectralLift_eq_sum, hu, hp, Thermal.spectralLift_eigenvalues hpsd.1]
  obtain ⟨k, hk⟩ : ∃ k, 0 < p k := by
    by_contra hcon
    push_neg at hcon
    have h0 : ∑ j, p j = 0 := Finset.sum_eq_zero (fun j _ => le_antisymm (hcon j) (hnn j))
    linarith
  have hrest : ∑ j ∈ Finset.univ.erase k, p j = 1 - p k := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hsum
    linarith
  refine ⟨ucol u k, ucol_ne_zero u k, ?_⟩
  apply Subtype.ext
  change (s : Density A.1).val = normRay (ucol u k)
  rw [← basisProjector_eq_normRay]
  by_cases hk1 : p k = 1
  · have hz : ∀ j ∈ Finset.univ.erase k, p j = 0 := by
      rw [hk1, sub_self] at hrest
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).mp hrest
    rw [hspec, Finset.sum_eq_single k]
    · rw [hk1, Complex.ofReal_one, one_smul]
    · intro j _hj hjk
      rw [hz j (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩), Complex.ofReal_zero, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ k) h
  · have hle1 : p k ≤ 1 := by
      have h0 := Finset.sum_nonneg (fun j (_hj : j ∈ Finset.univ.erase k) => hnn j)
      linarith
    have hlt : p k < 1 := lt_of_le_of_ne hle1 hk1
    have hq : 0 < 1 - p k := sub_pos.mpr hlt
    set rest := ∑ j ∈ Finset.univ.erase k, ((p j : ℝ) : ℂ) • Thermal.basisProjector u j
      with hrestdef
    have hrestpsd : rest.PosSemidef :=
      Thermal.psd_sum _ _ (fun j _ => by
        rw [basisProjector_eq_normRay]
        exact posSemidef_real_smul (normRay_posSemidef _) (hnn j))
    have hresttr : rest.trace = ((1 - p k : ℝ) : ℂ) := by
      calc
        rest.trace = ∑ j ∈ Finset.univ.erase k, ((p j : ℝ) : ℂ) := by
          rw [hrestdef, Matrix.trace_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Matrix.trace_smul, basisProjector_eq_normRay, normRay_trace (ucol_ne_zero u j),
            smul_eq_mul, mul_one]
        _ = ((1 - p k : ℝ) : ℂ) := by rw [← Complex.ofReal_sum, hrest]
    let a : Density A.1 := rayState (ucol u k) (ucol_ne_zero u k)
    let b : Density A.1 := ⟨((((1 - p k)⁻¹ : ℝ)) : ℂ) • rest,
      (psd_iff_posSemidef _).mpr (posSemidef_real_smul hrestpsd (inv_nonneg.mpr hq.le)),
      by
        rw [tr, Matrix.trace_smul, hresttr, smul_eq_mul, ← Complex.ofReal_mul,
          inv_mul_cancel₀ (ne_of_gt hq), Complex.ofReal_one]⟩
    have hmix : quantumData.mix (p k) a b = s := by
      apply Subtype.ext
      change (densityMix (p k) a b).val = (s : Density A.1).val
      rw [densityMix_val hk.le hlt.le, hspec, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      change ((p k : ℝ) : ℂ) • normRay (ucol u k) + ((1 - p k : ℝ) : ℂ) •
        (((((1 - p k)⁻¹ : ℝ)) : ℂ) • rest) =
          ((p k : ℝ) : ℂ) • Thermal.basisProjector u k + rest
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hq),
        Complex.ofReal_one, one_smul, basisProjector_eq_normRay]
    have ha := (hs (p k) a b hk hlt hmix).1
    calc
      (s : Density A.1).val = normRay (ucol u k) := (congrArg Subtype.val ha).symm
      _ = Thermal.basisProjector u k := (basisProjector_eq_normRay u k).symm

/-- Pure states of the quantum source are exactly the rank-one densities. -/
theorem quantumData_pure_iff {A : QSys} (s : quantumData.State A) :
    Pure quantumData s ↔ ∃ (ψ : Fin A.1 → ℂ) (hψ : ψ ≠ 0), s = rayState ψ hψ := by
  constructor
  · exact quantumData_pure_ray s
  · rintro ⟨ψ, hψ, rfl⟩
    exact rayState_pure ψ hψ


/-! ## M5.3 nonvacuity, part 6: atomic effects, pure conditioning and purification existence -/

section QuantumConditioning

theorem ray_smul {n : ℕ} (z : ℂ) (v : Fin n → ℂ) : ray (z • v) = (z * star z) • ray v := by
  ext a b
  simp only [ray_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, star_mul']
  ring

/-- Conjugating a ray by a matrix gives the ray of the image vector. -/
theorem mul_ray_mul_conjTranspose {N n : ℕ} (M : Matrix (Fin N) (Fin n) ℂ) (v : Fin n → ℂ) :
    M * ray v * M.conjTranspose = ray (M *ᵥ v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ray_apply, Matrix.mulVec, dotProduct,
    star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  ring

/-- The product vector of two vectors on the paired joint index. -/
def pairVec {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (φ : Fin n → ℂ) (χ : Fin m → ℂ) :
    Fin N → ℂ := fun x => φ (π x).1 * χ (π x).2

/-- The second-factor vector obtained by contracting a joint vector with `φ`. -/
def contract {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (φ : Fin n → ℂ) (ψ : Fin N → ℂ) :
    Fin m → ℂ := fun k => ∑ i, star (φ i) * ψ (π.symm (i, k))

theorem pairMatrix_normRay_mulVec {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (φ : Fin n → ℂ)
    (ψ : Fin N → ℂ) :
    pairMatrix π (normRay φ) 1 *ᵥ ψ =
      (((sqLength φ)⁻¹ : ℝ) : ℂ) • pairVec π φ (contract π φ ψ) := by
  ext x
  simp only [Matrix.mulVec, dotProduct, pairMatrix, Pi.smul_apply, smul_eq_mul, pairVec,
    contract]
  rw [sum_pair π]
  simp only [Equiv.apply_symm_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true, normRay, Matrix.smul_apply, ray_apply, smul_eq_mul]
  ring

theorem traceLeft_ray_pairVec {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (φ : Fin n → ℂ)
    (χ : Fin m → ℂ) : traceLeft π (ray (pairVec π φ χ)) = ((sqLength φ : ℝ) : ℂ) • ray χ := by
  ext k l
  rw [← dotProduct_self_eq_sqLength]
  simp only [traceLeft, ray_apply, pairVec, Equiv.apply_symm_apply, Matrix.smul_apply,
    smul_eq_mul, dotProduct, Pi.star_apply, star_mul', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem traceLeft_smul {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (z : ℂ) (x : Mat N) :
    traceLeft π (z • x) = z • traceLeft π x := by
  ext k l
  simp only [traceLeft, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem pairMatrix_smul_left' {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (c : ℂ) (a : Mat n)
    (b : Mat m) : pairMatrix π (c • a) b = c • pairMatrix π a b :=
  pairMatrix_smul_left π c a b

/-- A density that is a real multiple of a ray is that normalized ray. -/
theorem density_eq_rayState {n : ℕ} (ρ : Density n) (d : ℝ) (χ : Fin n → ℂ)
    (h : ρ.val = (d : ℂ) • ray χ) : ∃ hχ : χ ≠ 0, ρ = rayState χ hχ := by
  have hχ : χ ≠ 0 := by
    intro h0
    have ht := density_trace ρ
    rw [h, h0] at ht
    have hz : ray (0 : Fin n → ℂ) = 0 := by
      ext a b
      rw [ray_apply]
      simp only [Pi.zero_apply, star_zero, mul_zero, Matrix.zero_apply]
    rw [hz, smul_zero, Matrix.trace_zero] at ht
    exact zero_ne_one ht
  refine ⟨hχ, Subtype.ext ?_⟩
  have ht := density_trace ρ
  rw [h, Matrix.trace_smul, ray_eq_smul_normRay hχ, Matrix.trace_smul, normRay_trace hχ,
    smul_eq_mul, smul_eq_mul, mul_one, ← Complex.ofReal_mul] at ht
  have hd : d * sqLength χ = 1 := by exact_mod_cast ht
  change ρ.val = normRay χ
  rw [h, ray_eq_smul_normRay hχ, smul_smul, ← Complex.ofReal_mul, hd, Complex.ofReal_one,
    one_smul]

theorem hermitian_real_smul {n : ℕ} {a : Mat n} (ha : a.IsHermitian) (q : ℝ) :
    ((q : ℂ) • a).IsHermitian := by
  change ((q : ℂ) • a)ᴴ = (q : ℂ) • a
  rw [Matrix.conjTranspose_smul, ha.eq, Complex.star_def, Complex.conj_ofReal]

theorem normRay_eq {n : ℕ} (ψ : Fin n → ℂ) :
    normRay ψ = (((sqLength ψ)⁻¹ : ℝ) : ℂ) • ray ψ := rfl

/-- Atomic tests of the quantum source are positive multiples of rank-one projectors. -/
theorem quantumData_atomic_ray {A : QSys} (e : quantumData.Test A)
    (he : AtomicTest quantumData e) :
    ∃ (φ : Fin A.1 → ℂ) (_hφ : φ ≠ 0) (c : ℝ), 0 < c ∧
      (e : Effect A.1).val = (c : ℂ) • normRay φ := by
  have hpsd := effect_posSemidef (e : Effect A.1)
  set u := hpsd.1.eigenvectorUnitary with hu
  set p := hpsd.1.eigenvalues with hp
  have hnn : ∀ j, 0 ≤ p j := fun j => hpsd.eigenvalues_nonneg j
  have hspec : (e : Effect A.1).val = ∑ j, ((p j : ℝ) : ℂ) • Thermal.basisProjector u j := by
    rw [← spectralLift_eq_sum, hu, hp, Thermal.spectralLift_eigenvalues hpsd.1]
  obtain ⟨s0, hs0⟩ := he.1
  obtain ⟨k, hk⟩ : ∃ k, 0 < p k := by
    by_contra hcon
    push_neg at hcon
    apply hs0
    have hz : (e : Effect A.1).val = 0 := by
      rw [hspec]
      apply Finset.sum_eq_zero
      intro j _
      rw [le_antisymm (hcon j) (hnn j), Complex.ofReal_zero, zero_smul]
    change (tr ((s0 : Density A.1).val * (e : Effect A.1).val)).re = 0
    rw [hz, Matrix.mul_zero, tr, Matrix.trace_zero, Complex.zero_re]
  have hPn : Thermal.basisProjector u k = normRay (ucol u k) := basisProjector_eq_normRay u k
  have hk1 : p k ≤ 1 := by
    have h := (qprob_mem_unitInterval (rayState (ucol u k) (ucol_ne_zero u k)) e).2
    have hdl := Thermal.diagonalLaw_own_basis u p k
    rw [hu, hp, Thermal.spectralLift_eigenvalues hpsd.1, ← hu, ← hp] at hdl
    rw [Thermal.diagonalLaw, hPn, Matrix.trace_mul_comm] at hdl
    change (tr (normRay (ucol u k) * (e : Effect A.1).val)).re ≤ 1 at h
    rw [← hdl]
    exact h
  have hPpsd : (Thermal.basisProjector u k).PosSemidef := by
    rw [hPn]
    exact normRay_posSemidef _
  have hcompl : (1 - Thermal.basisProjector u k).PosSemidef := by
    rw [hPn]
    exact one_sub_normRay_posSemidef (ucol_ne_zero u k)
  let f : Effect A.1 := ⟨((p k : ℝ) : ℂ) • Thermal.basisProjector u k,
    (psd_iff_posSemidef _).mpr (posSemidef_real_smul hPpsd hk.le),
    (psd_iff_posSemidef _).mpr (by
      have he' : 1 - ((p k : ℝ) : ℂ) • Thermal.basisProjector u k =
          (1 - Thermal.basisProjector u k) +
            ((1 - p k : ℝ) : ℂ) • Thermal.basisProjector u k := by
        rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
        abel
      rw [he']
      exact hcompl.add (posSemidef_real_smul hPpsd (sub_nonneg.mpr hk1)))⟩
  have hrest : (e : Effect A.1).val - ((p k : ℝ) : ℂ) • Thermal.basisProjector u k =
      ∑ j ∈ Finset.univ.erase k, ((p j : ℝ) : ℂ) • Thermal.basisProjector u j := by
    rw [hspec, ← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_sub_cancel_left]
  let g : Effect A.1 := ⟨(e : Effect A.1).val - ((p k : ℝ) : ℂ) • Thermal.basisProjector u k,
    (psd_iff_posSemidef _).mpr (by
      rw [hrest]
      exact Thermal.psd_sum _ _ (fun j _ => by
        rw [basisProjector_eq_normRay]
        exact posSemidef_real_smul (normRay_posSemidef _) (hnn j))),
    (psd_iff_posSemidef _).mpr (by
      have he' : 1 - ((e : Effect A.1).val - ((p k : ℝ) : ℂ) • Thermal.basisProjector u k) =
          (1 - (e : Effect A.1).val) + ((p k : ℝ) : ℂ) • Thermal.basisProjector u k := by abel
      rw [he']
      exact (effect_compl_posSemidef _).add (posSemidef_real_smul hPpsd hk.le))⟩
  have hsplit : (e : Effect A.1).val = ((p k : ℝ) : ℂ) • Thermal.basisProjector u k +
      ((e : Effect A.1).val - ((p k : ℝ) : ℂ) • Thermal.basisProjector u k) := by abel
  obtain ⟨q, hq0, _hq1, hq⟩ := he.2 f g (fun s => by
    change (tr ((s : Density A.1).val * (e : Effect A.1).val)).re =
      (tr ((s : Density A.1).val * (((p k : ℝ) : ℂ) • Thermal.basisProjector u k))).re +
      (tr ((s : Density A.1).val * ((e : Effect A.1).val -
        ((p k : ℝ) : ℂ) • Thermal.basisProjector u k))).re
    conv_lhs => rw [hsplit]
    simp only [tr]
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re])
  have hfq : ((p k : ℝ) : ℂ) • Thermal.basisProjector u k =
      ((q : ℝ) : ℂ) • (e : Effect A.1).val := by
    apply hermitian_eq_of_density_tests (posSemidef_real_smul hPpsd hk.le).1
      (hermitian_real_smul hpsd.1 q)
    intro ρ
    have h := hq ρ
    change (tr (ρ.val * (((p k : ℝ) : ℂ) • Thermal.basisProjector u k))).re =
      q * (tr (ρ.val * (e : Effect A.1).val)).re at h
    rw [h, Matrix.mul_smul]
    simp only [tr]
    rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hqne : q ≠ 0 := by
    intro hqz
    rw [hqz, Complex.ofReal_zero, zero_smul] at hfq
    have ht := congrArg Matrix.trace hfq
    rw [Matrix.trace_smul, hPn, normRay_trace (ucol_ne_zero u k), smul_eq_mul, mul_one,
      Matrix.trace_zero, Complex.ofReal_eq_zero] at ht
    exact hk.ne' ht
  refine ⟨ucol u k, ucol_ne_zero u k, q⁻¹ * p k,
    mul_pos (inv_pos.mpr (lt_of_le_of_ne hq0 (Ne.symm hqne))) hk, ?_⟩
  rw [← hPn, Complex.ofReal_mul, ← smul_smul, hfq, smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ hqne, Complex.ofReal_one, one_smul]

/-- The conditional matrix of a rank-one joint state after a rank-one effect is a ray. -/
theorem traceLeft_conj_normRay {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) {φ : Fin n → ℂ}
    (hφ : φ ≠ 0) (ψ : Fin N → ℂ) (r : ℝ) :
    traceLeft π (pairMatrix π ((r : ℂ) • normRay φ) 1 * normRay ψ *
        pairMatrix π ((r : ℂ) • normRay φ) 1) =
      ((r * r * (sqLength ψ)⁻¹ * (sqLength φ)⁻¹ : ℝ) : ℂ) • ray (contract π φ ψ) := by
  have hs : sqLength φ ≠ 0 := (sqLength_pos hφ).ne'
  have hQ : (pairMatrix π (normRay φ) (1 : Mat m)).conjTranspose =
      pairMatrix π (normRay φ) 1 :=
    (pairMatrix_hermitian π (normRay_posSemidef φ).1 Matrix.isHermitian_one).eq
  have hcore : pairMatrix π (normRay φ) 1 * ray ψ * pairMatrix π (normRay φ) 1 =
      ((((sqLength φ)⁻¹ * (sqLength φ)⁻¹ : ℝ)) : ℂ) •
        ray (pairVec π φ (contract π φ ψ)) := by
    rw [show pairMatrix π (normRay φ) 1 * ray ψ * pairMatrix π (normRay φ) 1 =
        pairMatrix π (normRay φ) 1 * ray ψ *
          (pairMatrix π (normRay φ) (1 : Mat m)).conjTranspose by rw [hQ]]
    rw [mul_ray_mul_conjTranspose, pairMatrix_normRay_mulVec, ray_smul, Complex.star_def,
      Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [pairMatrix_smul_left, normRay_eq ψ]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hcore, smul_smul, traceLeft_smul, traceLeft_ray_pairVec, smul_smul]
  have hsc : ((sqLength φ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have keyC : ((sqLength φ : ℂ))⁻¹ * ((sqLength φ : ℂ))⁻¹ * (sqLength φ : ℂ) =
      ((sqLength φ : ℂ))⁻¹ := by
    field_simp
  congr 1
  push_cast
  linear_combination ((r : ℂ) * (r : ℂ) * ((sqLength ψ : ℂ))⁻¹) * keyC

/-- The conditional state of a rank-one joint state after a rank-one effect is a ray. -/
theorem conditionState_rank_one {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (ψ : Fin N → ℂ)
    (hψ : ψ ≠ 0) (e : Effect n) {φ : Fin n → ℂ} (hφ : φ ≠ 0) {c : ℝ} (hc : 0 < c)
    (hE : e.val = (c : ℂ) • normRay φ) (t : Density m)
    (ht : conditionState π e (rayState ψ hψ) = some t) :
    ∃ hχ : contract π φ ψ ≠ 0, t = rayState (contract π φ ψ) hχ := by
  by_cases hp : 0 < (tr ((rayState ψ hψ).val * pairMatrix π e.val 1)).re
  · have htv : t.val = ((((tr ((rayState ψ hψ).val * pairMatrix π e.val 1)).re)⁻¹ : ℝ) : ℂ) •
        condMat π e (rayState ψ hψ) := by
      rw [conditionState, dif_pos hp] at ht
      rw [← Option.some_inj.mp ht]
    have hsqrtA : (((Real.sqrt c : ℝ) : ℂ) • normRay φ).PosSemidef :=
      posSemidef_real_smul (normRay_posSemidef φ) (Real.sqrt_nonneg c)
    have hsq : (((Real.sqrt c : ℝ) : ℂ) • normRay φ) ^ 2 = e.val := by
      rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul, normRay_idempotent hφ,
        ← Complex.ofReal_mul, Real.mul_self_sqrt hc.le, hE]
    have hsqrt : (effect_posSemidef e).sqrt = ((Real.sqrt c : ℝ) : ℂ) • normRay φ :=
      ((Matrix.PosSemidef.eq_sqrt_iff_sq_eq hsqrtA (effect_posSemidef _)).2 hsq).symm
    have hcond : condMat π e (rayState ψ hψ) =
        ((Real.sqrt c * Real.sqrt c * (sqLength ψ)⁻¹ * (sqLength φ)⁻¹ : ℝ) : ℂ) •
          ray (contract π φ ψ) := by
      rw [condMat, hsqrt]
      exact traceLeft_conj_normRay π hφ ψ (Real.sqrt c)
    exact density_eq_rayState t
      (((tr ((rayState ψ hψ).val * pairMatrix π e.val 1)).re)⁻¹ *
        (Real.sqrt c * Real.sqrt c * (sqLength ψ)⁻¹ * (sqLength φ)⁻¹))
      (contract π φ ψ) (by rw [htv, hcond, smul_smul, ← Complex.ofReal_mul])
  · rw [conditionState, dif_neg hp] at ht
    exact Option.noConfusion ht

/-- Conditioning a pure joint state on an atomic test returns a pure state. -/
theorem quantumData_pureConditioning : PureConditioning quantumData := by
  intro A B s e hs he hp
  obtain ⟨ψ, hψ, rfl⟩ := quantumData_pure_ray s hs
  obtain ⟨φ, hφ, c, hc, hE⟩ := quantumData_atomic_ray e he
  obtain ⟨t, ht⟩ := (conditionState_laws (qpair A B) (rayState ψ hψ) (e : Effect A.1)).2.1 hp
  refine ⟨t, ht, ?_⟩
  obtain ⟨hχ, hteq⟩ := conditionState_rank_one (qpair A B) ψ hψ (e : Effect A.1) hφ hc hE t ht
  rw [hteq]
  exact rayState_pure _ hχ

/-- Every state of the quantum source has a pure joint state with that marginal. -/
theorem quantumData_purification_exists : ∀ (A : quantumData.Obj) (s : quantumData.State A),
    ∃ (B : quantumData.Obj) (t : quantumData.State (quantumData.tensor A B)),
      Pure quantumData t ∧ quantumData.marginal t = s := by
  intro A s
  have hpsd := density_posSemidef (s : Density A.1)
  let ψ : Fin (qtensor A A).1 → ℂ := fun x => hpsd.sqrt (qpair A A x).1 (qpair A A x).2
  have htr : traceRight (qpair A A) (ray ψ) = (s : Density A.1).val := by
    ext i j
    have hH : hpsd.sqrtᴴ = hpsd.sqrt := hpsd.posSemidef_sqrt.1.eq
    calc traceRight (qpair A A) (ray ψ) i j = ∑ k, hpsd.sqrt i k * star (hpsd.sqrt j k) := by
          simp only [traceRight, ray_apply, ψ, Equiv.apply_symm_apply]
      _ = (hpsd.sqrt * hpsd.sqrtᴴ) i j := by
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      _ = (s : Density A.1).val i j := by rw [hH, hpsd.sqrt_mul_self]
  have hψ : ψ ≠ 0 := by
    intro h0
    have ht := density_trace (s : Density A.1)
    rw [← htr, h0] at ht
    have hz : ray (0 : Fin (qtensor A A).1 → ℂ) = 0 := by
      ext a b
      rw [ray_apply]
      simp only [Pi.zero_apply, star_zero, mul_zero, Matrix.zero_apply]
    rw [hz, traceRight_trace, Matrix.trace_zero] at ht
    exact zero_ne_one ht
  have hlen : sqLength ψ = 1 := by
    have h1 := trace_ray_mul ψ 1
    rw [Matrix.mul_one, Matrix.one_mulVec, ← traceRight_trace (qpair A A), htr,
      density_trace] at h1
    rw [sqLength, ← h1, Complex.one_re]
  refine ⟨A, rayState ψ hψ, rayState_pure ψ hψ, ?_⟩
  apply Subtype.ext
  change traceRight (qpair A A) (normRay ψ) = (s : Density A.1).val
  rw [normRay_eq, hlen, inv_one, Complex.ofReal_one, one_smul, htr]

end QuantumConditioning


/-! ## M5.3 nonvacuity, part 7: essential uniqueness of purification

Two families of vectors with equal Gram matrices are related by a unitary matrix: the map
sending the span of the first family to the second is isometric, and an isometry from a
subspace extends to an isometry of the whole space. Applied to the rows of two pure joint
states with the same first marginal, the unitary acts on the second system as a reversible
process, and its action on the joint state is the parallel process with the identity.
-/

open scoped InnerProductSpace

section Uhlmann

/-- Equal Gram matrices give a unitary matrix carrying one family onto the other. -/
theorem exists_unitary_of_gram {n m : ℕ} (x y : Fin n → (Fin m → ℂ))
    (h : ∀ i j, x j ⬝ᵥ star (x i) = y j ⬝ᵥ star (y i)) :
    ∃ W : Mat m, star W * W = 1 ∧ ∀ i, W *ᵥ x i = y i := by
  let X : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun k i => x i k
  let Y : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun k i => y i k
  let G := Matrix.toEuclideanLin X
  let F := Matrix.toEuclideanLin Y
  have hinner : ∀ c : EuclideanSpace ℂ (Fin n), ⟪G c, G c⟫_ℂ = ⟪F c, F c⟫_ℂ := by
    intro c
    simp only [G, F, EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply]
    simp only [dotProduct, Matrix.mulVec, X, Y, Matrix.of_apply, Pi.star_apply, star_sum,
      star_mul', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _hj
    have hij := h i j
    simp only [dotProduct, Pi.star_apply] at hij
    calc ∑ k, (x j k * (WithLp.ofLp c) j) * (star (x i k) * star ((WithLp.ofLp c) i))
        = (WithLp.ofLp c) j * star ((WithLp.ofLp c) i) * ∑ k, x j k * star (x i k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          ring
      _ = (WithLp.ofLp c) j * star ((WithLp.ofLp c) i) * ∑ k, y j k * star (y i k) := by
          rw [hij]
      _ = ∑ k, (y j k * (WithLp.ofLp c) j) * (star (y i k) * star ((WithLp.ofLp c) i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          ring
  have hnorm : ∀ c, ‖G c‖ = ‖F c‖ := by
    intro c
    have h1 := hinner c
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖G c‖ ^ 2 = ‖F c‖ ^ 2 := by exact_mod_cast h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  have hker : LinearMap.ker G ≤ LinearMap.ker F := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, ← hnorm, hc, norm_zero]
  let L₀ : LinearMap.range G →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    ((LinearMap.ker G).liftQ F hker).comp G.quotKerEquivRange.symm.toLinearMap
  have hL₀ : ∀ c, L₀ ⟨G c, LinearMap.mem_range_self G c⟩ = F c := by
    intro c
    simp only [L₀, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  let L : LinearMap.range G →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m) :=
    { toLinearMap := L₀
      norm_map' := by
        rintro ⟨v, hv⟩
        obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hv
        change ‖L₀ ⟨G c, LinearMap.mem_range_self G c⟩‖ = ‖G c‖
        rw [hL₀, hnorm] }
  let W' := L.extend
  have hW' : ∀ c, W' (G c) = F c := by
    intro c
    have h1 := LinearIsometry.extend_apply L ⟨G c, LinearMap.mem_range_self G c⟩
    change W' (G c) = L₀ ⟨G c, LinearMap.mem_range_self G c⟩ at h1
    rw [h1, hL₀]
  let W : Mat m := Matrix.toEuclideanLin.symm W'.toLinearMap
  have hWlin : Matrix.toEuclideanLin W = W'.toLinearMap := LinearEquiv.apply_symm_apply _ _
  have hWv : ∀ v : Fin m → ℂ, W *ᵥ v = WithLp.ofLp (W' (WithLp.toLp 2 v)) := by
    intro v
    have hv := (Matrix.ofLp_toEuclideanLin_apply W (WithLp.toLp 2 v)).symm
    simpa only [WithLp.ofLp_toLp, hWlin] using hv
  refine ⟨W, ?_, ?_⟩
  · ext a b
    have h1 := W'.inner_map_map (WithLp.toLp 2 (Pi.single a (1 : ℂ)))
      (WithLp.toLp 2 (Pi.single b (1 : ℂ)))
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
      ← hWv, ← hWv] at h1
    simp only [WithLp.ofLp_toLp, Matrix.mulVec_single_one] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.star_apply]
    rw [single_dotProduct, one_mul] at h1
    simp only [Matrix.col_apply, dotProduct, Pi.star_apply] at h1
    simp only [Pi.single_apply] at h1
    by_cases hab : a = b
    · subst b
      simp only [if_true, star_one] at h1
      rw [if_pos rfl, ← h1]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    · rw [if_neg (Ne.symm hab), star_zero] at h1
      rw [if_neg hab, ← h1]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  · intro i
    have hxi : x i = X *ᵥ Pi.single i 1 := by
      rw [Matrix.mulVec_single_one]
      rfl
    have hyi : y i = Y *ᵥ Pi.single i 1 := by
      rw [Matrix.mulVec_single_one]
      rfl
    rw [hxi, hWv, hyi]
    rw [show WithLp.toLp 2 (X *ᵥ Pi.single i 1) = Matrix.toEuclideanLin X
      (WithLp.toLp 2 (Pi.single i 1)) from rfl]
    rw [hW' (WithLp.toLp 2 (Pi.single i 1))]
    rfl

end Uhlmann


/-! ## M5.3 nonvacuity, part 8: unitary processes and the purification condition -/

section UnitaryPurification

/-- Conjugation by a rectangular matrix as a linear map. -/
def conjMap {m k : ℕ} (W : Matrix (Fin m) (Fin k) ℂ) : Mat k →ₗ[ℂ] Mat m where
  toFun X := W * X * W.conjTranspose
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl

theorem conjMap_apply {m k : ℕ} (W : Matrix (Fin m) (Fin k) ℂ) (X : Mat k) :
    conjMap W X = W * X * W.conjTranspose := rfl

/-- The block-diagonal amplification of a matrix on an ancilla of size `r`. -/
def blockAmp {m k : ℕ} (W : Matrix (Fin m) (Fin k) ℂ) (r : ℕ) :
    Matrix (Fin r × Fin m) (Fin r × Fin k) ℂ :=
  fun z x => if z.1 = x.1 then W z.2 x.2 else 0

theorem blockAmp_mul_apply {m k r : ℕ} (W : Matrix (Fin m) (Fin k) ℂ)
    (a : Matrix (Fin r × Fin k) (Fin r × Fin k) ℂ) (z : Fin r × Fin m) (y : Fin r × Fin k) :
    (blockAmp W r * a) z y = ∑ p, W z.2 p * a (z.1, p) y := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single z.1]
  · apply Finset.sum_congr rfl
    intro p _hp
    simp only [blockAmp, if_true]
  · intro s _hs hsz
    apply Finset.sum_eq_zero
    intro p _hp
    simp only [blockAmp, if_neg (Ne.symm hsz), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem amplify_conjMap {m k : ℕ} (W : Matrix (Fin m) (Fin k) ℂ) (r : ℕ)
    (a : Matrix (Fin r × Fin k) (Fin r × Fin k) ℂ) :
    amplify (conjMap W) r a = blockAmp W r * a * (blockAmp W r).conjTranspose := by
  ext z w
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single w.1]
  · simp only [blockAmp_mul_apply]
    simp only [Matrix.conjTranspose_apply, blockAmp, if_true, amplify, conjMap_apply,
      Matrix.mul_apply]
  · intro t _ht htw
    apply Finset.sum_eq_zero
    intro q _hq
    simp only [Matrix.conjTranspose_apply, blockAmp, if_neg (Ne.symm htw), star_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem conjMap_cp {m k : ℕ} (W : Matrix (Fin m) (Fin k) ℂ) : CompletelyPositive (conjMap W) := by
  intro r a ha
  rw [amplify_conjMap]
  exact (generalPSD_iff_posSemidef _).mpr
    (((generalPSD_iff_posSemidef a).mp ha).mul_mul_conjTranspose_same _)

theorem trace_conjMap {m k : ℕ} {W : Matrix (Fin m) (Fin k) ℂ}
    (hW : W.conjTranspose * W = 1)
    (X : Mat k) :
    (conjMap W X).trace = X.trace := by
  rw [conjMap_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hW, Matrix.one_mul]

/-- A completely positive trace-preserving map as a process; the normalized output is the
image itself because every input density keeps unit weight. -/
def tpProc {k m : ℕ} (L : Mat k →ₗ[ℂ] Mat m) (hcp : CompletelyPositive L)
    (htp : ∀ X, (L X).trace = X.trace) : QProc k m where
  map := L
  cp := hcp
  tni := fun a _ => le_of_eq (congrArg Complex.re (htp a))
  out ρ := ⟨L ρ.val, (psd_iff_posSemidef _).mpr (cp_positive hcp (density_posSemidef ρ)),
    by rw [tr, htp, density_trace]⟩
  out_spec ρ := by
    change L ρ.val = (((tr (L ρ.val)).re : ℝ) : ℂ) • L ρ.val
    rw [tr, htp, density_trace, Complex.one_re, Complex.ofReal_one, one_smul]

theorem tpProc_weight {k m : ℕ} (L : Mat k →ₗ[ℂ] Mat m) (hcp : CompletelyPositive L)
    (htp : ∀ X, (L X).trace = X.trace) (ρ : Density k) :
    (tr ((tpProc L hcp htp).map ρ.val)).re = 1 := by
  change (tr (L ρ.val)).re = 1
  rw [tr, htp, density_trace, Complex.one_re]

/-- The process is induced by a rectangular isometry. -/
def isoProc {k m : ℕ} (W : Matrix (Fin m) (Fin k) ℂ)
    (hW : W.conjTranspose * W = 1) : QProc k m :=
  tpProc (conjMap W) (conjMap_cp W) (trace_conjMap hW)

/-- The reversible process given by a unitary matrix. -/
def unitaryProc {m : ℕ} (W : Mat m) (hW : star W * W = 1) : QProc m m :=
  isoProc W (by rw [← Matrix.star_eq_conjTranspose]; exact hW)

theorem unitaryProc_weight {m : ℕ} (W : Mat m) (hW : star W * W = 1) (ρ : Density m) :
    (tr ((unitaryProc W hW).map ρ.val)).re = 1 := by
  have hw : W.conjTranspose * W = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hW
  change (tr (conjMap W ρ.val)).re = 1
  rw [tr, trace_conjMap hw, density_trace, Complex.one_re]

theorem star_mul_self_of_star_mul_self {m : ℕ} {W : Mat m} (hW : star W * W = 1) :
    star (star W) * star W = 1 := by
  rw [star_star]
  exact Matrix.mul_eq_one_comm.mp hW

/-- A unitary process is reversible in the quantum source. -/
theorem unitaryProc_reversible {A : QSys} (W : Mat A.1) (hW : star W * W = 1) :
    Reversible quantumData (unitaryProc W hW : quantumData.Process A A) := by
  have hW' := star_mul_self_of_star_mul_self hW
  have hWW : W * star W = 1 := Matrix.mul_eq_one_comm.mp hW
  refine ⟨unitaryProc (star W) hW', fun s => ⟨unitaryProc_weight W hW s,
    unitaryProc_weight (star W) hW' s⟩, fun s => ?_, fun s => ?_⟩
  · apply Subtype.ext
    change star W * (W * (s : Density A.1).val * W.conjTranspose) * (star W).conjTranspose =
      (s : Density A.1).val
    rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_star,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hW, Matrix.one_mul, Matrix.mul_assoc, hW,
      Matrix.mul_one]
  · apply Subtype.ext
    change W * (star W * (s : Density A.1).val * (star W).conjTranspose) * W.conjTranspose =
      (s : Density A.1).val
    rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_star,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hWW, Matrix.one_mul, Matrix.mul_assoc, hWW,
      Matrix.mul_one]

/-- A paired-product entry whose column index is a paired preimage. -/
theorem pairMatrix_apply_symm {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (a : Mat n) (b : Mat m)
    (z : Fin N) (u : Fin n) (p : Fin m) :
    pairMatrix π a b z (π.symm (u, p)) = a (π z).1 u * b (π z).2 p := by
  simp only [pairMatrix, Equiv.apply_symm_apply]

/-- The identity in parallel with conjugation is conjugation by the paired matrix. -/
theorem parMap_id_conjMap {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (W : Mat m) (x : Mat N) :
    parMap LinearMap.id (conjMap W) π π x =
      pairMatrix π 1 W * x * (pairMatrix π 1 W).conjTranspose := by
  ext i j
  have hrow : ∀ (z : Fin N) (y : Mat N) (w : Fin N),
      (pairMatrix π 1 W * y) z w = ∑ p, W (π z).2 p * y (π.symm ((π z).1, p)) w := by
    intro z y w
    rw [Matrix.mul_apply, sum_pair π, Finset.sum_eq_single (π z).1]
    · apply Finset.sum_congr rfl
      intro p _hp
      rw [pairMatrix_apply_symm, Matrix.one_apply_eq, one_mul]
    · intro s _hs hsz
      apply Finset.sum_eq_zero
      intro p _hp
      rw [pairMatrix_apply_symm, Matrix.one_apply_ne (Ne.symm hsz), zero_mul, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hL : parMap LinearMap.id (conjMap W) π π x i j =
      ∑ q, (∑ p, W (π i).2 p * x (π.symm ((π i).1, p)) (π.symm ((π j).1, q))) *
        star (W (π j).2 q) := by
    simp only [parMap, innerL, blockL, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply,
      conjMap_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hL, Matrix.mul_apply, sum_pair π, Finset.sum_eq_single (π j).1]
  · apply Finset.sum_congr rfl
    intro q _hq
    rw [hrow, Matrix.conjTranspose_apply, pairMatrix_apply_symm, Matrix.one_apply_eq, one_mul]
  · intro s _hs hsj
    apply Finset.sum_eq_zero
    intro q _hq
    rw [Matrix.conjTranspose_apply, pairMatrix_apply_symm, Matrix.one_apply_ne (Ne.symm hsj),
      zero_mul, star_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pairMatrix_one_mulVec {N n m : ℕ} (π : Fin N ≃ Fin n × Fin m) (W : Mat m)
    (ψ : Fin N → ℂ) (z : Fin N) :
    (pairMatrix π 1 W *ᵥ ψ) z = ∑ p, W (π z).2 p * ψ (π.symm ((π z).1, p)) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_pair π, Finset.sum_eq_single (π z).1]
  · apply Finset.sum_congr rfl
    intro p _hp
    rw [pairMatrix_apply_symm, Matrix.one_apply_eq, one_mul]
  · intro s _hs hsz
    apply Finset.sum_eq_zero
    intro p _hp
    rw [pairMatrix_apply_symm, Matrix.one_apply_ne (Ne.symm hsz), zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sqLength_smul {n : ℕ} (c : ℝ) (ψ : Fin n → ℂ) :
    sqLength ((c : ℂ) • ψ) = c * c * sqLength ψ := by
  simp only [sqLength, dotProduct, Pi.smul_apply, smul_eq_mul, Pi.star_apply, star_mul',
    Complex.re_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  have hc : star (c : ℂ) = (c : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [hc]
  rw [show (c : ℂ) * star (ψ i) * ((c : ℂ) * ψ i) = ((c * c : ℝ) : ℂ) * (star (ψ i) * ψ i) by
    push_cast
    ring]
  rw [Complex.re_ofReal_mul]

/-- Every nonzero vector has a unit vector with the same normalized ray. -/
theorem exists_unit_ray {n : ℕ} {ψ : Fin n → ℂ} (hψ : ψ ≠ 0) :
    ∃ ψ' : Fin n → ℂ, ψ' ≠ 0 ∧ sqLength ψ' = 1 ∧ normRay ψ' = normRay ψ := by
  have hs := sqLength_pos hψ
  set c : ℝ := (Real.sqrt (sqLength ψ))⁻¹ with hc
  have hcc : c * c * sqLength ψ = 1 := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hs.le, inv_mul_cancel₀ hs.ne']
  have hc0 : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hs).ne'
  have hcoef : c * c = (sqLength ψ)⁻¹ := by
    calc
      c * c = (c * c * sqLength ψ) * (sqLength ψ)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hs.ne', mul_one]
      _ = (sqLength ψ)⁻¹ := by rw [hcc, one_mul]
  refine ⟨(c : ℂ) • ψ, ?_, ?_, ?_⟩
  · intro h0
    apply hψ
    have := congrArg (fun v => ((c⁻¹ : ℝ) : ℂ) • v) h0
    simp only [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc0, Complex.ofReal_one,
      one_smul, smul_zero] at this
    exact this
  · rw [sqLength_smul, hcc]
  · rw [normRay_eq, normRay_eq, sqLength_smul, hcc, inv_one, Complex.ofReal_one, one_smul,
      ray_smul, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, hcoef]

/-- Pure joint states with equal marginals differ by a reversible process on the second system. -/
theorem quantumData_purification_unique : ∀ (A B : quantumData.Obj)
    (s t : quantumData.State (quantumData.tensor A B)),
    Pure quantumData s → Pure quantumData t → quantumData.marginal s = quantumData.marginal t →
    ∃ u : quantumData.Process B B, Reversible quantumData u ∧ quantumData.actRight u s = t := by
  intro A B s t hs ht hm
  obtain ⟨ψ₀, hψ₀, rfl⟩ := quantumData_pure_ray s hs
  obtain ⟨φ₀, hφ₀, rfl⟩ := quantumData_pure_ray t ht
  obtain ⟨ψ, hψ, hψ1, hψe⟩ := exists_unit_ray hψ₀
  obtain ⟨φ, hφ, hφ1, hφe⟩ := exists_unit_ray hφ₀
  have hrayψ : normRay ψ₀ = ray ψ := by
    rw [← hψe, normRay_eq, hψ1, inv_one, Complex.ofReal_one, one_smul]
  have hrayφ : normRay φ₀ = ray φ := by
    rw [← hφe, normRay_eq, hφ1, inv_one, Complex.ofReal_one, one_smul]
  have hmarg : traceRight (qpair A B) (ray ψ) = traceRight (qpair A B) (ray φ) := by
    have h1 := congrArg Subtype.val hm
    change traceRight (qpair A B) (normRay ψ₀) = traceRight (qpair A B) (normRay φ₀) at h1
    rw [hrayψ, hrayφ] at h1
    exact h1
  let x : Fin A.1 → (Fin B.1 → ℂ) := fun i l => ψ ((qpair A B).symm (i, l))
  let y : Fin A.1 → (Fin B.1 → ℂ) := fun i l => φ ((qpair A B).symm (i, l))
  obtain ⟨W, hW, hWxy⟩ := exists_unitary_of_gram x y (fun i j => by
    have h1 := congrFun (congrFun hmarg j) i
    simp only [traceRight, ray_apply] at h1
    simp only [dotProduct, Pi.star_apply, x, y]
    exact h1)
  refine ⟨unitaryProc W hW, unitaryProc_reversible W hW, ?_⟩
  have hvec : pairMatrix (qpair A B) 1 W *ᵥ ψ = φ := by
    ext z
    rw [pairMatrix_one_mulVec]
    have h1 := congrFun (hWxy ((qpair A B) z).1) ((qpair A B) z).2
    simp only [Matrix.mulVec, dotProduct, x, y] at h1
    rw [h1, Prod.mk.eta, Equiv.symm_apply_apply]
  apply Subtype.ext
  change (normOut (parMap LinearMap.id (conjMap W) (qpair A B) (qpair A B))
    (parMap_cp (QProc.ident A.1).cp (unitaryProc W hW).cp (qpair A B) (qpair A B))
    (qtensor A B).2 (rayState ψ₀ hψ₀)).val = normRay φ₀
  have hmap : parMap LinearMap.id (conjMap W) (qpair A B) (qpair A B) (rayState ψ₀ hψ₀).val =
      ray φ := by
    change parMap LinearMap.id (conjMap W) (qpair A B) (qpair A B) (normRay ψ₀) = ray φ
    rw [parMap_id_conjMap, hrayψ, mul_ray_mul_conjTranspose, hvec]
  have hw : (tr (ray φ)).re = 1 := by
    have h1 := trace_ray_mul φ 1
    rw [Matrix.mul_one, Matrix.one_mulVec] at h1
    rw [tr, h1]
    exact hφ1
  rw [normOut, dif_pos (by rw [hmap, hw]; exact one_pos)]
  change (((((tr (parMap LinearMap.id (conjMap W) (qpair A B) (qpair A B)
    (rayState ψ₀ hψ₀).val)).re)⁻¹ : ℝ) : ℂ) • parMap LinearMap.id (conjMap W) (qpair A B)
      (qpair A B) (rayState ψ₀ hψ₀).val) = normRay φ₀
  rw [hmap, hw, inv_one, Complex.ofReal_one, one_smul, hrayφ]

/-- The purification condition holds for the quantum source. -/
theorem quantumData_purification : Purification quantumData :=
  ⟨quantumData_purification_exists, quantumData_purification_unique⟩

end UnitaryPurification


/-! ## M5.3 nonvacuity, part 9: perfect distinguishability

A density with a nonzero kernel vector `v` is perfectly distinguished from the ray of `v` by
the effect `1 - P_v`. A density with trivial kernel has all eigenvalues at least `δ > 0`, so
it dominates `δ/2` times every density and contains every state in its face.
-/

section Distinguishability

theorem spectralLift_posSemidef {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) : (Thermal.spectralLift u p).PosSemidef := by
  apply Thermal.rotate_posSemidef
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.zero_le_real.mpr (hp i)

theorem spectralLift_sub {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ) (p q : Fin n → ℝ) :
    Thermal.spectralLift u (p - q) = Thermal.spectralLift u p - Thermal.spectralLift u q := by
  simp only [Thermal.spectralLift, Thermal.rotate, Thermal.realDiagonal, Pi.sub_apply,
    Complex.ofReal_sub, ← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem spectralLift_const {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ) (c : ℝ) :
    Thermal.spectralLift u (fun _ => c) = (c : ℂ) • 1 := by
  have hd : Thermal.realDiagonal (fun _ : Fin n => c) = (c : ℂ) • (1 : Mat n) := by
    exact (Matrix.smul_one_eq_diagonal (c : ℂ)).symm
  rw [Thermal.spectralLift, Thermal.rotate, hd, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, Thermal.unitary_mul_adjoint]

/-- Every density is dominated by the unit matrix. -/
theorem one_sub_density_posSemidef {n : ℕ} (t : Density n) : (1 - t.val).PosSemidef := by
  have hpsd := density_posSemidef t
  set u := hpsd.1.eigenvectorUnitary with hu
  set p := hpsd.1.eigenvalues with hp
  have hnn : ∀ j, 0 ≤ p j := fun j => hpsd.eigenvalues_nonneg j
  have hsum : ∑ j, p j = 1 := by
    rw [hp, Thermal.eigenvalues_sum_trace hpsd.1, density_trace, Complex.one_re]
  have hle : ∀ j, p j ≤ 1 := by
    intro j
    rw [← hsum]
    exact Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j)
  have he : 1 - t.val = Thermal.spectralLift u ((fun _ => (1 : ℝ)) - p) := by
    rw [spectralLift_sub, spectralLift_const, Complex.ofReal_one, one_smul, hu, hp,
      Thermal.spectralLift_eigenvalues hpsd.1]
  rw [he]
  exact spectralLift_posSemidef u (fun j => by simp only [Pi.sub_apply]; linarith [hle j])

theorem eigen_mulVec_ucol {n : ℕ} {a : Mat n} (ha : a.IsHermitian) (k : Fin n) :
    a *ᵥ ucol ha.eigenvectorUnitary k = ((ha.eigenvalues k : ℝ) : ℂ) • ucol ha.eigenvectorUnitary k := by
  have h := ha.mulVec_eigenvectorBasis k
  have hc : ucol ha.eigenvectorUnitary k = ⇑(ha.eigenvectorBasis k) := by
    ext i
    exact Matrix.IsHermitian.eigenvectorUnitary_apply ha i k
  rw [hc]
  exact h

/-- A density that dominates a positive multiple of another contains it in its face. -/
theorem inFace_of_dominates {A : QSys} (s t : quantumData.State A) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1)
    (hrest : ((s : Density A.1).val - ((q : ℝ) : ℂ) • (t : Density A.1).val).PosSemidef) :
    InFace quantumData s t := by
  have hq1' : 0 < 1 - q := sub_pos.mpr hq1
  let w : Density A.1 := ⟨((((1 - q)⁻¹ : ℝ)) : ℂ) •
      ((s : Density A.1).val - ((q : ℝ) : ℂ) • (t : Density A.1).val),
    (psd_iff_posSemidef _).mpr (posSemidef_real_smul hrest (inv_nonneg.mpr hq1'.le)),
    by
      rw [tr, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, density_trace,
        density_trace, smul_eq_mul, smul_eq_mul, mul_one]
      rw [show (1 : ℂ) - ((q : ℝ) : ℂ) = ((1 - q : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_mul, inv_mul_cancel₀ hq1'.ne', Complex.ofReal_one]⟩
  refine ⟨q, w, hq0, hq1.le, ?_⟩
  apply Subtype.ext
  change (densityMix q t w).val = (s : Density A.1).val
  rw [densityMix_val hq0.le hq1.le]
  change ((q : ℝ) : ℂ) • (t : Density A.1).val + ((1 - q : ℝ) : ℂ) •
    (((((1 - q)⁻¹ : ℝ)) : ℂ) • ((s : Density A.1).val - ((q : ℝ) : ℂ) • (t : Density A.1).val)) =
      (s : Density A.1).val
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hq1'.ne', Complex.ofReal_one, one_smul]
  abel

/-- The face of a density with trivial kernel contains every density. -/
theorem inFace_of_trivial_kernel {A : QSys} (s : quantumData.State A)
    (hker : ∀ v : Fin A.1 → ℂ, (s : Density A.1).val *ᵥ v = 0 → v = 0)
    (t : quantumData.State A) : InFace quantumData s t := by
  have hpsd := density_posSemidef (s : Density A.1)
  set u := hpsd.1.eigenvectorUnitary with hu
  set p := hpsd.1.eigenvalues with hp
  have hnn : ∀ j, 0 ≤ p j := fun j => hpsd.eigenvalues_nonneg j
  have hsum : ∑ j, p j = 1 := by
    rw [hp, Thermal.eigenvalues_sum_trace hpsd.1, density_trace, Complex.one_re]
  have hpos : ∀ j, 0 < p j := by
    intro j
    rcases (hnn j).lt_or_eq with h | h
    · exact h
    · exfalso
      apply ucol_ne_zero u j
      apply hker
      rw [hu, eigen_mulVec_ucol hpsd.1 j, ← hp, ← h, Complex.ofReal_zero, zero_smul]
  have hne : (Finset.univ : Finset (Fin A.1)).Nonempty := ⟨⟨0, A.2⟩, Finset.mem_univ _⟩
  set δ := Finset.univ.inf' hne p with hδ
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    exact fun j _ => hpos j
  have hδle : ∀ j, δ ≤ p j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  have hδ1 : δ ≤ 1 := by
    have h0 := hδle ⟨0, A.2⟩
    have h1 : p ⟨0, A.2⟩ ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ _)
    linarith
  set q : ℝ := δ / 2 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  have hsdom : ((s : Density A.1).val - ((δ : ℝ) : ℂ) • 1).PosSemidef := by
    have he : (s : Density A.1).val - ((δ : ℝ) : ℂ) • 1 =
        Thermal.spectralLift u (p - fun _ => δ) := by
      rw [spectralLift_sub, spectralLift_const, hu, hp, Thermal.spectralLift_eigenvalues hpsd.1]
    rw [he]
    exact spectralLift_posSemidef u (fun j => by simp only [Pi.sub_apply]; linarith [hδle j])
  have hrest : ((s : Density A.1).val - ((q : ℝ) : ℂ) • (t : Density A.1).val).PosSemidef := by
    have he : (s : Density A.1).val - ((q : ℝ) : ℂ) • (t : Density A.1).val =
        ((s : Density A.1).val - ((δ : ℝ) : ℂ) • 1) +
          (((q : ℝ) : ℂ) • (1 - (t : Density A.1).val) + ((q : ℝ) : ℂ) • 1) := by
      rw [show ((δ : ℝ) : ℂ) = ((q : ℝ) : ℂ) + ((q : ℝ) : ℂ) by rw [hq]; push_cast; ring,
        add_smul, smul_sub]
      abel
    rw [he]
    exact hsdom.add ((posSemidef_real_smul (one_sub_density_posSemidef t) hq0.le).add
      (posSemidef_real_smul Matrix.PosSemidef.one hq0.le))
  exact inFace_of_dominates s t hq0 hq1 hrest

/-- The complementary projector of a ray as an effect. -/
def rayComplEffect {n : ℕ} (v : Fin n → ℂ) (hv : v ≠ 0) : Effect n :=
  ⟨1 - normRay v, (psd_iff_posSemidef _).mpr (one_sub_normRay_posSemidef hv),
    (psd_iff_posSemidef _).mpr (by rw [sub_sub_cancel]; exact normRay_posSemidef v)⟩

/-- Perfect distinguishability holds for the quantum source. -/
theorem quantumData_perfectDistinguishability : PerfectDistinguishability quantumData := by
  intro A s hs
  by_cases hk : ∃ v : Fin A.1 → ℂ, v ≠ 0 ∧ (s : Density A.1).val *ᵥ v = 0
  · obtain ⟨v, hv, hsv⟩ := hk
    refine ⟨rayState v hv, rayComplEffect v hv, ?_, ?_⟩
    · change (tr ((s : Density A.1).val * (1 - normRay v))).re = 1
      rw [tr, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, density_trace,
        Matrix.trace_mul_comm, trace_normRay_mul, hsv, dotProduct_zero, mul_zero, sub_zero,
        Complex.one_re]
    · change (tr (normRay v * (1 - normRay v))).re = 0
      rw [tr, Matrix.mul_sub, Matrix.mul_one, normRay_idempotent hv, sub_self,
        Matrix.trace_zero, Complex.zero_re]
  · exfalso
    push_neg at hk
    obtain ⟨t, ht⟩ := hs
    exact ht (inFace_of_trivial_kernel s (fun v hv => by
      by_contra hne
      exact hk v hne hv) t)

end Distinguishability

/-! ## M5.3 nonvacuity, part 10: ideal compression

The support of a density is spanned by the eigenvectors with positive eigenvalue. The
isometry `V` onto that support decodes; the encoder applies `V*` and sends the orthogonal
complement to a fixed basis state through rank-one Kraus operators, so it is trace preserving.
States in the face of the density vanish on the complement, so decoding recovers them, and
every state of the compressed system is the encoding of a state in the face.
-/

section Compression

theorem cp_add {n m : ℕ} {f g : Mat n →ₗ[ℂ] Mat m} (hf : CompletelyPositive f)
    (hg : CompletelyPositive g) : CompletelyPositive (f + g) := by
  intro r a ha
  have heq : amplify (f + g) r a = amplify f r a + amplify g r a := by
    ext p q
    rfl
  rw [heq]
  exact (generalPSD_iff_posSemidef _).mpr (((generalPSD_iff_posSemidef _).mp (hf r a ha)).add
    ((generalPSD_iff_posSemidef _).mp (hg r a ha)))

theorem cp_zero {n m : ℕ} : CompletelyPositive (0 : Mat n →ₗ[ℂ] Mat m) := by
  intro r a _ha
  have heq : amplify (0 : Mat n →ₗ[ℂ] Mat m) r a = 0 := by
    ext p q
    rfl
  rw [heq]
  exact (generalPSD_iff_posSemidef _).mpr Matrix.PosSemidef.zero

theorem cp_sum {n m : ℕ} {ι : Type} (s : Finset ι) (f : ι → (Mat n →ₗ[ℂ] Mat m))
    (h : ∀ i ∈ s, CompletelyPositive (f i)) : CompletelyPositive (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact cp_zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact cp_add (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Evaluation of a finite sum of matrix linear maps is the sum of the evaluations. -/
theorem matrixLinearSum_apply {k m : ℕ} {ι : Type} (S : Finset ι)
    (f : ι → (Mat k →ₗ[ℂ] Mat m)) (X : Mat k) :
    (∑ i ∈ S, f i) X = ∑ i ∈ S, f i X := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, LinearMap.zero_apply]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi, LinearMap.add_apply, ih]

theorem trace_conjMap_eq {m k : ℕ} (W : Matrix (Fin m) (Fin k) ℂ) (X : Mat k) :
    (conjMap W X).trace = (W.conjTranspose * W * X).trace := by
  rw [conjMap_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc]

variable {n : ℕ}

/-- The support isometry contains the columns of the unitary indexed by the support set. -/
def suppIso (u : Matrix.unitaryGroup (Fin n) ℂ) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin S.card) ℂ :=
  fun i a => (u : Mat n) i (S.equivFin.symm a).1

theorem sum_fin_card (S : Finset (Fin n)) (g : Fin n → ℂ) :
    (∑ a : Fin S.card, g (S.equivFin.symm a).1) = ∑ j ∈ S, g j := by
  rw [Equiv.sum_comp S.equivFin.symm (fun x : S => g x.1), Finset.sum_coe_sort S g]

theorem suppIso_isometry (u : Matrix.unitaryGroup (Fin n) ℂ) (S : Finset (Fin n)) :
    (suppIso u S).conjTranspose * suppIso u S = 1 := by
  ext a b
  have h := congrArg (fun M : Mat n => M (S.equivFin.symm a).1 (S.equivFin.symm b).1)
    (unitary.coe_star_mul_self u)
  simp only [Matrix.mul_apply, Matrix.star_apply] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, suppIso]
  rw [h, Matrix.one_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst b
    simp only [if_true]
  · have hne : (S.equivFin.symm a).1 ≠ (S.equivFin.symm b).1 := by
      intro he
      exact hab (S.equivFin.symm.injective (Subtype.ext he))
    rw [if_neg hne, if_neg hab]

theorem basisProjector_apply (u : Matrix.unitaryGroup (Fin n) ℂ) (j i k : Fin n) :
    Thermal.basisProjector u j i k = (u : Mat n) i j * star ((u : Mat n) k j) := by
  rw [basisProjector_eq_normRay, normRay_eq, sqLength_ucol, inv_one, Complex.ofReal_one,
    one_smul, ray_apply]
  rfl

theorem suppIso_mul_star (u : Matrix.unitaryGroup (Fin n) ℂ) (S : Finset (Fin n)) :
    suppIso u S * (suppIso u S).conjTranspose = ∑ j ∈ S, Thermal.basisProjector u j := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, suppIso, Matrix.sum_apply,
    basisProjector_apply]
  exact sum_fin_card S (fun j => (u : Mat n) i j * star ((u : Mat n) k j))

/-- The rank-one Kraus operator sends its unitary column to the first compressed basis vector. -/
def discardKraus (u : Matrix.unitaryGroup (Fin n) ℂ) {r : ℕ} (hr : 0 < r) (j : Fin n) :
    Matrix (Fin r) (Fin n) ℂ :=
  fun a i => if a = ⟨0, hr⟩ then star ((u : Mat n) i j) else 0

theorem discardKraus_star_mul (u : Matrix.unitaryGroup (Fin n) ℂ) {r : ℕ} (hr : 0 < r)
    (j : Fin n) :
    (discardKraus u hr j).conjTranspose * discardKraus u hr j = Thermal.basisProjector u j := by
  ext i k
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨0, hr⟩, basisProjector_apply]
  · simp only [Matrix.conjTranspose_apply, discardKraus, if_true, star_star]
  · intro a _ha hne
    simp only [discardKraus, if_neg hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The encoder compresses the support and resets its orthogonal complement. -/
def encMap (u : Matrix.unitaryGroup (Fin n) ℂ) (S : Finset (Fin n)) (hr : 0 < S.card) :
    Mat n →ₗ[ℂ] Mat S.card :=
  conjMap (suppIso u S).conjTranspose + ∑ j ∈ Finset.univ \ S, conjMap (discardKraus u hr j)

theorem encMap_cp (u : Matrix.unitaryGroup (Fin n) ℂ) (S : Finset (Fin n)) (hr : 0 < S.card) :
    CompletelyPositive (encMap u S hr) :=
  cp_add (conjMap_cp _) (cp_sum _ _ (fun _ _ => conjMap_cp _))

theorem encMap_tp (u : Matrix.unitaryGroup (Fin n) ℂ) (S : Finset (Fin n)) (hr : 0 < S.card)
    (X : Mat n) : (encMap u S hr X).trace = X.trace := by
  have hsum : (suppIso u S).conjTranspose.conjTranspose * (suppIso u S).conjTranspose +
      ∑ j ∈ Finset.univ \ S, (discardKraus u hr j).conjTranspose * discardKraus u hr j = 1 := by
    rw [Matrix.conjTranspose_conjTranspose, suppIso_mul_star]
    simp only [discardKraus_star_mul]
    have hd : Disjoint S (Finset.univ \ S) :=
      Finset.disjoint_left.mpr (fun _ hj hk => (Finset.mem_sdiff.mp hk).2 hj)
    rw [← Finset.sum_union hd, Finset.union_sdiff_of_subset (Finset.subset_univ S),
      Thermal.basisProjector_sum]
  simp only [encMap, LinearMap.add_apply, matrixLinearSum_apply,
    Matrix.trace_add, Matrix.trace_sum, trace_conjMap_eq]
  rw [← Matrix.trace_sum, ← Matrix.trace_add, ← Finset.sum_mul, ← Matrix.add_mul, hsum,
    Matrix.one_mul]

/-- A null vector of a convex combination is a null vector of each positive-weight component. -/
theorem mulVec_zero_of_mix {k : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (a b c : Density k)
    (h : (q : ℂ) • a.val + ((1 - q : ℝ) : ℂ) • b.val = c.val) (v : Fin k → ℂ)
    (hv : c.val *ᵥ v = 0) : a.val *ᵥ v = 0 := by
  have hz : star v ⬝ᵥ (c.val *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
  rw [← h, Matrix.add_mulVec, Matrix.smul_mulVec_assoc, Matrix.smul_mulVec_assoc,
    dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hz
  have ha0 := Complex.nonneg_iff.mp ((density_posSemidef a).2 v)
  have hb0 := Complex.nonneg_iff.mp ((density_posSemidef b).2 v)
  have hre := congrArg Complex.re hz
  rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.zero_re] at hre
  have hq : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have har : (star v ⬝ᵥ (a.val *ᵥ v)).re = 0 := by
    nlinarith [mul_nonneg hq0.le ha0.1, mul_nonneg hq hb0.1]
  have hzero : star v ⬝ᵥ (a.val *ᵥ v) = 0 :=
    Complex.ext (by rw [Complex.zero_re]; exact har) (by rw [Complex.zero_im]; exact ha0.2.symm)
  exact ((density_posSemidef a).dotProduct_mulVec_zero_iff v).mp hzero

/-- A matrix that annihilates a unitary column annihilates its ray projector on the right. -/
theorem mul_basisProjector_eq_zero (u : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n)
    (j : Fin n) (hv : X *ᵥ ucol u j = 0) :
    X * Thermal.basisProjector u j = 0 := by
  ext i k
  change (X * Thermal.basisProjector u j) i k = 0
  rw [Matrix.mul_apply]
  calc
    (∑ a, X i a * Thermal.basisProjector u j a k) =
        (X *ᵥ ucol u j) i * star ((u : Mat n) k j) := by
      simp only [basisProjector_apply, Matrix.mulVec, dotProduct, ucol, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = 0 := by rw [hv, Pi.zero_apply, zero_mul]

/-- The support projection acts as the identity on the right of a supported matrix. -/
theorem matrix_mul_support (u : Matrix.unitaryGroup (Fin n) ℂ) (S : Finset (Fin n))
    (X : Mat n) (hnull : ∀ j, j ∉ S → X *ᵥ ucol u j = 0) :
    X * (suppIso u S * (suppIso u S).conjTranspose) = X := by
  have hs : (∑ j ∈ S, X * Thermal.basisProjector u j) =
      ∑ j, X * Thermal.basisProjector u j :=
    Finset.sum_subset (Finset.subset_univ S)
      (fun j _hj hj => mul_basisProjector_eq_zero u X j (hnull j hj))
  rw [suppIso_mul_star, Matrix.mul_sum, hs, ← Matrix.mul_sum,
    Thermal.basisProjector_sum, Matrix.mul_one]

/-- The support projection acts as the identity on the left of a supported Hermitian matrix. -/
theorem support_mul_matrix (u : Matrix.unitaryGroup (Fin n) ℂ) (S : Finset (Fin n))
    (X : Mat n) (hX : X.IsHermitian)
    (hnull : ∀ j, j ∉ S → X *ᵥ ucol u j = 0) :
    (suppIso u S * (suppIso u S).conjTranspose) * X = X := by
  have h := congrArg Matrix.conjTranspose (matrix_mul_support u S X hnull)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hX.eq] at h
  exact h

/-- Each complement Kraus term vanishes on a density that annihilates its unitary column. -/
theorem discardKraus_conjMap_eq_zero (u : Matrix.unitaryGroup (Fin n) ℂ) {r : ℕ}
    (hr : 0 < r) (j : Fin n) (t : Density n) (hv : t.val *ᵥ ucol u j = 0) :
    conjMap (discardKraus u hr j) t.val = 0 := by
  apply posSemidef_eq_zero_of_trace_re
    (cp_positive (conjMap_cp _) (density_posSemidef t))
  rw [trace_conjMap_eq, discardKraus_star_mul, basisProjector_eq_normRay,
    trace_normRay_mul, hv, dotProduct_zero, mul_zero, Complex.zero_re]

/-- The encoder restricts to the adjoint isometry on every density supported in its range. -/
theorem encMap_on_support (u : Matrix.unitaryGroup (Fin n) ℂ) (S : Finset (Fin n))
    (hr : 0 < S.card) (t : Density n)
    (hnull : ∀ j, j ∉ S → t.val *ᵥ ucol u j = 0) :
    encMap u S hr t.val = (suppIso u S).conjTranspose * t.val * suppIso u S := by
  have hz : (∑ j ∈ Finset.univ \ S, conjMap (discardKraus u hr j) t.val) = 0 :=
    Finset.sum_eq_zero (fun j hj =>
      discardKraus_conjMap_eq_zero u hr j t (hnull j (Finset.mem_sdiff.mp hj).2))
  rw [encMap, LinearMap.add_apply, matrixLinearSum_apply, hz, add_zero, conjMap_apply,
    Matrix.conjTranspose_conjTranspose]

/-- The adjoint support isometry annihilates every omitted unitary column. -/
theorem suppIso_adjoint_ucol_off (u : Matrix.unitaryGroup (Fin n) ℂ)
    (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S) :
    (suppIso u S).conjTranspose *ᵥ ucol u j = 0 := by
  ext a
  have hne : (S.equivFin.symm a).1 ≠ j := by
    intro he
    exact hj (he ▸ (S.equivFin.symm a).property)
  have h := congrArg (fun M : Mat n => M (S.equivFin.symm a).1 j)
    (unitary.coe_star_mul_self u)
  change (∑ k, star ((u : Mat n) k (S.equivFin.symm a).1) * (u : Mat n) k j) =
    (1 : Mat n) (S.equivFin.symm a).1 j at h
  change (∑ k, star ((u : Mat n) k (S.equivFin.symm a).1) * (u : Mat n) k j) = 0
  rw [h, Matrix.one_apply_ne hne]

/-- Every decoded matrix annihilates the omitted unitary columns. -/
theorem conjMap_suppIso_null (u : Matrix.unitaryGroup (Fin n) ℂ)
    (S : Finset (Fin n)) (X : Mat S.card) (j : Fin n) (hj : j ∉ S) :
    conjMap (suppIso u S) X *ᵥ ucol u j = 0 := by
  rw [conjMap_apply, ← Matrix.mulVec_mulVec, suppIso_adjoint_ucol_off u S j hj,
    Matrix.mulVec_zero]

/-- A spectral support bound gives an explicit positive-weight face witness. -/
theorem inFace_of_spectral_support {A : QSys} (s t : quantumData.State A)
    (u : Matrix.unitaryGroup (Fin A.1) ℂ) (S : Finset (Fin A.1))
    (hS : S.Nonempty) (p : Fin A.1 → ℝ) (hp : ∀ j ∈ S, 0 < p j)
    (hspec : (s : Density A.1).val =
      ∑ j ∈ S, ((p j : ℝ) : ℂ) • Thermal.basisProjector u j)
    (hbound : (suppIso u S * (suppIso u S).conjTranspose -
      (t : Density A.1).val).PosSemidef) :
    InFace quantumData s t := by
  set δ : ℝ := S.inf' hS p with hδ
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    exact hp
  have hδle : ∀ j ∈ S, δ ≤ p j := fun j hj => Finset.inf'_le p hj
  set q : ℝ := min δ 1 / 2 with hq
  have hq0 : 0 < q := by
    rw [hq]
    positivity
  have hq1 : q < 1 := by
    have hm := min_le_right δ (1 : ℝ)
    rw [hq]
    linarith
  have hqδ : q ≤ δ := by
    have hm := min_le_left δ (1 : ℝ)
    rw [hq]
    linarith
  have hsdom : ((s : Density A.1).val -
      (q : ℂ) • (suppIso u S * (suppIso u S).conjTranspose)).PosSemidef := by
    rw [hspec, suppIso_mul_star, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Thermal.psd_sum
    intro j hj
    rw [← sub_smul, ← Complex.ofReal_sub]
    apply posSemidef_real_smul
    · rw [basisProjector_eq_normRay]
      exact normRay_posSemidef _
    · exact sub_nonneg.mpr (hqδ.trans (hδle j hj))
  have hrest : ((s : Density A.1).val -
      (q : ℂ) • (t : Density A.1).val).PosSemidef := by
    have he : (s : Density A.1).val - (q : ℂ) • (t : Density A.1).val =
        ((s : Density A.1).val -
          (q : ℂ) • (suppIso u S * (suppIso u S).conjTranspose)) +
          (q : ℂ) • (suppIso u S * (suppIso u S).conjTranspose -
            (t : Density A.1).val) := by
      rw [smul_sub]
      abel
    rw [he]
    exact hsdom.add (posSemidef_real_smul hbound hq0.le)
  exact inFace_of_dominates s t hq0 hq1 hrest

/-- Ideal compression holds for the quantum source. -/
theorem quantumData_idealCompression : IdealCompression quantumData := by
  intro A s
  have hpsd := density_posSemidef (s : Density A.1)
  set u := hpsd.1.eigenvectorUnitary with hu
  set p := hpsd.1.eigenvalues with hp
  have hnn : ∀ j, 0 ≤ p j := fun j => hpsd.eigenvalues_nonneg j
  have hsum : ∑ j, p j = 1 := by
    rw [hp, Thermal.eigenvalues_sum_trace hpsd.1, density_trace, Complex.one_re]
  set S : Finset (Fin A.1) := Finset.univ.filter (fun j => 0 < p j) with hS
  have hr : 0 < S.card := by
    rw [Finset.card_pos]
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, hS, Finset.filter_eq_empty_iff] at hcon
    have h0 : ∑ j, p j = 0 :=
      Finset.sum_eq_zero (fun j hj => le_antisymm (not_lt.mp (hcon hj)) (hnn j))
    linarith
  have hoff : ∀ j, j ∉ S → p j = 0 := by
    intro j hj
    rw [hS, Finset.mem_filter] at hj
    push_neg at hj
    exact le_antisymm (hj (Finset.mem_univ j)) (hnn j)
  let V := suppIso u S
  have hVV : V.conjTranspose * V = 1 := suppIso_isometry u S
  have hspec : (s : Density A.1).val = ∑ j ∈ S, ((p j : ℝ) : ℂ) • Thermal.basisProjector u j := by
    rw [← Thermal.spectralLift_eigenvalues hpsd.1, ← hu, ← hp, spectralLift_eq_sum]
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by
      rw [hoff j hj, Complex.ofReal_zero, zero_smul])]
  have hnull : ∀ j, j ∉ S → (s : Density A.1).val *ᵥ ucol u j = 0 := by
    intro j hj
    rw [hu, eigen_mulVec_ucol hpsd.1 j, ← hp, hoff j hj, Complex.ofReal_zero, zero_smul]
  let B : QSys := ⟨S.card, hr⟩
  let enc : quantumData.Process A B := tpProc (encMap u S hr) (encMap_cp u S hr)
    (encMap_tp u S hr)
  let dec : quantumData.Process B A := isoProc V hVV
  refine ⟨B, enc, dec, fun t => tpProc_weight _ _ _ t, fun w => tpProc_weight _ _ _ w, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, w, hq0, hq1, hmix⟩ := ht
    have hmixval : (q : ℂ) • (t : Density A.1).val +
        ((1 - q : ℝ) : ℂ) • (w : Density A.1).val = (s : Density A.1).val := by
      have h := congrArg (fun z : quantumData.State A => (z : Density A.1).val) hmix
      change (densityMix q t w).val = (s : Density A.1).val at h
      rw [densityMix_val hq0.le hq1] at h
      exact h
    have htNull : ∀ j, j ∉ S → (t : Density A.1).val *ᵥ ucol u j = 0 :=
      fun j hj => mulVec_zero_of_mix hq0 hq1 t w s hmixval (ucol u j) (hnull j hj)
    have htR : (t : Density A.1).val * (V * V.conjTranspose) =
        (t : Density A.1).val := matrix_mul_support u S t.val htNull
    have htL : (V * V.conjTranspose) * (t : Density A.1).val =
        (t : Density A.1).val :=
      support_mul_matrix u S t.val (density_hermitian t) htNull
    apply Subtype.ext
    change V * (encMap u S hr (t : Density A.1).val) * V.conjTranspose =
      (t : Density A.1).val
    rw [encMap_on_support u S hr t htNull]
    change V * (V.conjTranspose * (t : Density A.1).val * V) * V.conjTranspose =
      (t : Density A.1).val
    calc
      V * (V.conjTranspose * (t : Density A.1).val * V) * V.conjTranspose =
          (V * V.conjTranspose) * (t : Density A.1).val * (V * V.conjTranspose) := by
        simp only [Matrix.mul_assoc]
      _ = (t : Density A.1).val := by rw [htL, htR]
  · intro w
    let t : quantumData.State A := quantumData.act dec w
    have htval : (t : Density A.1).val =
        V * (w : Density B.1).val * V.conjTranspose := rfl
    have htNull : ∀ j, j ∉ S → (t : Density A.1).val *ᵥ ucol u j = 0 := by
      intro j hj
      change conjMap (suppIso u S) (w : Density B.1).val *ᵥ ucol u j = 0
      exact conjMap_suppIso_null u S w.val j hj
    have hbound : (V * V.conjTranspose - (t : Density A.1).val).PosSemidef := by
      have h := (one_sub_density_posSemidef (w : Density B.1)).mul_mul_conjTranspose_same V
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul] at h
      rw [htval]
      exact h
    have htFace : InFace quantumData s t :=
      inFace_of_spectral_support s t u S (Finset.card_pos.mp hr) p
        (fun j hj => (Finset.mem_filter.mp hj).2) hspec hbound
    refine ⟨t, htFace, ?_⟩
    apply Subtype.ext
    change encMap u S hr (t : Density A.1).val = (w : Density B.1).val
    rw [encMap_on_support u S hr t htNull, htval]
    change V.conjTranspose * (V * (w : Density B.1).val * V.conjTranspose) * V =
      (w : Density B.1).val
    calc
      V.conjTranspose * (V * (w : Density B.1).val * V.conjTranspose) * V =
          (V.conjTranspose * V) * (w : Density B.1).val * (V.conjTranspose * V) := by
        simp only [Matrix.mul_assoc]
      _ = (w : Density B.1).val := by rw [hVV, Matrix.one_mul, Matrix.mul_one]


/-- The quantum source satisfies all six selection conditions. -/
theorem quantumData_selectionConditions : SelectionConditions quantumData :=
  ⟨quantumData_causality, quantumData_perfectDistinguishability,
    quantumData_idealCompression, quantumData_localTomography,
    quantumData_pureConditioning, quantumData_purification⟩

end Compression

/-! ## M5.4 operational effect premises

Affine effect fullness concerns bounded affine functions of the operational state space.
It is defined through state mixtures and reported probabilities without a matrix
representation. The singleton source violates this condition. Every quantum
realization supplies zero tests and at least two distinct tests in every system.
-/

section EffectPremises

def AffineProbability (D : OperationalData) (A : D.Obj) (f : D.State A → ℝ) : Prop :=
  (∀ s, 0 ≤ f s ∧ f s ≤ 1) ∧
  ∀ (s t : D.State A) (p : ℝ), 0 ≤ p → p ≤ 1 →
    f (D.mix p s t) = p * f s + (1 - p) * f t

def AffineEffectFullness (D : OperationalData) : Prop :=
  ∀ (A : D.Obj) (f : D.State A → ℝ), AffineProbability D A f →
    ∃ e : D.Test A, ∀ s, D.prob e s = f s

def HasZeroOperationalEffect (D : OperationalData) : Prop :=
  ∀ A : D.Obj, ∃ e : D.Test A, ∀ s, D.prob e s = 0

def HasTwoOperationalTests (D : OperationalData) : Prop :=
  ∀ A : D.Obj, ∃ e f : D.Test A, e ≠ f

theorem zero_affineProbability (D : OperationalData) (A : D.Obj) :
    AffineProbability D A (fun _ => 0) := by
  constructor
  · intro s
    exact ⟨le_rfl, zero_le_one⟩
  · intro s t p _hp0 _hp1
    simp only [mul_zero, add_zero]

theorem affineEffectFullness_hasZero (D : OperationalData)
    (hfull : AffineEffectFullness D) : HasZeroOperationalEffect D := by
  intro A
  obtain ⟨e, he⟩ := hfull A (fun _ => 0) (zero_affineProbability D A)
  exact ⟨e, he⟩

theorem trivialData_not_hasZeroOperationalEffect :
    ¬ HasZeroOperationalEffect trivialData := by
  intro h
  obtain ⟨e, he⟩ := h ()
  have hz := he ()
  change (1 : ℝ) = 0 at hz
  exact one_ne_zero hz

theorem trivialData_not_affineEffectFullness :
    ¬ AffineEffectFullness trivialData := by
  intro h
  exact trivialData_not_hasZeroOperationalEffect
    (affineEffectFullness_hasZero trivialData h)

theorem realization_hasZeroOperationalEffect {D : OperationalData}
    (r : QuantumRealization D) : HasZeroOperationalEffect D := by
  intro A
  refine ⟨(r.effects A).symm (zeroEffect (r.dim A)), ?_⟩
  intro s
  rw [r.probabilities, Equiv.apply_symm_apply]
  change (tr ((r.states A s).val * (0 : Mat (r.dim A)))).re = 0
  rw [Matrix.mul_zero, tr, Matrix.trace_zero, Complex.zero_re]

theorem realization_hasTwoOperationalTests {D : OperationalData}
    (r : QuantumRealization D) : HasTwoOperationalTests D := by
  intro A
  refine ⟨(r.effects A).symm (zeroEffect (r.dim A)),
    (r.effects A).symm (unitEffect (r.dim A)), ?_⟩
  intro h
  exact zeroEffect_ne_unitEffect (r.dimension_positive A)
    ((r.effects A).symm.injective h)

theorem quantumData_hasZeroOperationalEffect :
    HasZeroOperationalEffect quantumData :=
  realization_hasZeroOperationalEffect quantumData_realization

theorem quantumData_hasTwoOperationalTests :
    HasTwoOperationalTests quantumData :=
  realization_hasTwoOperationalTests quantumData_realization

/-! Fullness and extensionality identify tests with bounded affine probability maps.
The equivalence is defined using only operational states, tests, mixtures and probabilities. -/

def TestExtensionality (D : OperationalData) : Prop :=
  ∀ (A : D.Obj) (e f : D.Test A), (∀ s, D.prob e s = D.prob f s) → e = f

def AffineTestSpace (D : OperationalData) (A : D.Obj) :=
  {f : D.State A → ℝ // AffineProbability D A f}

def affineTestMap (D : OperationalData) (hL : OperationalLaws D) (A : D.Obj) :
    D.Test A → AffineTestSpace D A :=
  fun e => ⟨(fun s => D.prob e s), ⟨(fun s => hL.2.1 A s e),
    (fun s t p hp0 hp1 => hL.2.2.2.2.1 A s t p hp0 hp1 e)⟩⟩

theorem affineTestMap_injective (D : OperationalData) (hL : OperationalLaws D)
    (hext : TestExtensionality D) (A : D.Obj) :
    Function.Injective (affineTestMap D hL A) := by
  intro e f hef
  apply hext A e f
  intro s
  exact congrFun (congrArg Subtype.val hef) s

theorem affineTestMap_surjective (D : OperationalData) (hL : OperationalLaws D)
    (hfull : AffineEffectFullness D) (A : D.Obj) :
    Function.Surjective (affineTestMap D hL A) := by
  rintro ⟨f, hf⟩
  obtain ⟨e, he⟩ := hfull A f hf
  refine ⟨e, Subtype.ext ?_⟩
  funext s
  exact he s

noncomputable def affineEffectEquiv (D : OperationalData) (hL : OperationalLaws D)
    (hfull : AffineEffectFullness D) (hext : TestExtensionality D)
    (A : D.Obj) : D.Test A ≃ AffineTestSpace D A :=
  Equiv.ofBijective (affineTestMap D hL A)
    ⟨affineTestMap_injective D hL hext A, affineTestMap_surjective D hL hfull A⟩

theorem quantumData_testExtensionality : TestExtensionality quantumData := by
  intro A e f he
  exact realization_effect_ext quantumData_realization A e f he

def TensorActRightLaws (D : OperationalData) : Prop :=
  ∀ (A B : D.Obj) (u : D.Process B B) (s : D.State (D.tensor A B)),
    D.actRight u s = D.act (D.parallel (D.ident A) u) s

theorem quantumData_tensorActRightLaws : TensorActRightLaws quantumData := by
  intro A B u s
  rfl

def DeterministicByStatistics (D : OperationalData) : Prop :=
  ∀ (A : D.Obj) (e : D.Test A), D.deterministicTest e ↔
    ∀ s, D.prob e s = 1

theorem quantumData_deterministicByStatistics : DeterministicByStatistics quantumData := by
  intro A e
  constructor
  · intro he s
    change (tr (s.val * e.val)).re = 1
    rw [he, Matrix.mul_one]
    change (Matrix.trace s.val).re = 1
    rw [density_trace, Complex.one_re]
  · intro he
    change e.val = 1
    have hx : e = unitEffect A.1 := by
      apply effect_ext_of_densities
      intro s
      have hs := he s
      change (tr (s.val * e.val)).re = 1 at hs
      change (tr (s.val * e.val)).re = (tr (s.val * (1 : Mat A.1))).re
      rw [Matrix.mul_one]
      change (tr (s.val * e.val)).re = (Matrix.trace s.val).re
      rw [density_trace, Complex.one_re]
      exact hs
    exact congrArg Subtype.val hx

end EffectPremises

/-! ## M5.4, part 1: affine probability functions on the densities are effects

An affine probability function on the densities extends to a positively homogeneous additive
function on the positive matrices, then to a real-linear functional on the Hermitian matrices,
and then, through the Hermitian and skew-Hermitian parts, to a complex-linear functional on all
matrices. That functional is positive, so its trace representer is a positive matrix; the bound
of the function by one places the representer below the unit matrix. The representer is the
effect whose trace pairing with each density is the given function.
-/

section AffineEffects

open OperatorKO7.Meta.Physics.BuschGleasonFinite (traceDual traceDual_represents)
open OperatorKO7.Meta.Physics.BuschGleasonConverse
  (rankOne rankOne_posSemidef trace_mul_rankOne IsPositiveFunctional quadraticForm_nonneg
    isHermitian_of_quadraticForm_nonneg)

variable {n : ℕ}

/-- A probability function on the densities that respects every convex mixture. -/
def DensityAffine (f : Density n → ℝ) : Prop :=
  (∀ ρ, 0 ≤ f ρ ∧ f ρ ≤ 1) ∧
  ∀ (ρ σ : Density n) (p : ℝ), 0 ≤ p → p ≤ 1 →
    f (densityMix p ρ σ) = p * f ρ + (1 - p) * f σ

/-- A positive matrix with positive trace, rescaled to a density. -/
def normalizeDensity (P : Mat n) (hP : P.PosSemidef) (ht : 0 < P.trace.re) : Density n :=
  ⟨(((P.trace.re)⁻¹ : ℝ) : ℂ) • P,
    (psd_iff_posSemidef _).mpr (posSemidef_real_smul hP (inv_nonneg.mpr ht.le)),
    by
      have hreal := posSemidef_trace_ofReal hP
      rw [tr, Matrix.trace_smul, smul_eq_mul]
      calc (((P.trace.re)⁻¹ : ℝ) : ℂ) * P.trace
          = (((P.trace.re)⁻¹ : ℝ) : ℂ) * ((P.trace.re : ℝ) : ℂ) := by rw [← hreal]
        _ = 1 := by rw [← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one]⟩

theorem normalizeDensity_val (P : Mat n) (hP : P.PosSemidef) (ht : 0 < P.trace.re) :
    (normalizeDensity P hP ht).val = (((P.trace.re)⁻¹ : ℝ) : ℂ) • P := rfl

theorem normalizeDensity_density (ρ : Density n) (hP : ρ.val.PosSemidef)
    (ht : 0 < ρ.val.trace.re) : normalizeDensity ρ.val hP ht = ρ := by
  apply Subtype.ext
  rw [normalizeDensity_val, density_trace, Complex.one_re, inv_one, Complex.ofReal_one, one_smul]

/-- The positively homogeneous extension of a density function to the positive matrices. -/
def coneValue (f : Density n → ℝ) (P : Mat n) : ℝ :=
  if h : P.PosSemidef ∧ 0 < P.trace.re then P.trace.re * f (normalizeDensity P h.1 h.2) else 0

theorem coneValue_of_pos (f : Density n → ℝ) {P : Mat n} (hP : P.PosSemidef)
    (ht : 0 < P.trace.re) : coneValue f P = P.trace.re * f (normalizeDensity P hP ht) := by
  rw [coneValue, dif_pos ⟨hP, ht⟩]

theorem coneValue_of_trace_zero (f : Density n → ℝ) {P : Mat n} (ht : P.trace.re = 0) :
    coneValue f P = 0 := by
  rw [coneValue, dif_neg (fun h => by linarith [h.2])]

theorem coneValue_zero (f : Density n → ℝ) : coneValue f (0 : Mat n) = 0 :=
  coneValue_of_trace_zero f (by rw [Matrix.trace_zero, Complex.zero_re])

theorem coneValue_density (f : Density n → ℝ) (ρ : Density n) : coneValue f ρ.val = f ρ := by
  have ht : 0 < ρ.val.trace.re := by
    rw [density_trace, Complex.one_re]
    exact one_pos
  rw [coneValue_of_pos f (density_posSemidef ρ) ht, normalizeDensity_density, density_trace,
    Complex.one_re, one_mul]

theorem coneValue_nonneg (f : Density n → ℝ) (hf : DensityAffine f) (P : Mat n) :
    0 ≤ coneValue f P := by
  unfold coneValue
  split
  · next h => exact mul_nonneg h.2.le (hf.1 _).1
  · exact le_rfl

theorem coneValue_le_trace (f : Density n → ℝ) (hf : DensityAffine f) {P : Mat n}
    (hP : P.PosSemidef) : coneValue f P ≤ P.trace.re := by
  unfold coneValue
  split
  · next h =>
      calc P.trace.re * f (normalizeDensity P h.1 h.2) ≤ P.trace.re * 1 :=
            mul_le_mul_of_nonneg_left (hf.1 _).2 h.2.le
        _ = P.trace.re := mul_one _
  · exact posSemidef_trace_re_nonneg hP

theorem coneValue_smul (f : Density n → ℝ) {P : Mat n} (hP : P.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) : coneValue f ((c : ℂ) • P) = c * coneValue f P := by
  have htr : ((c : ℂ) • P).trace.re = c * P.trace.re := by
    rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  rcases hc.lt_or_eq with hc' | hc'
  · rcases (posSemidef_trace_re_nonneg hP).lt_or_eq with ht | ht
    · have hcP := posSemidef_real_smul hP hc
      have ht' : 0 < ((c : ℂ) • P).trace.re := by
        rw [htr]
        exact mul_pos hc' ht
      have hc0 : c ≠ 0 := hc'.ne'
      have hN : normalizeDensity ((c : ℂ) • P) hcP ht' = normalizeDensity P hP ht := by
        apply Subtype.ext
        rw [normalizeDensity_val, normalizeDensity_val, htr, smul_smul, ← Complex.ofReal_mul,
          show (c * P.trace.re)⁻¹ * c = (P.trace.re)⁻¹ by
            rw [mul_inv, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc0, mul_one]]
      rw [coneValue_of_pos f hcP ht', coneValue_of_pos f hP ht, htr, hN, mul_assoc]
    · rw [coneValue_of_trace_zero f (by rw [htr, ← ht, mul_zero]),
        coneValue_of_trace_zero f ht.symm, mul_zero]
  · subst hc'
    rw [Complex.ofReal_zero, zero_smul, coneValue_zero, zero_mul]

theorem coneValue_add (f : Density n → ℝ) (hf : DensityAffine f) {P Q : Mat n}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    coneValue f (P + Q) = coneValue f P + coneValue f Q := by
  rcases (posSemidef_trace_re_nonneg hP).lt_or_eq with hp | hp
  · rcases (posSemidef_trace_re_nonneg hQ).lt_or_eq with hq | hq
    · have hPQ := hP.add hQ
      have htr : (P + Q).trace.re = P.trace.re + Q.trace.re := by
        rw [Matrix.trace_add, Complex.add_re]
      have ht : 0 < (P + Q).trace.re := by
        rw [htr]
        linarith
      obtain ⟨a, ha⟩ : ∃ a : ℝ, a = P.trace.re := ⟨_, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b : ℝ, b = Q.trace.re := ⟨_, rfl⟩
      have hab : 0 < a + b := by
        rw [ha, hb]
        linarith
      have ha0 : a ≠ 0 := by
        rw [ha]
        exact hp.ne'
      have hb0 : b ≠ 0 := by
        rw [hb]
        exact hq.ne'
      have hab0 : a + b ≠ 0 := hab.ne'
      have hp0 : 0 ≤ a / (a + b) := div_nonneg (by rw [ha]; exact hp.le) hab.le
      have hp1 : a / (a + b) ≤ 1 := (div_le_one hab).mpr (by rw [hb]; linarith)
      have c1 : a / (a + b) * a⁻¹ = (a + b)⁻¹ := by
        rw [div_mul_eq_mul_div, mul_inv_cancel₀ ha0, one_div]
      have hsub : (1 : ℝ) - a / (a + b) = b / (a + b) := by
        rw [eq_div_iff hab0, sub_mul, div_mul_cancel₀ a hab0]
        ring
      have c2 : (1 - a / (a + b)) * b⁻¹ = (a + b)⁻¹ := by
        rw [hsub, div_mul_eq_mul_div, mul_inv_cancel₀ hb0, one_div]
      have hmix : normalizeDensity (P + Q) hPQ ht =
          densityMix (a / (a + b)) (normalizeDensity P hP hp) (normalizeDensity Q hQ hq) := by
        apply Subtype.ext
        rw [densityMix_val hp0 hp1, normalizeDensity_val, normalizeDensity_val,
          normalizeDensity_val, htr, ← ha, ← hb, smul_smul, smul_smul, ← Complex.ofReal_mul,
          ← Complex.ofReal_mul, c1, c2, smul_add]
      rw [coneValue_of_pos f hPQ ht, coneValue_of_pos f hP hp, coneValue_of_pos f hQ hq, hmix,
        hf.2 _ _ _ hp0 hp1, htr, ← ha, ← hb, div_eq_mul_inv]
      have hu : (a + b) * (a + b)⁻¹ = 1 := mul_inv_cancel₀ hab0
      linear_combination
        (a * f (normalizeDensity P hP hp) - a * f (normalizeDensity Q hQ hq)) * hu
    · have hQ0 : Q = 0 := posSemidef_eq_zero_of_trace_re hQ hq.symm
      rw [hQ0, add_zero, coneValue_zero, add_zero]
  · have hP0 : P = 0 := posSemidef_eq_zero_of_trace_re hP hp.symm
    rw [hP0, zero_add, coneValue_zero, zero_add]

/-- A real shift that makes a Hermitian matrix positive: the sum of its absolute eigenvalues. -/
def hermShift (H : Mat n) : ℝ :=
  if h : H.IsHermitian then ∑ i, |h.eigenvalues i| else 0

theorem hermShift_nonneg (H : Mat n) : 0 ≤ hermShift H := by
  unfold hermShift
  split
  · exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  · exact le_rfl

theorem posSemidef_add_hermShift {H : Mat n} (hH : H.IsHermitian) :
    (H + ((hermShift H : ℝ) : ℂ) • 1).PosSemidef := by
  have hs : hermShift H = ∑ i, |hH.eigenvalues i| := by
    rw [hermShift, dif_pos hH]
  have he : H + ((hermShift H : ℝ) : ℂ) • 1 =
      Thermal.spectralLift hH.eigenvectorUnitary (hH.eigenvalues - fun _ => -hermShift H) := by
    rw [spectralLift_sub, spectralLift_const, Thermal.spectralLift_eigenvalues hH,
      Complex.ofReal_neg, neg_smul, sub_neg_eq_add]
  rw [he]
  apply spectralLift_posSemidef
  intro i
  have h1 : |hH.eigenvalues i| ≤ hermShift H := by
    rw [hs]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (hH.eigenvalues j)) (Finset.mem_univ i)
  have h2 := neg_abs_le (hH.eigenvalues i)
  simp only [Pi.sub_apply]
  linarith

/-- The extension of a density function to the Hermitian matrices. -/
def hermValue (f : Density n → ℝ) (H : Mat n) : ℝ :=
  coneValue f (H + ((hermShift H : ℝ) : ℂ) • 1) - coneValue f (((hermShift H : ℝ) : ℂ) • 1)

/-- Every positive shift computes the same Hermitian extension. -/
theorem hermValue_shift (f : Density n → ℝ) (hf : DensityAffine f) {H : Mat n}
    (hH : H.IsHermitian) {c : ℝ} (hc : 0 ≤ c) (hHc : (H + (c : ℂ) • 1).PosSemidef) :
    hermValue f H = coneValue f (H + (c : ℂ) • 1) - coneValue f ((c : ℂ) • 1) := by
  have hA := posSemidef_add_hermShift hH
  have hs := hermShift_nonneg H
  have hS : (((hermShift H : ℝ) : ℂ) • (1 : Mat n)).PosSemidef :=
    posSemidef_real_smul Matrix.PosSemidef.one hs
  have hC : ((c : ℂ) • (1 : Mat n)).PosSemidef := posSemidef_real_smul Matrix.PosSemidef.one hc
  have h1 := coneValue_add f hf hA hC
  have h2 := coneValue_add f hf hHc hS
  have heq : H + ((hermShift H : ℝ) : ℂ) • 1 + (c : ℂ) • 1 =
      H + (c : ℂ) • 1 + ((hermShift H : ℝ) : ℂ) • 1 := by abel
  rw [heq] at h1
  unfold hermValue
  linarith

theorem hermValue_posSemidef (f : Density n → ℝ) (hf : DensityAffine f) {P : Mat n}
    (hP : P.PosSemidef) : hermValue f P = coneValue f P := by
  rw [hermValue_shift f hf hP.1 le_rfl (by rw [Complex.ofReal_zero, zero_smul, add_zero]; exact hP),
    Complex.ofReal_zero, zero_smul, add_zero, coneValue_zero, sub_zero]

theorem hermValue_zero (f : Density n → ℝ) (hf : DensityAffine f) :
    hermValue f (0 : Mat n) = 0 := by
  rw [hermValue_posSemidef f hf Matrix.PosSemidef.zero, coneValue_zero]

theorem hermValue_density (f : Density n → ℝ) (hf : DensityAffine f) (ρ : Density n) :
    hermValue f ρ.val = f ρ := by
  rw [hermValue_posSemidef f hf (density_posSemidef ρ), coneValue_density]

theorem hermValue_add (f : Density n → ℝ) (hf : DensityAffine f) {H K : Mat n}
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    hermValue f (H + K) = hermValue f H + hermValue f K := by
  have hs := hermShift_nonneg H
  have ht := hermShift_nonneg K
  have hA := posSemidef_add_hermShift hH
  have hB := posSemidef_add_hermShift hK
  have hsum : H + K + (((hermShift H + hermShift K : ℝ)) : ℂ) • 1 =
      (H + ((hermShift H : ℝ) : ℂ) • 1) + (K + ((hermShift K : ℝ) : ℂ) • 1) := by
    rw [Complex.ofReal_add, add_smul]
    abel
  have hpsd : (H + K + (((hermShift H + hermShift K : ℝ)) : ℂ) • 1).PosSemidef := by
    rw [hsum]
    exact hA.add hB
  have hone : (((hermShift H + hermShift K : ℝ)) : ℂ) • (1 : Mat n) =
      ((hermShift H : ℝ) : ℂ) • 1 + ((hermShift K : ℝ) : ℂ) • 1 := by
    rw [Complex.ofReal_add, add_smul]
  rw [hermValue_shift f hf (hH.add hK) (add_nonneg hs ht) hpsd, hsum, coneValue_add f hf hA hB,
    hone, coneValue_add f hf (posSemidef_real_smul Matrix.PosSemidef.one hs)
      (posSemidef_real_smul Matrix.PosSemidef.one ht)]
  unfold hermValue
  ring

theorem hermValue_smul_nonneg (f : Density n → ℝ) (hf : DensityAffine f) {H : Mat n}
    (hH : H.IsHermitian) {r : ℝ} (hr : 0 ≤ r) :
    hermValue f ((r : ℂ) • H) = r * hermValue f H := by
  have hs := hermShift_nonneg H
  have hA := posSemidef_add_hermShift hH
  have heq : (r : ℂ) • H + ((r * hermShift H : ℝ) : ℂ) • 1 =
      (r : ℂ) • (H + ((hermShift H : ℝ) : ℂ) • 1) := by
    rw [smul_add, Complex.ofReal_mul, smul_smul]
  have hpsd : ((r : ℂ) • H + ((r * hermShift H : ℝ) : ℂ) • 1).PosSemidef := by
    rw [heq]
    exact posSemidef_real_smul hA hr
  have hone : ((r * hermShift H : ℝ) : ℂ) • (1 : Mat n) =
      (r : ℂ) • (((hermShift H : ℝ) : ℂ) • 1) := by
    rw [Complex.ofReal_mul, smul_smul]
  rw [hermValue_shift f hf (hermitian_real_smul hH r) (mul_nonneg hr hs) hpsd, heq,
    coneValue_smul f hA hr, hone,
    coneValue_smul f (posSemidef_real_smul Matrix.PosSemidef.one hs) hr]
  unfold hermValue
  ring

theorem hermValue_neg (f : Density n → ℝ) (hf : DensityAffine f) {H : Mat n}
    (hH : H.IsHermitian) : hermValue f (-H) = -hermValue f H := by
  have h := hermValue_add f hf hH hH.neg
  rw [add_neg_cancel, hermValue_zero f hf] at h
  linarith

theorem hermValue_smul (f : Density n → ℝ) (hf : DensityAffine f) {H : Mat n}
    (hH : H.IsHermitian) (r : ℝ) : hermValue f ((r : ℂ) • H) = r * hermValue f H := by
  rcases le_or_gt 0 r with hr | hr
  · exact hermValue_smul_nonneg f hf hH hr
  · have he : (r : ℂ) • H = -(((-r : ℝ) : ℂ) • H) := by
      rw [Complex.ofReal_neg, neg_smul, neg_neg]
    rw [he, hermValue_neg f hf (hermitian_real_smul hH (-r)),
      hermValue_smul_nonneg f hf hH (by linarith)]
    ring

/-- The Hermitian part of a matrix. -/
def hpart (A : Mat n) : Mat n := ((1 / 2 : ℝ) : ℂ) • (A + Aᴴ)

/-- The Hermitian matrix whose multiple by the imaginary unit is the skew part. -/
def kpart (A : Mat n) : Mat n := ((1 / 2 : ℝ) : ℂ) • (Complex.I • (Aᴴ - A))

theorem hpart_hermitian (A : Mat n) : (hpart A).IsHermitian := by
  change (hpart A)ᴴ = hpart A
  rw [hpart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.conj_ofReal, add_comm]

theorem kpart_hermitian (A : Mat n) : (kpart A).IsHermitian := by
  change (kpart A)ᴴ = kpart A
  rw [kpart, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    neg_smul, ← smul_neg, neg_sub]

theorem hpart_add (A B : Mat n) : hpart (A + B) = hpart A + hpart B := by
  rw [hpart, hpart, hpart, Matrix.conjTranspose_add, ← smul_add]
  congr 1
  abel

theorem kpart_add (A B : Mat n) : kpart (A + B) = kpart A + kpart B := by
  rw [kpart, kpart, kpart, Matrix.conjTranspose_add, ← smul_add, ← smul_add]
  congr 2
  abel

theorem hpart_smul (c : ℂ) (A : Mat n) :
    hpart (c • A) = ((c.re : ℝ) : ℂ) • hpart A + ((-c.im : ℝ) : ℂ) • kpart A := by
  ext i j
  simp only [hpart, kpart, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, star_mul']
  conv_lhs => rw [← Complex.re_add_im c]
  simp only [star_add, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg]
  ring

theorem kpart_smul (c : ℂ) (A : Mat n) :
    kpart (c • A) = ((c.im : ℝ) : ℂ) • hpart A + ((c.re : ℝ) : ℂ) • kpart A := by
  ext i j
  simp only [hpart, kpart, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, star_mul']
  conv_lhs => rw [← Complex.re_add_im c]
  simp only [star_add, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  linear_combination
    (-(((c.im : ℝ) : ℂ)) * ((1 / 2 : ℝ) : ℂ) * (A i j + (starRingEnd ℂ) (A j i))) *
      Complex.I_sq

theorem hpart_of_hermitian {H : Mat n} (hH : H.IsHermitian) : hpart H = H := by
  rw [hpart, hH.eq, ← two_smul ℂ H, smul_smul,
    show ((1 / 2 : ℝ) : ℂ) * 2 = 1 by push_cast; norm_num, one_smul]

theorem kpart_of_hermitian {H : Mat n} (hH : H.IsHermitian) : kpart H = 0 := by
  rw [kpart, hH.eq, sub_self, smul_zero, smul_zero]

/-- The complex-linear extension of a density function to all matrices. -/
def affineFunctional (f : Density n → ℝ) (hf : DensityAffine f) : Mat n →ₗ[ℂ] ℂ where
  toFun A := (hermValue f (hpart A) : ℂ) + Complex.I * (hermValue f (kpart A) : ℂ)
  map_add' A B := by
    change (hermValue f (hpart (A + B)) : ℂ) + Complex.I * (hermValue f (kpart (A + B)) : ℂ) =
      ((hermValue f (hpart A) : ℂ) + Complex.I * (hermValue f (kpart A) : ℂ)) +
        ((hermValue f (hpart B) : ℂ) + Complex.I * (hermValue f (kpart B) : ℂ))
    rw [hpart_add, kpart_add, hermValue_add f hf (hpart_hermitian A) (hpart_hermitian B),
      hermValue_add f hf (kpart_hermitian A) (kpart_hermitian B)]
    push_cast
    ring
  map_smul' c A := by
    change (hermValue f (hpart (c • A)) : ℂ) + Complex.I * (hermValue f (kpart (c • A)) : ℂ) =
      c • ((hermValue f (hpart A) : ℂ) + Complex.I * (hermValue f (kpart A) : ℂ))
    rw [hpart_smul, kpart_smul,
      hermValue_add f hf (hermitian_real_smul (hpart_hermitian A) _)
        (hermitian_real_smul (kpart_hermitian A) _),
      hermValue_add f hf (hermitian_real_smul (hpart_hermitian A) _)
        (hermitian_real_smul (kpart_hermitian A) _),
      hermValue_smul f hf (hpart_hermitian A), hermValue_smul f hf (kpart_hermitian A),
      hermValue_smul f hf (hpart_hermitian A), hermValue_smul f hf (kpart_hermitian A)]
    rw [smul_eq_mul]
    conv_rhs => rw [← Complex.re_add_im c]
    push_cast
    linear_combination
      (-(((c.im : ℝ) : ℂ)) * ((hermValue f (kpart A) : ℝ) : ℂ)) * Complex.I_sq

theorem affineFunctional_hermitian (f : Density n → ℝ) (hf : DensityAffine f) {H : Mat n}
    (hH : H.IsHermitian) : affineFunctional f hf H = (hermValue f H : ℂ) := by
  change (hermValue f (hpart H) : ℂ) + Complex.I * (hermValue f (kpart H) : ℂ) = _
  rw [hpart_of_hermitian hH, kpart_of_hermitian hH, hermValue_zero f hf, Complex.ofReal_zero,
    mul_zero, add_zero]

theorem affineFunctional_positive (f : Density n → ℝ) (hf : DensityAffine f) :
    IsPositiveFunctional (affineFunctional f hf) := by
  intro P hP
  rw [affineFunctional_hermitian f hf hP.1, hermValue_posSemidef f hf hP]
  exact Complex.zero_le_real.mpr (coneValue_nonneg f hf P)

/-- The effect representing an affine probability function on the densities. -/
def affineEffectMatrix (f : Density n → ℝ) (hf : DensityAffine f) : Mat n :=
  traceDual (affineFunctional f hf)

theorem affineEffectMatrix_posSemidef (f : Density n → ℝ) (hf : DensityAffine f) :
    (affineEffectMatrix f hf).PosSemidef :=
  ⟨isHermitian_of_quadraticForm_nonneg _ (quadraticForm_nonneg (affineFunctional_positive f hf)),
    quadraticForm_nonneg (affineFunctional_positive f hf)⟩

theorem one_sub_affineEffectMatrix_posSemidef (f : Density n → ℝ) (hf : DensityAffine f) :
    (1 - affineEffectMatrix f hf).PosSemidef := by
  refine ⟨Matrix.isHermitian_one.sub (affineEffectMatrix_posSemidef f hf).1, fun x => ?_⟩
  have hr := rankOne_posSemidef x
  have hE := traceDual_represents (affineFunctional f hf) (rankOne x)
  rw [trace_mul_rankOne, affineFunctional_hermitian f hf hr.1,
    hermValue_posSemidef f hf hr] at hE
  have hone := trace_mul_rankOne (1 : Mat n) x
  rw [Matrix.one_mul, Matrix.one_mulVec, posSemidef_trace_ofReal hr] at hone
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
  change 0 ≤ star x ⬝ᵥ x - star x ⬝ᵥ (traceDual (affineFunctional f hf) *ᵥ x)
  rw [← hone, hE, ← Complex.ofReal_sub]
  exact Complex.zero_le_real.mpr (sub_nonneg.mpr (coneValue_le_trace f hf hr))

/-- Every affine probability function on the densities is the probability rule of an effect. -/
theorem densityAffine_effect (f : Density n → ℝ) (hf : DensityAffine f) :
    ∃ e : Effect n, ∀ ρ : Density n, (tr (ρ.val * e.val)).re = f ρ := by
  refine ⟨⟨affineEffectMatrix f hf,
    (psd_iff_posSemidef _).mpr (affineEffectMatrix_posSemidef f hf),
    (psd_iff_posSemidef _).mpr (one_sub_affineEffectMatrix_posSemidef f hf)⟩, fun ρ => ?_⟩
  change (tr (ρ.val * affineEffectMatrix f hf)).re = f ρ
  rw [tr, Matrix.trace_mul_comm, affineEffectMatrix, traceDual_represents,
    affineFunctional_hermitian f hf (density_hermitian ρ), hermValue_density f hf,
    Complex.ofReal_re]

/-- The quantum source satisfies affine effect fullness. -/
theorem quantumData_affineEffectFullness : AffineEffectFullness quantumData := by
  intro A f hf
  exact densityAffine_effect f hf

end AffineEffects

/-! ## M5.4, part 2: generalized probability measures on the effects are densities

A function on the effects that is nonnegative, takes the value one at the unit effect and adds
over every pair of effects whose sum is an effect is the probability rule of exactly one
density. Additivity gives rational homogeneity, monotonicity extends it to real scalars in the
unit interval, and the rescaled function is additive and positively homogeneous on the positive
matrices. The Hermitian and complex extensions then give a positive linear functional, and its
trace representer is the density. This is the extension lemma of Busch that
`OperatorKO7.Meta.Physics.BuschGleasonFinite` names as an open reduction. The operational form
is state fullness: every generalized probability measure on the tests of a system is a state.
-/

section BuschStates

open OperatorKO7.Meta.Physics.BuschGleasonFinite (traceDual traceDual_represents)
open OperatorKO7.Meta.Physics.BuschGleasonConverse
  (rankOne rankOne_posSemidef trace_mul_rankOne IsPositiveFunctional quadraticForm_nonneg
    isHermitian_of_quadraticForm_nonneg)

variable {n : ℕ}

/-- A nonnegative additive positively homogeneous function on the positive matrices. -/
def ConeAdditive (g : Mat n → ℝ) : Prop :=
  (∀ P : Mat n, P.PosSemidef → 0 ≤ g P) ∧
  (∀ P Q : Mat n, P.PosSemidef → Q.PosSemidef → g (P + Q) = g P + g Q) ∧
  ∀ (P : Mat n) (c : ℝ), P.PosSemidef → 0 ≤ c → g ((c : ℂ) • P) = c * g P

theorem ConeAdditive.map_zero {g : Mat n → ℝ} (hg : ConeAdditive g) : g 0 = 0 := by
  have h := hg.2.2 0 0 Matrix.PosSemidef.zero le_rfl
  rw [Complex.ofReal_zero, zero_smul, zero_mul] at h
  exact h

/-- The extension of a cone function to the Hermitian matrices. -/
def coneHerm (g : Mat n → ℝ) (H : Mat n) : ℝ :=
  g (H + ((hermShift H : ℝ) : ℂ) • 1) - g (((hermShift H : ℝ) : ℂ) • 1)

/-- Every positive shift computes the same Hermitian extension. -/
theorem coneHerm_shift {g : Mat n → ℝ} (hg : ConeAdditive g) {H : Mat n}
    (hH : H.IsHermitian) {c : ℝ} (hc : 0 ≤ c) (hHc : (H + (c : ℂ) • 1).PosSemidef) :
    coneHerm g H = g (H + (c : ℂ) • 1) - g ((c : ℂ) • 1) := by
  have hA := posSemidef_add_hermShift hH
  have hs := hermShift_nonneg H
  have hS : (((hermShift H : ℝ) : ℂ) • (1 : Mat n)).PosSemidef :=
    posSemidef_real_smul Matrix.PosSemidef.one hs
  have hC : ((c : ℂ) • (1 : Mat n)).PosSemidef := posSemidef_real_smul Matrix.PosSemidef.one hc
  have h1 := hg.2.1 _ _ hA hC
  have h2 := hg.2.1 _ _ hHc hS
  have heq : H + ((hermShift H : ℝ) : ℂ) • 1 + (c : ℂ) • 1 =
      H + (c : ℂ) • 1 + ((hermShift H : ℝ) : ℂ) • 1 := by abel
  rw [heq] at h1
  unfold coneHerm
  linarith

theorem coneHerm_posSemidef {g : Mat n → ℝ} (hg : ConeAdditive g) {P : Mat n}
    (hP : P.PosSemidef) : coneHerm g P = g P := by
  rw [coneHerm_shift hg hP.1 le_rfl (by rw [Complex.ofReal_zero, zero_smul, add_zero]; exact hP),
    Complex.ofReal_zero, zero_smul, add_zero, hg.map_zero, sub_zero]

theorem coneHerm_zero {g : Mat n → ℝ} (hg : ConeAdditive g) : coneHerm g (0 : Mat n) = 0 := by
  rw [coneHerm_posSemidef hg Matrix.PosSemidef.zero, hg.map_zero]

theorem coneHerm_add {g : Mat n → ℝ} (hg : ConeAdditive g) {H K : Mat n}
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    coneHerm g (H + K) = coneHerm g H + coneHerm g K := by
  have hs := hermShift_nonneg H
  have ht := hermShift_nonneg K
  have hA := posSemidef_add_hermShift hH
  have hB := posSemidef_add_hermShift hK
  have hsum : H + K + (((hermShift H + hermShift K : ℝ)) : ℂ) • 1 =
      (H + ((hermShift H : ℝ) : ℂ) • 1) + (K + ((hermShift K : ℝ) : ℂ) • 1) := by
    rw [Complex.ofReal_add, add_smul]
    abel
  have hpsd : (H + K + (((hermShift H + hermShift K : ℝ)) : ℂ) • 1).PosSemidef := by
    rw [hsum]
    exact hA.add hB
  have hone : (((hermShift H + hermShift K : ℝ)) : ℂ) • (1 : Mat n) =
      ((hermShift H : ℝ) : ℂ) • 1 + ((hermShift K : ℝ) : ℂ) • 1 := by
    rw [Complex.ofReal_add, add_smul]
  rw [coneHerm_shift hg (hH.add hK) (add_nonneg hs ht) hpsd, hsum, hg.2.1 _ _ hA hB, hone,
    hg.2.1 _ _ (posSemidef_real_smul Matrix.PosSemidef.one hs)
      (posSemidef_real_smul Matrix.PosSemidef.one ht)]
  unfold coneHerm
  ring

theorem coneHerm_smul_nonneg {g : Mat n → ℝ} (hg : ConeAdditive g) {H : Mat n}
    (hH : H.IsHermitian) {r : ℝ} (hr : 0 ≤ r) :
    coneHerm g ((r : ℂ) • H) = r * coneHerm g H := by
  have hs := hermShift_nonneg H
  have hA := posSemidef_add_hermShift hH
  have heq : (r : ℂ) • H + ((r * hermShift H : ℝ) : ℂ) • 1 =
      (r : ℂ) • (H + ((hermShift H : ℝ) : ℂ) • 1) := by
    rw [smul_add, Complex.ofReal_mul, smul_smul]
  have hpsd : ((r : ℂ) • H + ((r * hermShift H : ℝ) : ℂ) • 1).PosSemidef := by
    rw [heq]
    exact posSemidef_real_smul hA hr
  have hone : ((r * hermShift H : ℝ) : ℂ) • (1 : Mat n) =
      (r : ℂ) • (((hermShift H : ℝ) : ℂ) • 1) := by
    rw [Complex.ofReal_mul, smul_smul]
  rw [coneHerm_shift hg (hermitian_real_smul hH r) (mul_nonneg hr hs) hpsd, heq,
    hg.2.2 _ _ hA hr, hone, hg.2.2 _ _ (posSemidef_real_smul Matrix.PosSemidef.one hs) hr]
  unfold coneHerm
  ring

theorem coneHerm_neg {g : Mat n → ℝ} (hg : ConeAdditive g) {H : Mat n}
    (hH : H.IsHermitian) : coneHerm g (-H) = -coneHerm g H := by
  have h := coneHerm_add hg hH hH.neg
  rw [add_neg_cancel, coneHerm_zero hg] at h
  linarith

theorem coneHerm_smul {g : Mat n → ℝ} (hg : ConeAdditive g) {H : Mat n}
    (hH : H.IsHermitian) (r : ℝ) : coneHerm g ((r : ℂ) • H) = r * coneHerm g H := by
  rcases le_or_gt 0 r with hr | hr
  · exact coneHerm_smul_nonneg hg hH hr
  · have he : (r : ℂ) • H = -(((-r : ℝ) : ℂ) • H) := by
      rw [Complex.ofReal_neg, neg_smul, neg_neg]
    rw [he, coneHerm_neg hg (hermitian_real_smul hH (-r)),
      coneHerm_smul_nonneg hg hH (by linarith)]
    ring

/-- The complex-linear extension of a cone function to all matrices. -/
def coneFunctional (g : Mat n → ℝ) (hg : ConeAdditive g) : Mat n →ₗ[ℂ] ℂ where
  toFun A := (coneHerm g (hpart A) : ℂ) + Complex.I * (coneHerm g (kpart A) : ℂ)
  map_add' A B := by
    change (coneHerm g (hpart (A + B)) : ℂ) + Complex.I * (coneHerm g (kpart (A + B)) : ℂ) =
      ((coneHerm g (hpart A) : ℂ) + Complex.I * (coneHerm g (kpart A) : ℂ)) +
        ((coneHerm g (hpart B) : ℂ) + Complex.I * (coneHerm g (kpart B) : ℂ))
    rw [hpart_add, kpart_add, coneHerm_add hg (hpart_hermitian A) (hpart_hermitian B),
      coneHerm_add hg (kpart_hermitian A) (kpart_hermitian B)]
    push_cast
    ring
  map_smul' c A := by
    change (coneHerm g (hpart (c • A)) : ℂ) + Complex.I * (coneHerm g (kpart (c • A)) : ℂ) =
      c • ((coneHerm g (hpart A) : ℂ) + Complex.I * (coneHerm g (kpart A) : ℂ))
    rw [hpart_smul, kpart_smul,
      coneHerm_add hg (hermitian_real_smul (hpart_hermitian A) _)
        (hermitian_real_smul (kpart_hermitian A) _),
      coneHerm_add hg (hermitian_real_smul (hpart_hermitian A) _)
        (hermitian_real_smul (kpart_hermitian A) _),
      coneHerm_smul hg (hpart_hermitian A), coneHerm_smul hg (kpart_hermitian A),
      coneHerm_smul hg (hpart_hermitian A), coneHerm_smul hg (kpart_hermitian A)]
    rw [smul_eq_mul]
    conv_rhs => rw [← Complex.re_add_im c]
    push_cast
    linear_combination
      (-(((c.im : ℝ) : ℂ)) * ((coneHerm g (kpart A) : ℝ) : ℂ)) * Complex.I_sq

theorem coneFunctional_hermitian {g : Mat n → ℝ} (hg : ConeAdditive g) {H : Mat n}
    (hH : H.IsHermitian) : coneFunctional g hg H = (coneHerm g H : ℂ) := by
  change (coneHerm g (hpart H) : ℂ) + Complex.I * (coneHerm g (kpart H) : ℂ) = _
  rw [hpart_of_hermitian hH, kpart_of_hermitian hH, coneHerm_zero hg, Complex.ofReal_zero,
    mul_zero, add_zero]

theorem coneFunctional_posSemidef {g : Mat n → ℝ} (hg : ConeAdditive g) {P : Mat n}
    (hP : P.PosSemidef) : coneFunctional g hg P = (g P : ℂ) := by
  rw [coneFunctional_hermitian hg hP.1, coneHerm_posSemidef hg hP]

theorem coneFunctional_positive {g : Mat n → ℝ} (hg : ConeAdditive g) :
    IsPositiveFunctional (coneFunctional g hg) := by
  intro P hP
  rw [coneFunctional_posSemidef hg hP]
  exact Complex.zero_le_real.mpr (hg.1 P hP)

/-- The trace representer of a cone function is positive. -/
theorem traceDual_coneFunctional_posSemidef {g : Mat n → ℝ} (hg : ConeAdditive g) :
    (traceDual (coneFunctional g hg)).PosSemidef :=
  ⟨isHermitian_of_quadraticForm_nonneg _ (quadraticForm_nonneg (coneFunctional_positive hg)),
    quadraticForm_nonneg (coneFunctional_positive hg)⟩

/-- A matrix between the zero matrix and the unit matrix. -/
def IsEff (X : Mat n) : Prop := X.PosSemidef ∧ (1 - X).PosSemidef

/-- The effect carried by a matrix between the zero matrix and the unit matrix. -/
def mkEff (X : Mat n) (h : IsEff X) : Effect n :=
  ⟨X, (psd_iff_posSemidef _).mpr h.1, (psd_iff_posSemidef _).mpr h.2⟩

theorem effect_isEff (e : Effect n) : IsEff e.val :=
  ⟨effect_posSemidef e, effect_compl_posSemidef e⟩

/-- A generalized probability measure on the effects. -/
def EffectMeasure (μ : Effect n → ℝ) : Prop :=
  (∀ e, 0 ≤ μ e) ∧ μ (unitEffect n) = 1 ∧
  ∀ e f g : Effect n, g.val = e.val + f.val → μ g = μ e + μ f

/-- The measure read on matrices, with the value zero outside the effects. -/
def measureExt (μ : Effect n → ℝ) (X : Mat n) : ℝ :=
  if h : IsEff X then μ (mkEff X h) else 0

theorem measureExt_of_isEff (μ : Effect n → ℝ) {X : Mat n} (h : IsEff X) :
    measureExt μ X = μ (mkEff X h) := by
  rw [measureExt, dif_pos h]

theorem measureExt_effect (μ : Effect n → ℝ) (e : Effect n) : measureExt μ e.val = μ e := by
  rw [measureExt_of_isEff μ (effect_isEff e)]
  rfl

theorem measureExt_nonneg {μ : Effect n → ℝ} (hμ : EffectMeasure μ) (X : Mat n) :
    0 ≤ measureExt μ X := by
  unfold measureExt
  split
  · exact hμ.1 _
  · exact le_rfl

theorem measureExt_add {μ : Effect n → ℝ} (hμ : EffectMeasure μ) {X Y : Mat n}
    (hX : IsEff X) (hY : IsEff Y) (hXY : IsEff (X + Y)) :
    measureExt μ (X + Y) = measureExt μ X + measureExt μ Y := by
  rw [measureExt_of_isEff μ hX, measureExt_of_isEff μ hY, measureExt_of_isEff μ hXY]
  exact hμ.2.2 _ _ _ rfl

theorem isEff_zero : IsEff (0 : Mat n) :=
  ⟨Matrix.PosSemidef.zero, by rw [sub_zero]; exact Matrix.PosSemidef.one⟩

theorem isEff_one : IsEff (1 : Mat n) :=
  ⟨Matrix.PosSemidef.one, by rw [sub_self]; exact Matrix.PosSemidef.zero⟩

theorem measureExt_zero {μ : Effect n → ℝ} (hμ : EffectMeasure μ) :
    measureExt μ (0 : Mat n) = 0 := by
  have h := measureExt_add hμ isEff_zero isEff_zero (by rw [add_zero]; exact isEff_zero)
  rw [add_zero] at h
  linarith

theorem measureExt_one {μ : Effect n → ℝ} (hμ : EffectMeasure μ) :
    measureExt μ (1 : Mat n) = 1 := by
  rw [measureExt_of_isEff μ isEff_one]
  exact hμ.2.1

theorem measureExt_mono {μ : Effect n → ℝ} (hμ : EffectMeasure μ) {X Y : Mat n}
    (hX : IsEff X) (hY : IsEff Y) (hle : (Y - X).PosSemidef) :
    measureExt μ X ≤ measureExt μ Y := by
  have hd : IsEff (Y - X) := ⟨hle, by
    have h := hY.2.add hX.1
    rw [show 1 - Y + X = 1 - (Y - X) by abel] at h
    exact h⟩
  have hXY : X + (Y - X) = Y := by abel
  have h := measureExt_add hμ hX hd (by rw [hXY]; exact hY)
  rw [hXY] at h
  linarith [measureExt_nonneg hμ (Y - X)]

theorem measureExt_le_one {μ : Effect n → ℝ} (hμ : EffectMeasure μ) {X : Mat n}
    (hX : IsEff X) : measureExt μ X ≤ 1 := by
  rw [← measureExt_one hμ]
  exact measureExt_mono hμ hX isEff_one hX.2

theorem isEff_smul {X : Mat n} (hX : IsEff X) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    IsEff ((t : ℂ) • X) := by
  refine ⟨posSemidef_real_smul hX.1 h0, ?_⟩
  have h := (posSemidef_real_smul (Matrix.PosSemidef.one : (1 : Mat n).PosSemidef)
    (sub_nonneg.mpr h1)).add (posSemidef_real_smul hX.2 h0)
  have heq : ((1 - t : ℝ) : ℂ) • (1 : Mat n) + (t : ℂ) • (1 - X) = 1 - (t : ℂ) • X := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, smul_sub]
    abel
  rw [heq] at h
  exact h

/-- Additivity gives the value at every multiple `m / (k + 1)` up to the effect itself. -/
theorem measureExt_frac {μ : Effect n → ℝ} (hμ : EffectMeasure μ) {X : Mat n} (hX : IsEff X)
    (k : ℕ) : ∀ m : ℕ, m ≤ k + 1 →
      measureExt μ ((((m : ℝ) / (k + 1) : ℝ) : ℂ) • X) =
        m * measureExt μ ((((1 : ℝ) / (k + 1) : ℝ) : ℂ) • X) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  intro m
  induction m with
  | zero =>
    intro _
    rw [Nat.cast_zero, zero_div, Complex.ofReal_zero, zero_smul, measureExt_zero hμ, zero_mul]
  | succ m ih =>
    intro hm
    have hm' : (m : ℝ) + 1 ≤ k + 1 := by exact_mod_cast hm
    have h1 : (0 : ℝ) ≤ (m : ℝ) / (k + 1) := div_nonneg (Nat.cast_nonneg m) hk.le
    have h2 : (m : ℝ) / (k + 1) ≤ 1 := (div_le_one hk).mpr (by linarith)
    have h3 : (0 : ℝ) ≤ (1 : ℝ) / (k + 1) := div_nonneg zero_le_one hk.le
    have h4 : (1 : ℝ) / (k + 1) ≤ 1 := (div_le_one hk).mpr (by linarith)
    have h5 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) / (k + 1) := div_nonneg (Nat.cast_nonneg _) hk.le
    have h6 : ((m + 1 : ℕ) : ℝ) / (k + 1) ≤ 1 := (div_le_one hk).mpr (by push_cast; linarith)
    have hsc : (((m + 1 : ℕ) : ℝ) / (k + 1) : ℝ) = (m : ℝ) / (k + 1) + 1 / (k + 1) := by
      push_cast
      ring
    have hsplit : ((((m + 1 : ℕ) : ℝ) / (k + 1) : ℝ) : ℂ) • X =
        ((((m : ℝ) / (k + 1) : ℝ) : ℂ) • X) + ((((1 : ℝ) / (k + 1) : ℝ) : ℂ) • X) := by
      rw [hsc, Complex.ofReal_add, add_smul]
    rw [hsplit, measureExt_add hμ (isEff_smul hX h1 h2) (isEff_smul hX h3 h4)
      (by rw [← hsplit]; exact isEff_smul hX h5 h6), ih (by omega)]
    push_cast
    ring

/-- Rational homogeneity of the measure on an effect. -/
theorem measureExt_frac_eq {μ : Effect n → ℝ} (hμ : EffectMeasure μ) {X : Mat n}
    (hX : IsEff X) (k m : ℕ) (hm : m ≤ k + 1) :
    measureExt μ ((((m : ℝ) / (k + 1) : ℝ) : ℂ) • X) = (m : ℝ) / (k + 1) * measureExt μ X := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hfull := measureExt_frac hμ hX k (k + 1) le_rfl
  have hX1 : ((((k + 1 : ℕ) : ℝ) / (k + 1) : ℝ) : ℂ) • X = X := by
    rw [show (((k + 1 : ℕ) : ℝ) / (k + 1) : ℝ) = 1 by push_cast; exact div_self hk.ne',
      Complex.ofReal_one, one_smul]
  rw [hX1] at hfull
  rw [measureExt_frac hμ hX k m hm, hfull]
  push_cast
  rw [← mul_assoc, div_mul_cancel₀ _ hk.ne']

/-- Two reals within every reciprocal of a positive integer coincide. -/
theorem eq_of_abs_sub_le_inv_succ {a b : ℝ} (h : ∀ k : ℕ, |a - b| ≤ 1 / ((k : ℝ) + 1)) :
    a = b := by
  by_contra hne
  have hpos : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
  linarith [h k]

/-- The lower estimate of the measure of a scaled effect by a rational multiple. -/
theorem measureExt_smul_lower {μ : Effect n → ℝ} (hμ : EffectMeasure μ) {X : Mat n}
    (hX : IsEff X) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (k : ℕ) :
    t * measureExt μ X - 1 / ((k : ℝ) + 1) * measureExt μ X ≤ measureExt μ ((t : ℂ) • X) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌊t * (k + 1)⌋₊ := ⟨_, rfl⟩
  have hfl : (m : ℝ) ≤ t * (k + 1) := by
    rw [hm]
    exact Nat.floor_le (mul_nonneg h0 hk.le)
  have hlt : t * (k + 1) < m + 1 := by
    rw [hm]
    exact Nat.lt_floor_add_one _
  have hmk : m ≤ k + 1 := by
    have : (m : ℝ) ≤ k + 1 := by nlinarith
    exact_mod_cast this
  have hq0 : (0 : ℝ) ≤ (m : ℝ) / (k + 1) := div_nonneg (Nat.cast_nonneg m) hk.le
  have hqt : (m : ℝ) / (k + 1) ≤ t := (div_le_iff₀ hk).mpr hfl
  have hq1 : (m : ℝ) / (k + 1) ≤ 1 := le_trans hqt h1
  have hlow : t - 1 / ((k : ℝ) + 1) ≤ (m : ℝ) / (k + 1) := by
    rw [sub_le_iff_le_add, div_add_div_same, le_div_iff₀ hk]
    linarith
  have hmono := measureExt_mono hμ (isEff_smul hX hq0 hq1) (isEff_smul hX h0 h1)
    (by
      rw [← sub_smul, ← Complex.ofReal_sub]
      exact posSemidef_real_smul hX.1 (sub_nonneg.mpr hqt))
  rw [measureExt_frac_eq hμ hX k m hmk] at hmono
  have hM := measureExt_nonneg hμ X
  have hprod := mul_le_mul_of_nonneg_right hlow hM
  rw [sub_mul] at hprod
  linarith

/-- Real homogeneity of the measure on an effect, for scalars in the unit interval. -/
theorem measureExt_smul {μ : Effect n → ℝ} (hμ : EffectMeasure μ) {X : Mat n} (hX : IsEff X)
    {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    measureExt μ ((t : ℂ) • X) = t * measureExt μ X := by
  have hsum : (t : ℂ) • X + ((1 - t : ℝ) : ℂ) • X = X := by
    rw [← add_smul, ← Complex.ofReal_add, show t + (1 - t) = 1 by ring, Complex.ofReal_one,
      one_smul]
  have hadd := measureExt_add hμ (isEff_smul hX h0 h1)
    (isEff_smul hX (sub_nonneg.mpr h1) (by linarith)) (by rw [hsum]; exact hX)
  rw [hsum] at hadd
  have hM0 := measureExt_nonneg hμ X
  have hM1 := measureExt_le_one hμ hX
  apply eq_of_abs_sub_le_inv_succ
  intro k
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hl1 := measureExt_smul_lower hμ hX h0 h1 k
  have hl2 := measureExt_smul_lower hμ hX (sub_nonneg.mpr h1) (by linarith) k
  have e2 : (1 - t) * measureExt μ X = measureExt μ X - t * measureExt μ X := by ring
  have hq : 1 / ((k : ℝ) + 1) * measureExt μ X ≤ 1 / ((k : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left hM1 hk.le
    linarith
  have hq0 : 0 ≤ 1 / ((k : ℝ) + 1) * measureExt μ X := mul_nonneg hk.le hM0
  rw [abs_le]
  constructor <;> linarith

/-- The scale that brings a positive matrix below the unit matrix. -/
def effScale (P : Mat n) : ℝ := hermShift (-P) + 1

theorem effScale_pos (P : Mat n) : 0 < effScale P := by
  unfold effScale
  linarith [hermShift_nonneg (-P)]

theorem effScale_bound {P : Mat n} (hP : P.PosSemidef) :
    (((effScale P : ℝ) : ℂ) • (1 : Mat n) - P).PosSemidef := by
  have h := (posSemidef_add_hermShift hP.1.neg).add
    (Matrix.PosSemidef.one : (1 : Mat n).PosSemidef)
  have heq : -P + ((hermShift (-P) : ℝ) : ℂ) • 1 + 1 = ((effScale P : ℝ) : ℂ) • (1 : Mat n) - P := by
    rw [effScale, Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
    abel
  rw [heq] at h
  exact h

theorem isEff_inv_smul {P : Mat n} (hP : P.PosSemidef) {c : ℝ} (hc : 0 < c)
    (hle : ((c : ℂ) • (1 : Mat n) - P).PosSemidef) : IsEff (((c⁻¹ : ℝ) : ℂ) • P) := by
  refine ⟨posSemidef_real_smul hP (inv_nonneg.mpr hc.le), ?_⟩
  have heq : 1 - ((c⁻¹ : ℝ) : ℂ) • P = ((c⁻¹ : ℝ) : ℂ) • ((c : ℂ) • (1 : Mat n) - P) := by
    rw [smul_sub, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one,
      one_smul]
  rw [heq]
  exact posSemidef_real_smul hle (inv_nonneg.mpr hc.le)

/-- The rescaled measure of a positive matrix. -/
def conePart (μ : Effect n → ℝ) (P : Mat n) : ℝ :=
  effScale P * measureExt μ ((((effScale P)⁻¹ : ℝ) : ℂ) • P)

/-- Two admissible scales give the same rescaled measure. -/
theorem measureExt_scale_eq {μ : Effect n → ℝ} (hμ : EffectMeasure μ) {P : Mat n}
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hE : IsEff (((a⁻¹ : ℝ) : ℂ) • P)) :
    b * measureExt μ (((b⁻¹ : ℝ) : ℂ) • P) = a * measureExt μ (((a⁻¹ : ℝ) : ℂ) • P) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hb0 : b ≠ 0 := hb.ne'
  have hq0 : 0 ≤ a / b := div_nonneg ha.le hb.le
  have hq1 : a / b ≤ 1 := (div_le_one hb).mpr hab
  have heq : ((b⁻¹ : ℝ) : ℂ) • P = ((a / b : ℝ) : ℂ) • (((a⁻¹ : ℝ) : ℂ) • P) := by
    rw [smul_smul, ← Complex.ofReal_mul,
      show a / b * a⁻¹ = b⁻¹ by rw [div_mul_eq_mul_div, mul_inv_cancel₀ ha.ne', one_div]]
  have hba : b * (a / b) = a := by field_simp
  rw [heq, measureExt_smul hμ hE hq0 hq1, ← mul_assoc, hba]

/-- Every admissible scale computes the rescaled measure. -/
theorem conePart_eq {μ : Effect n → ℝ} (hμ : EffectMeasure μ) {P : Mat n} (hP : P.PosSemidef)
    {b : ℝ} (hb : 0 < b) (hE : IsEff (((b⁻¹ : ℝ) : ℂ) • P)) :
    conePart μ P = b * measureExt μ (((b⁻¹ : ℝ) : ℂ) • P) := by
  have hs := effScale_pos P
  have hEs := isEff_inv_smul hP hs (effScale_bound hP)
  unfold conePart
  rcases le_total (effScale P) b with h | h
  · exact (measureExt_scale_eq hμ hs h hEs).symm
  · exact measureExt_scale_eq hμ hb h hE

theorem conePart_coneAdditive {μ : Effect n → ℝ} (hμ : EffectMeasure μ) :
    ConeAdditive (conePart μ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro P _hP
    exact mul_nonneg (effScale_pos P).le (measureExt_nonneg hμ _)
  · intro P Q hP hQ
    have hsP := effScale_pos P
    have hsQ := effScale_pos Q
    have hc : 0 < effScale P + effScale Q := add_pos hsP hsQ
    have hBP := effScale_bound hP
    have hBQ := effScale_bound hQ
    have hle : ∀ {R : Mat n}, (((effScale P + effScale Q : ℝ) : ℂ) • (1 : Mat n) - R) =
        (((effScale P : ℝ) : ℂ) • 1 - P) + (((effScale Q : ℝ) : ℂ) • 1 - Q) + (P + Q - R) := by
      intro R
      rw [Complex.ofReal_add, add_smul]
      abel
    have hEP : IsEff ((((effScale P + effScale Q)⁻¹ : ℝ) : ℂ) • P) := by
      apply isEff_inv_smul hP hc
      rw [hle, show P + Q - P = Q by abel]
      exact (hBP.add hBQ).add hQ
    have hEQ : IsEff ((((effScale P + effScale Q)⁻¹ : ℝ) : ℂ) • Q) := by
      apply isEff_inv_smul hQ hc
      rw [hle, show P + Q - Q = P by abel]
      exact (hBP.add hBQ).add hP
    have hEPQ : IsEff ((((effScale P + effScale Q)⁻¹ : ℝ) : ℂ) • (P + Q)) := by
      apply isEff_inv_smul (hP.add hQ) hc
      rw [hle, sub_self, add_zero]
      exact hBP.add hBQ
    rw [conePart_eq hμ (hP.add hQ) hc hEPQ, conePart_eq hμ hP hc hEP, conePart_eq hμ hQ hc hEQ,
      smul_add, measureExt_add hμ hEP hEQ (by rw [← smul_add]; exact hEPQ)]
    ring
  · intro P c hP hc
    rcases hc.lt_or_eq with hc' | hc'
    · have hb : 0 < c * effScale P := mul_pos hc' (effScale_pos P)
      have hEs := isEff_inv_smul hP (effScale_pos P) (effScale_bound hP)
      have heq : ((((c * effScale P)⁻¹ : ℝ)) : ℂ) • ((c : ℂ) • P) =
          (((effScale P)⁻¹ : ℝ) : ℂ) • P := by
        rw [smul_smul, ← Complex.ofReal_mul,
          show (c * effScale P)⁻¹ * c = (effScale P)⁻¹ by
            rw [mul_inv, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc'.ne', mul_one]]
      rw [conePart_eq hμ (posSemidef_real_smul hP hc) hb (by rw [heq]; exact hEs), heq]
      unfold conePart
      ring
    · subst hc'
      rw [Complex.ofReal_zero, zero_smul, zero_mul]
      unfold conePart
      rw [smul_zero, measureExt_zero hμ, mul_zero]

theorem conePart_effect {μ : Effect n → ℝ} (hμ : EffectMeasure μ) {X : Mat n} (hX : IsEff X) :
    conePart μ X = measureExt μ X := by
  rw [conePart_eq hμ hX.1 one_pos (by rw [inv_one, Complex.ofReal_one, one_smul]; exact hX),
    inv_one, Complex.ofReal_one, one_smul, one_mul]

/-- The density representing a generalized probability measure on the effects. -/
def measureDensity (μ : Effect n → ℝ) (hμ : EffectMeasure μ) : Density n :=
  ⟨traceDual (coneFunctional (conePart μ) (conePart_coneAdditive hμ)),
    (psd_iff_posSemidef _).mpr (traceDual_coneFunctional_posSemidef _),
    by
      have h := traceDual_represents (coneFunctional (conePart μ) (conePart_coneAdditive hμ)) 1
      rw [Matrix.mul_one, coneFunctional_posSemidef _ Matrix.PosSemidef.one,
        conePart_effect hμ isEff_one, measureExt_one hμ, Complex.ofReal_one] at h
      exact h⟩

theorem measureDensity_represents (μ : Effect n → ℝ) (hμ : EffectMeasure μ) (e : Effect n) :
    (tr ((measureDensity μ hμ).val * e.val)).re = μ e := by
  change ((traceDual (coneFunctional (conePart μ) (conePart_coneAdditive hμ)) * e.val).trace).re
    = μ e
  rw [traceDual_represents, coneFunctional_posSemidef _ (effect_posSemidef e),
    conePart_effect hμ (effect_isEff e), measureExt_effect, Complex.ofReal_re]

/-- Busch's theorem in finite dimension: every generalized probability measure on the effects is
the probability rule of exactly one density. -/
theorem busch_density (μ : Effect n → ℝ) (hμ : EffectMeasure μ) :
    ∃! ρ : Density n, ∀ e : Effect n, (tr (ρ.val * e.val)).re = μ e := by
  refine ⟨measureDensity μ hμ, measureDensity_represents μ hμ, fun ρ hρ => ?_⟩
  apply density_ext_of_effects
  intro e
  rw [hρ e, measureDensity_represents]

/-- The probability rule of a density is a generalized probability measure on the effects. -/
theorem density_effectMeasure (ρ : Density n) :
    EffectMeasure (fun e : Effect n => (tr (ρ.val * e.val)).re) := by
  refine ⟨fun e => ?_, ?_, fun e f g hg => ?_⟩
  · exact (qprob_mem_unitInterval ρ e).1
  · change (tr (ρ.val * (1 : Mat n))).re = 1
    rw [Matrix.mul_one, tr, density_trace, Complex.one_re]
  · change (tr (ρ.val * g.val)).re = (tr (ρ.val * e.val)).re + (tr (ρ.val * f.val)).re
    rw [hg, Matrix.mul_add, tr, Matrix.trace_add, Complex.add_re]

/-- A generalized probability measure on the tests of a system. -/
def TestMeasure (D : OperationalData) (A : D.Obj) (μ : D.Test A → ℝ) : Prop :=
  (∀ e, 0 ≤ μ e) ∧ μ (D.unitTest A) = 1 ∧
  ∀ e f g : D.Test A, (∀ s, D.prob g s = D.prob e s + D.prob f s) → μ g = μ e + μ f

/-- Every generalized probability measure on the tests of a system is a state. -/
def StateFullness (D : OperationalData) : Prop :=
  ∀ (A : D.Obj) (μ : D.Test A → ℝ), TestMeasure D A μ → ∃ s : D.State A, ∀ e, D.prob e s = μ e

theorem quantumData_stateFullness : StateFullness quantumData := by
  intro A μ hμ
  have hm : EffectMeasure μ := by
    refine ⟨hμ.1, hμ.2.1, fun e f g hg => hμ.2.2 e f g (fun s => ?_)⟩
    change (tr (s.val * g.val)).re = (tr (s.val * e.val)).re + (tr (s.val * f.val)).re
    rw [hg, Matrix.mul_add, tr, Matrix.trace_add, Complex.add_re]
  obtain ⟨ρ, hρ, _⟩ := busch_density μ hm
  exact ⟨ρ, hρ⟩

/-- A lawful source with a quantum realization has every test measure as a state. -/
theorem realization_stateFullness {D : OperationalData} (hL : OperationalLaws D)
    (r : QuantumRealization D) : StateFullness D := by
  intro A μ hμ
  have hunit : (r.effects A).symm (unitEffect (r.dim A)) = D.unitTest A := by
    apply (r.effects A).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    rw [realization_unit_effect hL r A]
    rfl
  have hm : EffectMeasure (fun E : Effect (r.dim A) => μ ((r.effects A).symm E)) := by
    refine ⟨fun E => hμ.1 _, ?_, fun e f g hg => hμ.2.2 _ _ _ (fun s => ?_)⟩
    · change μ ((r.effects A).symm (unitEffect (r.dim A))) = 1
      rw [hunit]
      exact hμ.2.1
    · rw [r.probabilities, r.probabilities, r.probabilities, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply, hg, Matrix.mul_add, tr,
        Matrix.trace_add, Complex.add_re]
  obtain ⟨ρ, hρ, _⟩ := busch_density _ hm
  refine ⟨(r.states A).symm ρ, fun e => ?_⟩
  rw [realization_prob_symm r A ρ e, hρ, Equiv.symm_apply_apply]

end BuschStates

/-! ## M5.4, part 3: the strengthened operational framework

STATEMENT CHANGE. The specification leaves the framework of `ReconstructionFromFrameworkGoal`
as a parameter.
Old type: `ReconstructionFromFrameworkGoal (fun D => OperationalLaws D ∧ SelectionConditions D)`,
refuted by `minimalFramework_not_reconstruction`.
New type: `ReconstructionFromFrameworkGoal StrengthenedFramework`. The strengthened framework
adds test extensionality, affine effect fullness, state fullness, the statistical reading of
deterministic tests, the right action as the parallel process with the identity, the product law
of parallel processes and finite tomography, each stated with operational data alone. Its first and third
clauses are proved here for every source and for the finite quantum source.
-/

section StrengthenedFramework

/-- Parallel processes act on product states factor by factor, with multiplied weights. -/
def ParallelProductLaws (D : OperationalData) : Prop :=
  ∀ (A B C E : D.Obj) (f : D.Process A B) (g : D.Process C E) (s : D.State A)
    (t : D.State C),
    D.weight (D.parallel f g) (D.productState s t) = D.weight f s * D.weight g t ∧
    (0 < D.weight f s → 0 < D.weight g t →
      D.act (D.parallel f g) (D.productState s t) = D.productState (D.act f s) (D.act g t))

/-- Finitely many tests determine every state of each system. -/
def FiniteTomography (D : OperationalData) : Prop :=
  ∀ A : D.Obj, ∃ (ι : Type) (_ : Fintype ι) (T : ι → D.Test A),
    ∀ s t : D.State A, (∀ k, D.prob (T k) s = D.prob (T k) t) → s = t

/-- The strengthened framework of M5.4. -/
def StrengthenedFramework (D : OperationalData) : Prop :=
  OperationalLaws D ∧ SelectionConditions D ∧ TestExtensionality D ∧ AffineEffectFullness D ∧
    StateFullness D ∧ DeterministicByStatistics D ∧ TensorActRightLaws D ∧
    ParallelProductLaws D ∧ FiniteTomography D

/-- The normalized output of a positive-weight input is the rescaled image. -/
theorem normOut_val_of_pos {n m : ℕ} (L : Mat n →ₗ[ℂ] Mat m) (hcp : CompletelyPositive L)
    (hm : 0 < m) (ρ : Density n) (h : 0 < (tr (L ρ.val)).re) :
    (normOut L hcp hm ρ).val = ((((tr (L ρ.val)).re)⁻¹ : ℝ) : ℂ) • L ρ.val := by
  rw [normOut, dif_pos h]

/-- The parallel process of the quantum source acts factor by factor on product states. -/
theorem quantumData_parallelProductLaws : ParallelProductLaws quantumData := by
  intro A B C E f g s t
  have hpar : parMap f.map g.map (qpair A C) (qpair B E) (pairMatrix (qpair A C) s.val t.val) =
      pairMatrix (qpair B E) (f.map s.val) (g.map t.val) :=
    parMap_pairMatrix _ _ _ _ _ _
  have htf := posSemidef_trace_ofReal (cp_positive f.cp (density_posSemidef s))
  have htg := posSemidef_trace_ofReal (cp_positive g.cp (density_posSemidef t))
  have hw : (tr (parMap f.map g.map (qpair A C) (qpair B E)
      (pairMatrix (qpair A C) s.val t.val))).re =
      (tr (f.map s.val)).re * (tr (g.map t.val)).re := by
    rw [hpar, tr, pairMatrix_trace, htf, htg, ← Complex.ofReal_mul, Complex.ofReal_re]
  refine ⟨hw, fun hf hg => ?_⟩
  have hpos : 0 < (tr (parMap f.map g.map (qpair A C) (qpair B E)
      (pairMatrix (qpair A C) s.val t.val))).re := by
    rw [hw]
    exact mul_pos hf hg
  obtain ⟨wf, hwf⟩ : ∃ w : ℝ, w = (tr (f.map s.val)).re := ⟨_, rfl⟩
  obtain ⟨wg, hwg⟩ : ∃ w : ℝ, w = (tr (g.map t.val)).re := ⟨_, rfl⟩
  have hfs := f.out_spec s
  have hgt := g.out_spec t
  rw [← hwf] at hfs
  rw [← hwg] at hgt
  have hwf0 : 0 < wf := by
    rw [hwf]
    exact hf
  have hwg0 : 0 < wg := by
    rw [hwg]
    exact hg
  apply Subtype.ext
  change (normOut (parMap f.map g.map (qpair A C) (qpair B E))
    (parMap_cp f.cp g.cp (qpair A C) (qpair B E)) (qtensor B E).2
      (pairState (qpair A C) s t)).val = pairMatrix (qpair B E) (f.out s).val (g.out t).val
  rw [normOut_val_of_pos _ _ _ _ hpos]
  change ((((tr (parMap f.map g.map (qpair A C) (qpair B E)
      (pairMatrix (qpair A C) s.val t.val))).re)⁻¹ : ℝ) : ℂ) •
      parMap f.map g.map (qpair A C) (qpair B E) (pairMatrix (qpair A C) s.val t.val) = _
  rw [hw, hpar, ← hwf, ← hwg, hfs, hgt, pairMatrix_smul, smul_smul,
    show (((wf * wg)⁻¹ : ℝ) : ℂ) * ((wf : ℂ) * (wg : ℂ)) = 1 by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ (mul_pos hwf0 hwg0).ne',
        Complex.ofReal_one], one_smul]

/-- The coefficient of the second basis vector in the finite tomographic family. -/
def tomoCoeff : Bool → ℂ
  | false => 1
  | true => Complex.I

/-- The vectors `e_i + e_j` and `e_i + I e_j` of the finite tomographic family. -/
def tomoVec {n : ℕ} (k : Fin n × Fin n × Bool) : Fin n → ℂ :=
  Pi.single k.1 1 + Pi.single k.2.1 (tomoCoeff k.2.2)

theorem tomoVec_ne_zero {n : ℕ} (k : Fin n × Fin n × Bool) : tomoVec k ≠ 0 := by
  intro h
  have hk := congrFun h k.1
  rw [tomoVec, Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at hk
  by_cases hij : k.2.1 = k.1
  · rw [hij, Pi.single_eq_same] at hk
    have him := congrArg Complex.re hk
    cases hb : k.2.2
    · rw [hb] at him
      change ((1 : ℂ) + 1).re = (0 : ℂ).re at him
      norm_num at him
    · rw [hb] at him
      change ((1 : ℂ) + Complex.I).re = (0 : ℂ).re at him
      norm_num at him
  · rw [Pi.single_eq_of_ne (Ne.symm hij), add_zero] at hk
    exact one_ne_zero hk

theorem tomoVec_false {n : ℕ} (i j : Fin n) :
    tomoVec (i, j, false) = Pi.single i 1 + Pi.single j 1 := rfl

theorem tomoVec_true {n : ℕ} (i j : Fin n) :
    tomoVec (i, j, true) = Pi.single i 1 + Pi.single j Complex.I := rfl

/-- A Hermitian matrix whose quadratic form has zero real part on the finite family is zero. -/
theorem hermitian_eq_zero_of_tomo {n : ℕ} {Z : Mat n} (hZ : Z.IsHermitian)
    (h : ∀ k : Fin n × Fin n × Bool, (star (tomoVec k) ⬝ᵥ Z *ᵥ tomoVec k).re = 0) :
    Z = 0 := by
  have hsym : ∀ i j, Z j i = star (Z i j) := fun i j => (hZ.apply j i).symm
  have hdiag : ∀ i, Z i i = 0 := by
    intro i
    have hi := h (i, i, false)
    rw [tomoVec_false] at hi
    rw [OperatorKO7.Meta.Physics.BuschGleasonConverse.quadratic_pair] at hi
    simp only [star_one, one_mul, mul_one, Complex.add_re] at hi
    have hre : (Z i i).re = 0 := by linarith
    have him : (Z i i).im = 0 := by
      have hs := hsym i i
      have := congrArg Complex.im hs
      rw [Complex.star_def, Complex.conj_im] at this
      linarith
    exact Complex.ext hre him
  have hoff : ∀ i j, Z i j = 0 := by
    intro i j
    have h1 := h (i, j, false)
    have hI := h (i, j, true)
    rw [tomoVec_false] at h1
    rw [tomoVec_true] at hI
    rw [OperatorKO7.Meta.Physics.BuschGleasonConverse.quadratic_pair, hdiag i, hdiag j,
      hsym i j] at h1 hI
    simp only [star_one, one_mul, mul_one, mul_zero, zero_add, add_zero,
      Complex.add_re, Complex.star_def, Complex.conj_re] at h1
    simp only [mul_zero, zero_mul, zero_add, add_zero, Complex.add_re, Complex.mul_re,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.conj_I, Complex.I_re,
      Complex.I_im, Complex.neg_re, Complex.neg_im] at hI
    apply Complex.ext
    · rw [Complex.zero_re]
      linarith
    · rw [Complex.zero_im]
      linarith
  ext i j
  rw [hoff i j, Matrix.zero_apply]

/-- The finite family of normalized rays separates the densities. -/
theorem density_eq_of_tomo {n : ℕ} (s t : Density n)
    (h : ∀ k : Fin n × Fin n × Bool,
      (tr (s.val * normRay (tomoVec k))).re = (tr (t.val * normRay (tomoVec k))).re) :
    s = t := by
  apply Subtype.ext
  have hZ : (s.val - t.val).IsHermitian := (density_hermitian s).sub (density_hermitian t)
  have hforms : ∀ k, (star (tomoVec k) ⬝ᵥ (s.val - t.val) *ᵥ tomoVec k).re = 0 := by
    intro k
    have hk := h k
    rw [tr, tr, Matrix.trace_mul_comm, Matrix.trace_mul_comm t.val, re_trace_normRay_mul,
      re_trace_normRay_mul] at hk
    have hs := (sqLength_pos (tomoVec_ne_zero k)).ne'
    have hk' := mul_left_cancel₀ (inv_ne_zero hs) hk
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, hk', sub_self]
  exact sub_eq_zero.mp (hermitian_eq_zero_of_tomo hZ hforms)

/-- The quantum source is tomographically finite: the rays of the finite family suffice. -/
theorem quantumData_finiteTomography : FiniteTomography quantumData := by
  intro A
  refine ⟨Fin A.1 × Fin A.1 × Bool, inferInstance,
    fun k => rayEffect (tomoVec k) (tomoVec_ne_zero k), ?_⟩
  intro s t h
  exact density_eq_of_tomo s t h

/-- The finite quantum source satisfies every premise of the strengthened framework. -/
theorem quantumData_strengthenedFramework : StrengthenedFramework quantumData :=
  ⟨quantumData_operationalLaws, quantumData_selectionConditions, quantumData_testExtensionality,
    quantumData_affineEffectFullness, quantumData_stateFullness,
    quantumData_deterministicByStatistics, quantumData_tensorActRightLaws,
    quantumData_parallelProductLaws,
    quantumData_finiteTomography⟩

/-- First clause of the reconstruction goal for the strengthened framework. -/
theorem strengthenedFramework_lawsAndSelection :
    ∀ D, StrengthenedFramework D → OperationalLaws D ∧ SelectionConditions D :=
  fun _ h => ⟨h.1, h.2.1⟩

/-- Third clause of the reconstruction goal: a source of the framework with two pure states. -/
theorem strengthenedFramework_nonvacuous :
    ∃ D, StrengthenedFramework D ∧
      ∃ (A : D.Obj) (s t : D.State A), s ≠ t ∧ Pure D s ∧ Pure D t :=
  ⟨quantumData, quantumData_strengthenedFramework, quantumData_two_pure_states⟩

end StrengthenedFramework

/-! ## M5.4, part 4: the strengthened framework does not force a quantum realization

The finite quantum source restricted to the processes of unit weight on every density keeps
every state, test, mixture, product and conditioning of the quantum source, and every premise
of the strengthened framework transfers to it. It has no quantum realization: the zero map is
completely positive and trace-nonincreasing, so operation fullness would supply a process
whose image of a density is zero, while every process of the restricted source has unit
weight. The second clause of `ReconstructionFromFrameworkGoal StrengthenedFramework` is
therefore false; the missing premise is fullness of the trace-decreasing processes.
-/

section TracePreservingSource

/-- A completely positive map of unit weight on the densities preserves every trace. -/
theorem trace_preserving_of_densities {n m : ℕ} (L : Mat n →ₗ[ℂ] Mat m)
    (hcp : CompletelyPositive L) (h : ∀ ρ : Density n, (tr (L ρ.val)).re = 1) (X : Mat n) :
    (L X).trace = X.trace := by
  have hd : ∀ ρ : Density n, (L ρ.val).trace = ρ.val.trace := by
    intro ρ
    have h1 : (L ρ.val).trace.re = 1 := h ρ
    rw [posSemidef_trace_ofReal (cp_positive hcp (density_posSemidef ρ)), density_trace, h1,
      Complex.ofReal_one]
  have hz : ∀ v : Fin n → ℂ, (L (ray v)).trace - (ray v).trace = 0 := by
    intro v
    by_cases hv : v = 0
    · subst hv
      have hr : ray (0 : Fin n → ℂ) = 0 := by
        ext a b
        rw [ray_apply]
        simp only [Pi.zero_apply, zero_mul, Matrix.zero_apply]
      rw [hr, map_zero, Matrix.trace_zero, Matrix.trace_zero, sub_self]
    · rw [ray_eq_smul_normRay hv, map_smul, Matrix.trace_smul, Matrix.trace_smul]
      have h1 := hd (rayState v hv)
      change (L (normRay v)).trace = (normRay v).trace at h1
      rw [h1, sub_self]
  have hv := vanish_of_rays (fun A => (L A).trace - A.trace)
    (by
      intro a b
      simp only [map_add, Matrix.trace_add]
      ring)
    (by
      intro c a
      simp only [map_smul, Matrix.trace_smul, smul_eq_mul]
      ring)
    hz X
  exact sub_eq_zero.mp hv

/-- The trace of a parallel map of two trace-preserving maps is the trace of its input. -/
theorem trace_parMap_of_tp {n m k l N₁ N₂ : ℕ} (f : Mat n →ₗ[ℂ] Mat m) (g : Mat k →ₗ[ℂ] Mat l)
    (πi : Fin N₁ ≃ Fin n × Fin k) (πo : Fin N₂ ≃ Fin m × Fin l)
    (hf : ∀ X, (f X).trace = X.trace) (hg : ∀ X, (g X).trace = X.trace) (X : Mat N₁) :
    (parMap f g πi πo X).trace = X.trace := by
  have htr1 : (parMap f g πi πo X).trace = ∑ c, (f (innerL g πi c c X)).trace := by
    simp only [Matrix.trace, Matrix.diag]
    rw [sum_pair πo]
    simp only [parMap, LinearMap.coe_mk, AddHom.coe_mk, Equiv.apply_symm_apply]
    exact Finset.sum_comm
  have htr2 : (∑ c, (innerL g πi c c X).trace) = ∑ u, (g (blockL πi u u X)).trace := by
    simp only [Matrix.trace, Matrix.diag, innerL, LinearMap.coe_mk, AddHom.coe_mk]
    exact Finset.sum_comm
  have htr3 : (∑ u, (blockL πi u u X).trace) = X.trace := by
    simp only [Matrix.trace, Matrix.diag, blockL, LinearMap.coe_mk, AddHom.coe_mk]
    exact (sum_pair πi (fun p => X p p)).symm
  rw [htr1, Finset.sum_congr rfl (fun c _ => hf (innerL g πi c c X)), htr2,
    Finset.sum_congr rfl (fun u _ => hg (blockL πi u u X)), htr3]

/-- Processes of the quantum source with unit weight on every density. -/
abbrev TPProc (A B : QSys) := {f : QProc A.1 B.1 // ∀ ρ : Density A.1, (tr (f.map ρ.val)).re = 1}

def TPProc.ident (A : QSys) : TPProc A A :=
  ⟨QProc.ident A.1, fun ρ => by
    change (tr ρ.val).re = 1
    rw [density_tr, Complex.one_re]⟩

def TPProc.comp {A B C : QSys} (g : TPProc B C) (f : TPProc A B) : TPProc A C :=
  ⟨QProc.comp g.1 f.1, fun ρ => by
    have h := quantumData_operationalLaws.2.2.2.2.2.2.2.2 A B C f.1 g.1 ρ
    change (tr ((QProc.comp g.1 f.1).map ρ.val)).re =
      (tr (f.1.map ρ.val)).re * (tr (g.1.map (f.1.out ρ).val)).re at h
    rw [h, f.2 ρ, g.2 (f.1.out ρ), mul_one]⟩

def TPProc.par {A B C E : QSys} (f : TPProc A B) (g : TPProc C E) :
    TPProc (qtensor A C) (qtensor B E) :=
  ⟨QProc.par f.1 g.1 (qpair A C) (qpair B E) (qtensor B E).2, fun ρ => by
    change (parMap f.1.map g.1.map (qpair A C) (qpair B E) ρ.val).trace.re = 1
    rw [trace_parMap_of_tp _ _ _ _ (trace_preserving_of_densities _ f.1.cp f.2)
      (trace_preserving_of_densities _ g.1.cp g.2), density_trace, Complex.one_re]⟩

/-- The quantum source with its processes restricted to unit weight. -/
def tpData : OperationalData where
  Obj := QSys
  State A := Density A.1
  Test A := Effect A.1
  Process A B := TPProc A B
  tensor := qtensor
  prob e s := (tr (s.val * e.val)).re
  mix p s t := densityMix p s t
  act f s := f.1.out s
  weight f s := (tr (f.1.map s.val)).re
  ident A := TPProc.ident A
  compose g f := TPProc.comp g f
  unitTest A := unitEffect A.1
  deterministicTest e := e.val = 1
  jointTest := fun {A B} e f => pairEffect (qpair A B) e f
  productState := fun {A B} s t => pairState (qpair A B) s t
  parallel := fun f g => TPProc.par f g
  marginal := fun {A B} s => marginalState (qpair A B) s
  actRight := fun {A B} u s =>
    (QProc.par (QProc.ident A.1) u.1 (qpair A B) (qpair A B) (qtensor A B).2).out s
  condition := fun {A B} e s => conditionState (qpair A B) e s

theorem tpData_operationalLaws : OperationalLaws tpData := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := quantumData_operationalLaws
  exact ⟨h1, h2, h3, h4, h5, fun A s => h6 A s, fun A B C f g s => h7 A B C f.1 g.1 s,
    fun A B f s => h8 A B f.1 s, fun A B C f g s => h9 A B C f.1 g.1 s⟩

theorem tpData_idealCompression : IdealCompression tpData := by
  intro A s
  obtain ⟨B, enc, dec, henc, hdec, hrec, hsurj⟩ := quantumData_idealCompression A s
  exact ⟨B, ⟨enc, henc⟩, ⟨dec, hdec⟩, henc, hdec, hrec, hsurj⟩

theorem tpData_purification : Purification tpData := by
  obtain ⟨hex, huniq⟩ := quantumData_purification
  refine ⟨hex, ?_⟩
  intro A B s t hs ht hm
  obtain ⟨u, ⟨g, hw, hgu, hug⟩, hu⟩ := huniq A B s t hs ht hm
  exact ⟨⟨u, fun ρ => (hw ρ).1⟩, ⟨⟨g, fun ρ => (hw ρ).2⟩, hw, hgu, hug⟩, hu⟩

theorem tpData_selectionConditions : SelectionConditions tpData :=
  ⟨quantumData_causality, quantumData_perfectDistinguishability, tpData_idealCompression,
    quantumData_localTomography, quantumData_pureConditioning, tpData_purification⟩

theorem tpData_strengthenedFramework : StrengthenedFramework tpData :=
  ⟨tpData_operationalLaws, tpData_selectionConditions, quantumData_testExtensionality,
    quantumData_affineEffectFullness, quantumData_stateFullness,
    quantumData_deterministicByStatistics, fun _ _ _ _ => rfl,
    fun A B C E f g s t => quantumData_parallelProductLaws A B C E f.1 g.1 s t,
    quantumData_finiteTomography⟩

/-- The trace-nonincreasing zero map. -/
theorem tni_zero {n m : ℕ} : TraceNonIncreasing (0 : Mat n →ₗ[ℂ] Mat m) := by
  intro a ha
  rw [LinearMap.zero_apply]
  change (0 : Mat m).trace.re ≤ a.trace.re
  rw [Matrix.trace_zero, Complex.zero_re]
  exact posSemidef_trace_re_nonneg ((psd_iff_posSemidef a).mp ha)

/-- The restricted source has no quantum realization. -/
theorem tpData_no_realization (r : QuantumRealization tpData) : False := by
  let A : QSys := ⟨1, Nat.one_pos⟩
  obtain ⟨g, hg⟩ := r.operation_fullness A A 0 cp_zero tni_zero
  let s : tpData.State A := defaultDensity A.2
  have h := r.source_action A A g s
  rw [hg, LinearMap.zero_apply] at h
  have hw : tpData.weight g s = 1 := g.2 s
  rw [hw, Complex.ofReal_one, one_smul] at h
  have ht := density_trace (r.states A (tpData.act g s))
  rw [← h, Matrix.trace_zero] at ht
  exact zero_ne_one ht

/-- The strengthened framework of part 3 does not imply a quantum realization. -/
theorem strengthenedFramework_not_reconstruction :
    ¬ ReconstructionFromFrameworkGoal StrengthenedFramework := by
  rintro ⟨_, hreal, _⟩
  obtain ⟨r⟩ := hreal tpData tpData_strengthenedFramework
  exact tpData_no_realization r

end TracePreservingSource

/-! ## M5.4, part 5: each added premise against quantum realizability

Five of the seven premises that the strengthened framework adds hold in every lawful source with
a quantum realization: test extensionality, affine effect fullness, state fullness, the product
law of parallel processes and finite tomography. The other two fix data that a realization
leaves free, the deterministic-test predicate and the right action. Two modified quantum sources
carry a realization, the operational laws and the selection conditions, and each violates
exactly one of those two premises while keeping the other six.
-/

section PremiseNecessity

/-- A quantum realization forces test extensionality. -/
theorem realization_testExtensionality {D : OperationalData} (r : QuantumRealization D) :
    TestExtensionality D :=
  fun A e f h => realization_effect_ext r A e f h

/-- A lawful source with a quantum realization has every affine probability map as a test. -/
theorem realization_affineEffectFullness {D : OperationalData} (hL : OperationalLaws D)
    (r : QuantumRealization D) : AffineEffectFullness D := by
  intro A f hf
  have hmix : ∀ (ρ σ : Density (r.dim A)) (p : ℝ), 0 ≤ p → p ≤ 1 →
      (r.states A).symm (densityMix p ρ σ) =
        D.mix p ((r.states A).symm ρ) ((r.states A).symm σ) := by
    intro ρ σ p hp0 hp1
    apply (r.states A).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    rw [realization_mix hL r A _ _ p hp0 hp1, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      densityMix_val hp0 hp1]
  have hg : DensityAffine (fun ρ : Density (r.dim A) => f ((r.states A).symm ρ)) := by
    refine ⟨fun ρ => hf.1 _, ?_⟩
    intro ρ σ p hp0 hp1
    change f ((r.states A).symm (densityMix p ρ σ)) =
      p * f ((r.states A).symm ρ) + (1 - p) * f ((r.states A).symm σ)
    rw [hmix ρ σ p hp0 hp1]
    exact hf.2 _ _ p hp0 hp1
  obtain ⟨E, hE⟩ := densityAffine_effect _ hg
  have hE' : ∀ ρ : Density (r.dim A), (tr (ρ.val * E.val)).re = f ((r.states A).symm ρ) := hE
  refine ⟨(r.effects A).symm E, fun s => ?_⟩
  rw [r.probabilities, Equiv.apply_symm_apply, hE', Equiv.symm_apply_apply]

/-- A quantum realization forces finite tomography through the normalized rays. -/
theorem realization_finiteTomography {D : OperationalData} (r : QuantumRealization D) :
    FiniteTomography D := by
  intro A
  refine ⟨Fin (r.dim A) × Fin (r.dim A) × Bool, inferInstance,
    fun k => (r.effects A).symm (rayEffect (tomoVec k) (tomoVec_ne_zero k)), ?_⟩
  intro s t h
  apply (r.states A).injective
  apply density_eq_of_tomo
  intro k
  have hk := h k
  rw [r.probabilities, r.probabilities, Equiv.apply_symm_apply] at hk
  exact hk

/-- A quantum realization forces the product law of parallel processes. -/
theorem realization_parallelProductLaws {D : OperationalData} (r : QuantumRealization D) :
    ParallelProductLaws D := by
  intro A B C E f g s t
  have hstate : ∀ {X Y : D.Obj} (x : D.State X) (y : D.State Y),
      (r.states (D.tensor X Y) (D.productState x y)).val =
        pairMatrix (r.pairIndex X Y) (r.states X x).val (r.states Y y).val := by
    intro X Y x y
    ext i j
    exact r.product_states X Y x y i j
  have hpar : r.maps (D.tensor A C) (D.tensor B E) (D.parallel f g)
      (pairMatrix (r.pairIndex A C) (r.states A s).val (r.states C t).val) =
      pairMatrix (r.pairIndex B E) (r.maps A B f (r.states A s).val)
        (r.maps C E g (r.states C t).val) := by
    ext i j
    exact r.parallel_on_products A B C E f g _ _ i j
  have hsa := r.source_action (D.tensor A C) (D.tensor B E) (D.parallel f g)
    (D.productState s t)
  rw [hstate, hpar, r.source_action A B f s, r.source_action C E g t, pairMatrix_smul] at hsa
  have htr := congrArg Matrix.trace hsa
  simp only [Matrix.trace_smul, pairMatrix_trace, density_trace, smul_eq_mul, mul_one] at htr
  have hw : D.weight (D.parallel f g) (D.productState s t) = D.weight f s * D.weight g t := by
    have h' := htr.symm
    rw [← Complex.ofReal_mul] at h'
    exact Complex.ofReal_injective h'
  refine ⟨hw, fun hf hg => ?_⟩
  apply realization_states_val_injective r
  rw [hstate]
  have hpos : (0 : ℝ) < D.weight f s * D.weight g t := mul_pos hf hg
  rw [hw, ← Complex.ofReal_mul] at hsa
  exact (smul_right_injective (Mat (r.dim (D.tensor B E)))
    (Complex.ofReal_ne_zero.mpr hpos.ne') hsa).symm

/-- A source with its deterministic-test predicate and its right action replaced. -/
def withFreeData (D : OperationalData) (det : {A : D.Obj} → D.Test A → Prop)
    (ar : {A B : D.Obj} → D.Process B B → D.State (D.tensor A B) →
      D.State (D.tensor A B)) : OperationalData :=
  { D with deterministicTest := det, actRight := ar }

/-- A realization ignores the deterministic-test predicate and the right action. -/
def QuantumRealization.withFreeData {D : OperationalData} (r : QuantumRealization D)
    (det : {A : D.Obj} → D.Test A → Prop)
    (ar : {A B : D.Obj} → D.Process B B → D.State (D.tensor A B) →
      D.State (D.tensor A B)) : QuantumRealization (withFreeData D det ar) where
  dim := r.dim
  dimension_positive := r.dimension_positive
  states := r.states
  effects := r.effects
  probabilities := r.probabilities
  maps := r.maps
  positivity := r.positivity
  trace_bound := r.trace_bound
  source_action := r.source_action
  composition := r.composition
  operation_fullness := r.operation_fullness
  operation_faithfulness := r.operation_faithfulness
  pairIndex := r.pairIndex
  product_states := r.product_states
  product_effects := r.product_effects
  parallel_on_products := r.parallel_on_products

/-- The quantum source in which no test is declared deterministic. -/
def noDeterministicData : OperationalData :=
  withFreeData quantumData (fun _ => False) quantumData.actRight

theorem noDeterministicData_selectionConditions : SelectionConditions noDeterministicData :=
  ⟨fun _ _ he _ => (he : False).elim, quantumData_perfectDistinguishability,
    quantumData_idealCompression, quantumData_localTomography, quantumData_pureConditioning,
    quantumData_purification⟩

theorem noDeterministicData_realization : Nonempty (QuantumRealization noDeterministicData) :=
  ⟨quantumData_realization.withFreeData _ _⟩

theorem noDeterministicData_not_deterministicByStatistics :
    ¬ DeterministicByStatistics noDeterministicData := by
  intro h
  exact ((h ⟨1, Nat.one_pos⟩ (unitEffect 1)).mpr
    (fun s => quantumData_operationalLaws.2.2.1 ⟨1, Nat.one_pos⟩ s) : False)

/-- Deterministic tests read off statistics are independent of quantum realizability. -/
theorem deterministicByStatistics_not_forced :
    OperationalLaws noDeterministicData ∧ SelectionConditions noDeterministicData ∧
      Nonempty (QuantumRealization noDeterministicData) ∧
      TestExtensionality noDeterministicData ∧ AffineEffectFullness noDeterministicData ∧
      StateFullness noDeterministicData ∧ TensorActRightLaws noDeterministicData ∧ ParallelProductLaws noDeterministicData ∧
      FiniteTomography noDeterministicData ∧ ¬ DeterministicByStatistics noDeterministicData := by
  obtain ⟨r⟩ := noDeterministicData_realization
  exact ⟨quantumData_operationalLaws, noDeterministicData_selectionConditions, ⟨r⟩,
    realization_testExtensionality r,
    realization_affineEffectFullness quantumData_operationalLaws r,
    realization_stateFullness quantumData_operationalLaws r,
    fun _ _ _ _ => rfl, realization_parallelProductLaws r, realization_finiteTomography r,
    noDeterministicData_not_deterministicByStatistics⟩

/-- A parallel map with a zero second factor is zero. -/
theorem parMap_zero_right {n m k l N₁ N₂ : ℕ} (f : Mat n →ₗ[ℂ] Mat m)
    (πi : Fin N₁ ≃ Fin n × Fin k) (πo : Fin N₂ ≃ Fin m × Fin l) :
    parMap f (0 : Mat k →ₗ[ℂ] Mat l) πi πo = 0 := by
  have hin : ∀ c d : Fin l, innerL (0 : Mat k →ₗ[ℂ] Mat l) πi c d = 0 := by
    intro c d
    apply LinearMap.ext
    intro x
    ext u w
    rfl
  apply LinearMap.ext
  intro x
  ext i j
  change f (innerL 0 πi (πo i).2 (πo j).2 x) (πo i).1 (πo j).1 = 0
  rw [hin, LinearMap.zero_apply, map_zero, Matrix.zero_apply]

/-- The zero process of a quantum system. -/
def zeroProc {n : ℕ} (hn : 0 < n) : QProc n n := QProc.ofMap 0 cp_zero tni_zero hn

theorem zeroProc_not_reversible (B : QSys) :
    ¬ Reversible quantumData (zeroProc B.2 : quantumData.Process B B) := by
  rintro ⟨_, hw, _, _⟩
  have h := (hw (defaultDensity B.2)).1
  change (tr ((0 : Mat B.1 →ₗ[ℂ] Mat B.1) (defaultDensity B.2).val)).re = 1 at h
  rw [LinearMap.zero_apply, tr, Matrix.trace_zero, Complex.zero_re] at h
  exact zero_ne_one h

/-- The quantum source whose right action moves only by reversible processes. -/
def reversibleActRightData : OperationalData :=
  withFreeData quantumData quantumData.deterministicTest
    (fun {A _B} u s => if Reversible quantumData u then quantumData.actRight (A := A) u s else s)

theorem reversibleActRightData_purification : Purification reversibleActRightData := by
  obtain ⟨hex, huniq⟩ := quantumData_purification
  refine ⟨hex, ?_⟩
  intro A B s t hs ht hm
  obtain ⟨u, hu, hut⟩ := huniq A B s t hs ht hm
  refine ⟨u, hu, ?_⟩
  change (if Reversible quantumData u then quantumData.actRight (A := A) u s else s) = t
  rw [if_pos hu]
  exact hut

theorem reversibleActRightData_selectionConditions :
    SelectionConditions reversibleActRightData :=
  ⟨quantumData_causality, quantumData_perfectDistinguishability, quantumData_idealCompression,
    quantumData_localTomography, quantumData_pureConditioning,
    reversibleActRightData_purification⟩

theorem reversibleActRightData_realization :
    Nonempty (QuantumRealization reversibleActRightData) :=
  ⟨quantumData_realization.withFreeData _ _⟩

/-- In the quantum source a parallel process with the zero map outputs the basis density. -/
theorem quantumData_act_parallel_zero (A B : QSys) (s : Density (qtensor A B).1) :
    quantumData.act (quantumData.parallel (quantumData.ident A)
      (zeroProc B.2 : quantumData.Process B B)) s = defaultDensity (qtensor A B).2 := by
  change normOut (parMap (QProc.ident A.1).map (zeroProc B.2).map (qpair A B) (qpair A B))
    (parMap_cp (QProc.ident A.1).cp (zeroProc B.2).cp (qpair A B) (qpair A B))
    (qtensor A B).2 s = _
  have hz : parMap (QProc.ident A.1).map (zeroProc B.2).map (qpair A B) (qpair A B) = 0 :=
    parMap_zero_right _ _ _
  have hw : ¬ 0 < (tr (parMap (QProc.ident A.1).map (zeroProc B.2).map (qpair A B)
      (qpair A B) s.val)).re := by
    rw [hz, LinearMap.zero_apply, tr, Matrix.trace_zero, Complex.zero_re]
    exact lt_irrefl 0
  rw [normOut, dif_neg hw]

/-- Two basis ray densities at different indices differ. -/
theorem rayState_single_ne {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    rayState (Pi.single i (1 : ℂ)) (pi_single_ne_zero i) ≠
      rayState (Pi.single j (1 : ℂ)) (pi_single_ne_zero j) := by
  intro h
  have hent := congrArg (fun ρ : Density N => ρ.val j j) h
  change normRay (Pi.single i (1 : ℂ)) j j = normRay (Pi.single j (1 : ℂ)) j j at hent
  rw [normRay, normRay, Matrix.smul_apply, Matrix.smul_apply, ray_apply, ray_apply,
    Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_same, zero_mul, smul_zero, star_one, mul_one,
    smul_eq_mul, mul_one] at hent
  exact (Complex.ofReal_ne_zero.mpr (inv_ne_zero (sqLength_pos (pi_single_ne_zero j)).ne'))
    hent.symm

/-- The right-action law in the modified source would send every joint density to one. -/
theorem reversibleActRightData_tensorActRight_collapse
    (h : TensorActRightLaws reversibleActRightData) (A B : QSys) (s : Density (qtensor A B).1) :
    s = defaultDensity (qtensor A B).2 := by
  have h2 : (if Reversible quantumData (zeroProc B.2 : quantumData.Process B B) then
      quantumData.actRight (A := A) (zeroProc B.2 : quantumData.Process B B) s else s) =
      defaultDensity (qtensor A B).2 :=
    (h A B (zeroProc B.2) s).trans (quantumData_act_parallel_zero A B s)
  rw [if_neg (zeroProc_not_reversible B)] at h2
  exact h2

theorem reversibleActRightData_not_tensorActRightLaws :
    ¬ TensorActRightLaws reversibleActRightData := by
  intro h
  have hc := reversibleActRightData_tensorActRight_collapse h ⟨1, Nat.one_pos⟩ ⟨2, Nat.two_pos⟩
    (rayState (Pi.single ⟨1, Nat.one_lt_two⟩ (1 : ℂ)) (pi_single_ne_zero _))
  exact rayState_single_ne (fun h01 => absurd (congrArg Fin.val h01) (by decide)) hc

/-- The right action as a parallel process is independent of quantum realizability. -/
theorem tensorActRightLaws_not_forced :
    OperationalLaws reversibleActRightData ∧ SelectionConditions reversibleActRightData ∧
      Nonempty (QuantumRealization reversibleActRightData) ∧
      TestExtensionality reversibleActRightData ∧
      AffineEffectFullness reversibleActRightData ∧ StateFullness reversibleActRightData ∧
      DeterministicByStatistics reversibleActRightData ∧
      ParallelProductLaws reversibleActRightData ∧ FiniteTomography reversibleActRightData ∧
      ¬ TensorActRightLaws reversibleActRightData := by
  obtain ⟨r⟩ := reversibleActRightData_realization
  exact ⟨quantumData_operationalLaws, reversibleActRightData_selectionConditions, ⟨r⟩,
    realization_testExtensionality r,
    realization_affineEffectFullness quantumData_operationalLaws r,
    realization_stateFullness quantumData_operationalLaws r,
    quantumData_deterministicByStatistics, realization_parallelProductLaws r,
    realization_finiteTomography r, reversibleActRightData_not_tensorActRightLaws⟩

end PremiseNecessity

end QuantumPurity

end OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational
