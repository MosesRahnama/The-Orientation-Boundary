import Mathlib

namespace OperatorKO7.Meta.LiteratureReview

/-!
Remark rem:weighted-fiber states that a finite law supported exactly on one
record fiber defines a normalized diagonal bipartite state with both marginals
equal to the probability diagonal, entropy equal to its Shannon entropy, and
simultaneous permutation stabilizer equal to the fiber-preserving permutations
that preserve the law.

The carrier is Fin n, so all state and marginal formulas use finite sums and
finite complex matrices; infinite laws are outside this file's scope.
Entropies use natural logarithms and the matrix spectral functional calculus.
The action on the product basis is the coordinate realization of Uσ tensor Uσ.
Conditioning requires positive record mass; exact fiber support additionally
requires a nonzero original weight at every point of that fiber.
-/

namespace WeightedFiber

open scoped BigOperators
open Matrix

noncomputable section

variable {n : ℕ}

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev State (n : ℕ) := EuclideanSpace ℂ (Fin n × Fin n)

def IsLaw (p : Fin n → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

def realDiag (p : Fin n → ℝ) : Mat n :=
  Matrix.diagonal (fun x => (p x : ℂ))

lemma real_function_selfAdjoint (p : Fin n → ℝ) : IsSelfAdjoint p := by
  change star p = p
  funext x
  change star (p x) = p x
  simp

lemma realDiag_selfAdjoint (p : Fin n → ℝ) : IsSelfAdjoint (realDiag p) := by
  change (realDiag p).conjTranspose = realDiag p
  unfold realDiag
  rw [Matrix.diagonal_conjTranspose]
  apply congrArg (fun d : Fin n → ℂ => Matrix.diagonal d)
  funext x
  change star (p x : ℂ) = (p x : ℂ)
  simp

def realDiagHom (n : ℕ) : (Fin n → ℝ) →⋆ₐ[ℝ] Mat n where
  toFun := realDiag
  map_zero' := by
    ext i j
    simp [realDiag]
  map_one' := by
    ext i j
    by_cases h : i = j <;> simp [realDiag, Matrix.one_apply, h]
  map_add' p r := by
    unfold realDiag
    rw [Matrix.diagonal_add]
    apply congrArg (fun d : Fin n → ℂ => Matrix.diagonal d)
    funext i
    exact Complex.ofReal_add (p i) (r i)
  map_mul' p r := by
    unfold realDiag
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg (fun d : Fin n → ℂ => Matrix.diagonal d)
    funext i
    exact Complex.ofReal_mul (p i) (r i)
  commutes' r := by
    change Matrix.diagonal (fun _ : Fin n => (r : ℂ)) =
      algebraMap ℝ (Mat n) r
    rw [Matrix.algebraMap_eq_diagonal]
    rfl
  map_star' p := by
    change realDiag (star p) = star (realDiag p)
    rw [real_function_selfAdjoint p]
    exact (realDiag_selfAdjoint p).symm

lemma realDiagHom_continuous (n : ℕ) : Continuous (realDiagHom n) := by
  exact (realDiagHom n).toAlgHom.toLinearMap.continuous_of_finiteDimensional

lemma cfc_realDiag (f : ℝ → ℝ) (hf : Continuous f) (p : Fin n → ℝ) :
    cfc f (realDiag p) = realDiag (fun i => f (p i)) := by
  let a : Fin n → ℂ := fun i => (p i : ℂ)
  let φ : (Fin n → ℂ) →⋆ₐ[ℝ] Mat n :=
    { Matrix.diagonalAlgHom (R := ℝ) (n := Fin n) (α := ℂ) with
      map_star' := by
        intro d
        change Matrix.diagonal (star d) = (Matrix.diagonal d).conjTranspose
        exact (Matrix.diagonal_conjTranspose d).symm }
  have ha_entry : ∀ i : Fin n, IsSelfAdjoint (a i) := by
    intro i
    change star (p i : ℂ) = (p i : ℂ)
    simp
  have ha : IsSelfAdjoint a := by
    change star a = a
    funext i
    exact ha_entry i
  have hφ : Continuous φ :=
    φ.toAlgHom.toLinearMap.continuous_of_finiteDimensional
  have hp : cfc f a = fun i => (f (p i) : ℂ) := by
    rw [cfc_map_pi (S := ℝ) f a hf.continuousOn ha ha_entry]
    funext i
    change cfc f (algebraMap ℝ ℂ (p i)) =
      algebraMap ℝ ℂ (f (p i))
    exact cfc_algebraMap (A := ℂ) (p i) f
  have h := φ.map_cfc f a hf.continuousOn hφ ha (realDiag_selfAdjoint p)
  change Matrix.diagonal (cfc f a) = cfc f (realDiag p) at h
  rw [hp] at h
  exact h.symm

def shannon (p : Fin n → ℝ) : ℝ := ∑ x, Real.negMulLog (p x)

def matrixEntropy (ρ : Mat n) : ℝ :=
  (Matrix.trace (cfc Real.negMulLog ρ)).re

lemma trace_realDiag (p : Fin n → ℝ) :
    Matrix.trace (realDiag p) = ((∑ x, p x : ℝ) : ℂ) := by
  simp [realDiag, Matrix.trace, Matrix.diag]

lemma entropy_realDiag (p : Fin n → ℝ) :
    matrixEntropy (realDiag p) = shannon p := by
  rw [matrixEntropy, cfc_realDiag Real.negMulLog Real.continuous_negMulLog,
    trace_realDiag, Complex.ofReal_re]
  rfl

def amplitude (p : Fin n → ℝ) (x : Fin n) : ℂ :=
  (Real.sqrt (p x) : ℂ)

@[simp] lemma star_amplitude (p : Fin n → ℝ) (x : Fin n) :
    star (amplitude p x) = amplitude p x := by
  simp [amplitude]

lemma amplitude_sq (p : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x) (x : Fin n) :
    amplitude p x * amplitude p x = (p x : ℂ) := by
  unfold amplitude
  exact_mod_cast (Real.mul_self_sqrt (hp x))

def state (p : Fin n → ℝ) : State n :=
  WithLp.toLp 2 (fun z => if z.1 = z.2 then amplitude p z.1 else 0)

@[simp] lemma state_apply (p : Fin n → ℝ) (i j : Fin n) :
    state p (i, j) = if i = j then amplitude p i else 0 := rfl

lemma state_ext {v w : State n} (h : ∀ z, v z = w z) : v = w :=
  (WithLp.equiv 2 _).injective (funext h)

def pureDensity (ψ : State n) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun z w => ψ z * star (ψ w)

def partialLeft (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : Mat n :=
  fun i j => ∑ k, ρ (i, k) (j, k)

def partialRight (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : Mat n :=
  fun i j => ∑ k, ρ (k, i) (k, j)

def entanglementEntropy (ψ : State n) : ℝ :=
  matrixEntropy (partialLeft (pureDensity ψ))

lemma left_marginal (p : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    partialLeft (pureDensity (state p)) = realDiag p := by
  ext i j
  change (∑ k, state p (i, k) * star (state p (j, k))) = realDiag p i j
  by_cases hij : i = j
  · subst j
    rw [realDiag, Matrix.diagonal_apply_eq, Finset.sum_eq_single i]
    · simpa using amplitude_sq p hp i
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  · rw [realDiag, Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i = k
    · subst k
      simp [Ne.symm hij]
    · simp [hik]

lemma right_marginal (p : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    partialRight (pureDensity (state p)) = realDiag p := by
  ext i j
  change (∑ k, state p (k, i) * star (state p (k, j))) = realDiag p i j
  by_cases hij : i = j
  · subst j
    rw [realDiag, Matrix.diagonal_apply_eq, Finset.sum_eq_single i]
    · simpa using amplitude_sq p hp i
    · intro k _ hk
      simp [hk]
    · simp
  · rw [realDiag, Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i
    · subst k
      simp [hij]
    · simp [hki]

lemma trace_partialLeft
    (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    Matrix.trace (partialLeft ρ) = Matrix.trace ρ := by
  simp only [Matrix.trace, Matrix.diag, partialLeft, Fintype.sum_prod_type]

lemma trace_pureDensity (ψ : State n) :
    Matrix.trace (pureDensity ψ) = inner ℂ ψ ψ := by
  simp only [Matrix.trace, Matrix.diag, pureDensity, PiLp.inner_apply,
    RCLike.inner_apply, starRingEnd_apply]

lemma state_inner (p : Fin n → ℝ) (hp : IsLaw p) :
    inner ℂ (state p) (state p) = 1 := by
  rw [← trace_pureDensity, ← trace_partialLeft, left_marginal p hp.1,
    trace_realDiag, hp.2]
  norm_num

lemma state_normalized (p : Fin n → ℝ) (hp : IsLaw p) :
    ‖state p‖ = 1 := by
  have hs := norm_sq_eq_re_inner (𝕜 := ℂ) (state p)
  rw [state_inner p hp] at hs
  have hn := norm_nonneg (state p)
  norm_num at hs
  rcases hs with hs | hs
  · exact hs
  · linarith

lemma entanglement_entropy (p : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    entanglementEntropy (state p) = shannon p := by
  rw [entanglementEntropy, left_marginal p hp, entropy_realDiag]

lemma right_entropy (p : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    matrixEntropy (partialRight (pureDensity (state p))) = shannon p := by
  rw [right_marginal p hp, entropy_realDiag]

def permuteBoth (σ : Equiv.Perm (Fin n)) (ψ : State n) : State n :=
  WithLp.toLp 2 (fun z => ψ (σ.symm z.1, σ.symm z.2))

@[simp] lemma permuteBoth_apply (σ : Equiv.Perm (Fin n)) (ψ : State n)
    (i j : Fin n) :
    permuteBoth σ ψ (i, j) = ψ (σ.symm i, σ.symm j) := rfl

lemma permuteBoth_inverse (σ : Equiv.Perm (Fin n)) (ψ : State n) :
    permuteBoth σ.symm (permuteBoth σ ψ) = ψ := by
  apply state_ext
  rintro ⟨i, j⟩
  change ψ (σ.symm (σ i), σ.symm (σ j)) = ψ (i, j)
  exact congrArg (fun z : Fin n × Fin n => ψ z)
    (Prod.ext (σ.symm_apply_apply i) (σ.symm_apply_apply j))

lemma permuteBoth_inner (σ : Equiv.Perm (Fin n)) (u v : State n) :
    inner ℂ (permuteBoth σ u) (permuteBoth σ v) = inner ℂ u v := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change (∑ z : Fin n × Fin n,
    inner ℂ (u (σ.symm z.1, σ.symm z.2)) (v (σ.symm z.1, σ.symm z.2))) =
      ∑ z : Fin n × Fin n, inner ℂ (u z) (v z)
  exact (Equiv.prodCongr σ.symm σ.symm).sum_comp
    (fun z : Fin n × Fin n => inner ℂ (u z) (v z))

lemma permutation_invariance (p : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x)
    (σ : Equiv.Perm (Fin n)) :
    permuteBoth σ (state p) = state p ↔ ∀ x, p (σ x) = p x := by
  constructor
  · intro h x
    have he := congrArg (fun ψ : State n => (ψ (σ x, σ x)).re) h
    have hs : Real.sqrt (p x) = Real.sqrt (p (σ x)) := by
      simpa [amplitude] using he
    exact ((Real.sqrt_inj (hp x) (hp (σ x))).mp hs).symm
  · intro h
    apply state_ext
    rintro ⟨i, j⟩
    have hp' : p (σ.symm i) = p i := by
      simpa using (h (σ.symm i)).symm
    by_cases hij : i = j
    · subst j
      simp [amplitude, hp']
    · have hs : σ.symm i ≠ σ.symm j := by
        intro he
        exact hij (σ.symm.injective he)
      simp [hij, hs]

variable {Y : Type*}

def FiberSupport (q : Fin n → Y) (y : Y) (p : Fin n → ℝ) : Prop :=
  ∀ x, p x ≠ 0 ↔ q x = y

lemma state_zero_outside (q : Fin n → Y) (y : Y) (p : Fin n → ℝ)
    (hs : FiberSupport q y p) (i j : Fin n) (hi : q i ≠ y) :
    state p (i, j) = 0 := by
  have hp : p i = 0 := by
    by_contra h
    exact hi ((hs i).1 h)
  simp [amplitude, hp]

lemma image_fiber_iff (q : Fin n → Y) (y : Y) (σ : Equiv.Perm (Fin n)) :
    σ '' {x | q x = y} = {x | q x = y} ↔
      ∀ x, q (σ x) = y ↔ q x = y := by
  constructor
  · intro h x
    constructor
    · intro hx
      have hm : σ x ∈ σ '' {z | q z = y} := by
        rw [h]
        exact hx
      rcases hm with ⟨z, hz, he⟩
      have hzx : z = x := σ.injective he
      simpa [hzx] using hz
    · intro hx
      have hm : σ x ∈ σ '' {z | q z = y} := ⟨x, hx, rfl⟩
      rw [h] at hm
      exact hm
  · intro h
    apply Set.ext
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h x).2 hx
    · intro hz
      refine' ⟨σ.symm z, _, by simp⟩
      apply (h (σ.symm z)).1
      simpa using hz

lemma fiber_stabilizer (q : Fin n → Y) (y : Y) (p : Fin n → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hs : FiberSupport q y p)
    (σ : Equiv.Perm (Fin n)) :
    permuteBoth σ (state p) = state p ↔
      σ '' {x | q x = y} = {x | q x = y} ∧
        ∀ x, q x = y → p (σ x) = p x := by
  rw [permutation_invariance p hp σ]
  constructor
  · intro h
    constructor
    · apply (image_fiber_iff q y σ).2
      intro x
      rw [← hs (σ x), ← hs x, h x]
    · intro x _
      exact h x
  · rintro ⟨himage, hweight⟩ x
    have hpres := (image_fiber_iff q y σ).1 himage
    by_cases hx : q x = y
    · exact hweight x hx
    · have hz : p x = 0 := by
        by_contra hn
        exact hx ((hs x).1 hn)
      have hσ : q (σ x) ≠ y := fun he => hx ((hpres x).1 he)
      have hzσ : p (σ x) = 0 := by
        by_contra hn
        exact hσ ((hs (σ x)).1 hn)
      rw [hz, hzσ]

variable [DecidableEq Y]

def fiber (q : Fin n → Y) (y : Y) : Finset (Fin n) :=
  Finset.univ.filter (fun x => q x = y)

lemma sum_const_fiber (q : Fin n → Y) (y : Y) (a : ℝ) :
    (∑ x : Fin n, if q x = y then a else 0) = ((fiber q y).card : ℝ) * a := by
  calc
    _ = ∑ x ∈ fiber q y, a := by
      unfold fiber
      rw [Finset.sum_filter]
    _ = _ := by simp [nsmul_eq_mul]

def uniform (q : Fin n → Y) (y : Y) (x : Fin n) : ℝ :=
  if q x = y then ((fiber q y).card : ℝ)⁻¹ else 0

lemma fiber_card_ne_zero (q : Fin n → Y) (y : Y) (hy : (fiber q y).Nonempty) :
    ((fiber q y).card : ℝ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Finset.card_pos.mpr hy))

lemma uniform_isLaw (q : Fin n → Y) (y : Y) (hy : (fiber q y).Nonempty) :
    IsLaw (uniform q y) := by
  constructor
  · intro x
    unfold uniform
    split_ifs <;> positivity
  · unfold uniform
    rw [sum_const_fiber]
    exact mul_inv_cancel₀ (fiber_card_ne_zero q y hy)

lemma uniform_support (q : Fin n → Y) (y : Y) (hy : (fiber q y).Nonempty) :
    FiberSupport q y (uniform q y) := by
  intro x
  by_cases hx : q x = y <;>
    simp [uniform, hx, fiber_card_ne_zero q y hy]

lemma uniform_entropy (q : Fin n → Y) (y : Y) (hy : (fiber q y).Nonempty) :
    shannon (uniform q y) = Real.log ((fiber q y).card : ℝ) := by
  have he : shannon (uniform q y) =
      ∑ x : Fin n, if q x = y then
        Real.negMulLog (((fiber q y).card : ℝ)⁻¹) else 0 := by
    unfold shannon uniform
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : q x = y <;> simp [hx]
  rw [he, sum_const_fiber]
  calc
    _ = (((fiber q y).card : ℝ) * ((fiber q y).card : ℝ)⁻¹) *
        Real.log ((fiber q y).card : ℝ) := by
      rw [Real.negMulLog, Real.log_inv]
      ring
    _ = _ := by rw [mul_inv_cancel₀ (fiber_card_ne_zero q y hy), one_mul]

lemma uniform_entanglement (q : Fin n → Y) (y : Y)
    (hy : (fiber q y).Nonempty) :
    entanglementEntropy (state (uniform q y)) = Real.log ((fiber q y).card : ℝ) := by
  rw [entanglement_entropy _ (uniform_isLaw q y hy).1, uniform_entropy q y hy]

lemma uniform_stabilizer (q : Fin n → Y) (y : Y)
    (hy : (fiber q y).Nonempty) (σ : Equiv.Perm (Fin n)) :
    permuteBoth σ (state (uniform q y)) = state (uniform q y) ↔
      σ '' {x | q x = y} = {x | q x = y} := by
  rw [fiber_stabilizer q y (uniform q y) (uniform_isLaw q y hy).1
    (uniform_support q y hy) σ]
  constructor
  · exact And.left
  · intro h
    refine' ⟨h, _⟩
    intro x hx
    have hσ : q (σ x) = y := ((image_fiber_iff q y σ).1 h x).2 hx
    simp [uniform, hx, hσ]

def recordMass (q : Fin n → Y) (y : Y) (p : Fin n → ℝ) : ℝ :=
  ∑ x, if q x = y then p x else 0

def conditional (q : Fin n → Y) (y : Y) (p : Fin n → ℝ) (x : Fin n) : ℝ :=
  (if q x = y then p x else 0) / recordMass q y p

def conditionalEntropy (q : Fin n → Y) (y : Y) (p : Fin n → ℝ) : ℝ :=
  ∑ x ∈ fiber q y, Real.negMulLog (p x / recordMass q y p)

lemma conditional_isLaw (q : Fin n → Y) (y : Y) (p : Fin n → ℝ)
    (hp : IsLaw p) (hy : 0 < recordMass q y p) :
    IsLaw (conditional q y p) := by
  constructor
  · intro x
    unfold conditional
    apply div_nonneg
    · by_cases hx : q x = y <;> simp [hx, hp.1 x]
    · exact hy.le
  · unfold conditional
    rw [← Finset.sum_div]
    change recordMass q y p / recordMass q y p = 1
    exact div_self (ne_of_gt hy)

lemma conditional_zero_outside (q : Fin n → Y) (y : Y) (p : Fin n → ℝ)
    (x : Fin n) (hx : q x ≠ y) : conditional q y p x = 0 := by
  simp [conditional, hx]

lemma conditional_shannon (q : Fin n → Y) (y : Y) (p : Fin n → ℝ) :
    shannon (conditional q y p) = conditionalEntropy q y p := by
  unfold shannon conditionalEntropy fiber
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : q x = y <;> simp [conditional, hx]

lemma conditional_support (q : Fin n → Y) (y : Y) (p : Fin n → ℝ)
    (hy : 0 < recordMass q y p) (hfull : ∀ x, q x = y → p x ≠ 0) :
    FiberSupport q y (conditional q y p) := by
  intro x
  by_cases hx : q x = y
  · have hn := div_ne_zero (hfull x hx) (ne_of_gt hy)
    simpa [conditional, hx] using hn
  · simp [conditional, hx]

theorem conditional_weighted_fiber (q : Fin n → Y) (y : Y) (p : Fin n → ℝ)
    (hp : IsLaw p) (hy : 0 < recordMass q y p) :
    ‖state (conditional q y p)‖ = 1 ∧
      partialLeft (pureDensity (state (conditional q y p))) =
        realDiag (conditional q y p) ∧
      partialRight (pureDensity (state (conditional q y p))) =
        realDiag (conditional q y p) ∧
      entanglementEntropy (state (conditional q y p)) =
        conditionalEntropy q y p := by
  have hc := conditional_isLaw q y p hp hy
  exact ⟨state_normalized _ hc, left_marginal _ hc.1, right_marginal _ hc.1,
    (entanglement_entropy _ hc.1).trans (conditional_shannon q y p)⟩

theorem conditional_stabilizer (q : Fin n → Y) (y : Y) (p : Fin n → ℝ)
    (hp : IsLaw p) (hy : 0 < recordMass q y p)
    (hfull : ∀ x, q x = y → p x ≠ 0) (σ : Equiv.Perm (Fin n)) :
    permuteBoth σ (state (conditional q y p)) = state (conditional q y p) ↔
      σ '' {x | q x = y} = {x | q x = y} ∧
        ∀ x, q x = y → conditional q y p (σ x) = conditional q y p x :=
  fiber_stabilizer q y _ (conditional_isLaw q y p hp hy).1
    (conditional_support q y p hy hfull) σ

def counterLaw (x : Fin 3) : ℝ := if x = 0 then 1 else 0
def counterRecord (x : Fin 3) : Bool := if x = 2 then true else false
def counterSwap : Equiv.Perm (Fin 3) := Equiv.swap 1 2

lemma counterLaw_isLaw : IsLaw counterLaw := by
  constructor
  · intro x
    unfold counterLaw
    split_ifs <;> norm_num
  · norm_num [counterLaw, Fin.sum_univ_succ]

lemma counterMass : recordMass counterRecord false counterLaw = 1 := by
  unfold recordMass counterRecord counterLaw
  rw [Fin.sum_univ_three]
  simp (config := { decide := true })

lemma counterConditional :
    conditional counterRecord false counterLaw = counterLaw := by
  funext x
  rw [conditional, counterMass]
  fin_cases x <;> norm_num [counterRecord, counterLaw, Fin.ext_iff]

lemma counter_invariant :
    permuteBoth counterSwap (state counterLaw) = state counterLaw := by
  apply (permutation_invariance counterLaw counterLaw_isLaw.1 counterSwap).2
  intro x
  fin_cases x <;>
    norm_num [counterLaw, counterSwap, Equiv.swap_apply_def, Fin.ext_iff]

lemma counter_not_fiber_preserving :
    counterSwap '' {x | counterRecord x = false} ≠
      {x | counterRecord x = false} := by
  intro h
  have hx : counterRecord (1 : Fin 3) = false := by
    norm_num [counterRecord, Fin.ext_iff]
  have hs := ((image_fiber_iff counterRecord false counterSwap).1 h (1 : Fin 3)).2 hx
  norm_num [counterRecord, counterSwap, Equiv.swap_apply_def, Fin.ext_iff] at hs

theorem conditional_support_counterexample :
    IsLaw counterLaw ∧ recordMass counterRecord false counterLaw = 1 ∧
      permuteBoth counterSwap (state (conditional counterRecord false counterLaw)) =
        state (conditional counterRecord false counterLaw) ∧
      counterSwap '' {x | counterRecord x = false} ≠
        {x | counterRecord x = false} := by
  simp only [counterConditional]
  exact ⟨counterLaw_isLaw, counterMass, counter_invariant, counter_not_fiber_preserving⟩

end

end WeightedFiber

open WeightedFiber in
theorem weighted_fiber {n : ℕ} {Y : Type*}
    (q : Fin n → Y) (y : Y) (p : Fin n → ℝ)
    (hp : IsLaw p) (hs : FiberSupport q y p) :
    ‖state p‖ = 1 ∧
      partialLeft (pureDensity (state p)) = realDiag p ∧
      partialRight (pureDensity (state p)) = realDiag p ∧
      entanglementEntropy (state p) = shannon p ∧
      matrixEntropy (partialRight (pureDensity (state p))) = shannon p ∧
      (∀ σ : Equiv.Perm (Fin n),
        permuteBoth σ (state p) = state p ↔
          σ '' {x | q x = y} = {x | q x = y} ∧
            ∀ x, q x = y → p (σ x) = p x) :=
  ⟨state_normalized p hp, left_marginal p hp.1, right_marginal p hp.1,
    entanglement_entropy p hp.1, right_entropy p hp.1,
    fun σ => fiber_stabilizer q y p hp.1 hs σ⟩

end OperatorKO7.Meta.LiteratureReview
