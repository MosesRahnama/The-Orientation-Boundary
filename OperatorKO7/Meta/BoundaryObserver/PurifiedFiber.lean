import OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction
import OperatorKO7.Meta.BoundaryObserver.BitDivision
import OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws
import OperatorKO7.Meta.BoundaryObserver.LandauDictionary
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.ClosureSwap
import OperatorKO7.Meta.BoundaryObserver.EntangledMergedPair
import OperatorKO7.Meta.BoundaryObserver.PairPurification

set_option autoImplicit false

open scoped Classical

/-! The amplitudes, density, marginal and spectral entropy of the purified fiber are finite
quantum objects. -/

noncomputable section

namespace OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

open scoped BigOperators ComplexOrder
open BoundaryReconstruction

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The uniform diagonal law on a finite subset, extended by zero. -/
def fiberWeight (C : Finset X) (x : X) : ℝ :=
  if x ∈ C then (C.card : ℝ)⁻¹ else 0

/-- The diagonal purification, with zero amplitude on the empty subset. -/
def purifiedFiber (C : Finset X) : X × X → ℂ :=
  fun z => if z.1 ∈ C ∧ z.1 = z.2 then
    (Real.sqrt ((C.card : ℝ)⁻¹) : ℂ) else 0

/-- The outer product of an amplitude and its actual adjoint. -/
def pureDensity {I : Type} (v : I → ℂ) : Matrix I I ℂ :=
  fun i j => v i * star (v j)

/-- Born mass is the sum of the squared complex amplitudes. -/
def bornMass {I : Type} [Fintype I] (v : I → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

theorem pureDensity_posSemidef {I : Type} [Fintype I] (v : I → ℂ) :
    (pureDensity v).PosSemidef := by
  let a : Matrix I Unit ℂ := fun i _ => v i
  have h : pureDensity v = a * a.conjTranspose := by
    ext i j
    simp [a, pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose a

theorem bornMass_eq_trace {I : Type} [Fintype I] (v : I → ℂ) :
    bornMass v = (pureDensity v).trace.re := by
  simp [bornMass, pureDensity, Matrix.trace, Complex.mul_conj]

theorem bornMass_nonneg {I : Type} [Fintype I] (v : I → ℂ) :
    0 ≤ bornMass v :=
  Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (v i))

omit [Fintype X] in
theorem purifiedFiber_empty : purifiedFiber (∅ : Finset X) = 0 := by
  funext z
  simp [purifiedFiber]

/-- The native partial trace is exactly the uniform diagonal marginal. -/
theorem marginal_purifiedFiber (C : Finset X) :
    Thermal.marginalLeft (pureDensity (purifiedFiber C)) =
      Thermal.realDiagonal (fiberWeight C) := by
  ext i j
  by_cases hij : i = j
  · subst j
    change (∑ r, purifiedFiber C (i, r) * star (purifiedFiber C (i, r))) =
      (Thermal.realDiagonal (fiberWeight C)) i i
    rw [Finset.sum_eq_single i]
    · by_cases hi : i ∈ C
      · have hn : 0 ≤ (C.card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
        have hv : purifiedFiber C (i, i) =
            (Real.sqrt ((C.card : ℝ)⁻¹) : ℂ) := if_pos ⟨hi, rfl⟩
        have hs : star (Real.sqrt ((C.card : ℝ)⁻¹) : ℂ) =
            (Real.sqrt ((C.card : ℝ)⁻¹) : ℂ) := Complex.conj_ofReal _
        simp only [hv, hs]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hn]
        simp [fiberWeight, Thermal.realDiagonal, hi]
      · simp [purifiedFiber, fiberWeight, Thermal.realDiagonal, hi]
    · intro r _ hri
      simp [purifiedFiber, Ne.symm hri]
    · simp
  · change (∑ r, purifiedFiber C (i, r) * star (purifiedFiber C (j, r))) =
      (Thermal.realDiagonal (fiberWeight C)) i j
    have hz : (∑ r, purifiedFiber C (i, r) * star (purifiedFiber C (j, r))) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      by_cases hir : i = r
      · subst r
        simp [purifiedFiber, Ne.symm hij]
      · simp [purifiedFiber, hir]
    rw [hz]
    simp [Thermal.realDiagonal, Matrix.diagonal, hij]

theorem sum_fiberWeight (C : Finset X) :
    (∑ x, fiberWeight C x) = (C.card : ℝ) * (C.card : ℝ)⁻¹ := by
  calc
    (∑ x, fiberWeight C x) = ∑ x ∈ C, fiberWeight C x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ C)
      intro x _ hx
      simp [fiberWeight, hx]
    _ = ∑ _x ∈ C, (C.card : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [fiberWeight, hx]
    _ = _ := by simp [nsmul_eq_mul]

theorem bornMass_purifiedFiber (C : Finset X) :
    bornMass (purifiedFiber C) = (C.card : ℝ) * (C.card : ℝ)⁻¹ := by
  rw [bornMass_eq_trace, ← Thermal.marginalLeft_trace, marginal_purifiedFiber]
  simpa [Thermal.realDiagonal, Matrix.trace_diagonal] using sum_fiberWeight C

theorem purifiedFiber_normalized (C : Finset X) (hC : C.Nonempty) :
    bornMass (purifiedFiber C) = 1 := by
  rw [bornMass_purifiedFiber]
  exact mul_inv_cancel₀ (by exact_mod_cast Finset.card_ne_zero.mpr hC)

theorem entropy_realDiagonal (p : X → ℝ) :
    Thermal.entropy (Thermal.realDiagonal p) = ∑ x, Real.negMulLog (p x) := by
  simpa [Thermal.spectralLift, Thermal.rotate] using
    Thermal.entropy_spectralLift (1 : Matrix.unitaryGroup X ℂ) p

theorem sum_negMulLog_fiberWeight (C : Finset X) :
    (∑ x, Real.negMulLog (fiberWeight C x)) =
      (C.card : ℝ) * Real.negMulLog ((C.card : ℝ)⁻¹) := by
  calc
    (∑ x, Real.negMulLog (fiberWeight C x)) =
        ∑ x ∈ C, Real.negMulLog (fiberWeight C x) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ C)
      intro x _ hx
      simp [fiberWeight, hx]
    _ = ∑ _x ∈ C, Real.negMulLog ((C.card : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [fiberWeight, hx]
    _ = _ := by simp [nsmul_eq_mul]

/-- The existing spectral entropy gives log card, also at card zero. -/
theorem entropy_marginal_purifiedFiber_all (C : Finset X) :
    Thermal.entropy (Thermal.marginalLeft (pureDensity (purifiedFiber C))) =
      Real.log C.card := by
  rw [marginal_purifiedFiber, entropy_realDiagonal, sum_negMulLog_fiberWeight]
  by_cases hC : C.card = 0
  · simp [hC]
  · have hn : (C.card : ℝ) ≠ 0 := by exact_mod_cast hC
    rw [Real.negMulLog, Real.log_inv]
    field_simp

/-- On a nonempty fiber `C`, the entropy of the marginal of the purified fiber is `log |C|`, in
natural logarithms. -/
theorem entropy_marginal_purifiedFiber (C : Finset X) (_hC : C.Nonempty) :
    Thermal.entropy (Thermal.marginalLeft (pureDensity (purifiedFiber C))) =
      Real.log C.card :=
  entropy_marginal_purifiedFiber_all C

theorem entropy_marginal_purifiedFiber_bits (C : Finset X) (hC : C.Nonempty) :
    Thermal.entropy (Thermal.marginalLeft (pureDensity (purifiedFiber C))) / Real.log 2 =
      Real.logb 2 C.card := by
  rw [entropy_marginal_purifiedFiber C hC]
  rfl

theorem empty_fiber_quantum_data :
    purifiedFiber (∅ : Finset X) = 0 ∧
      Thermal.marginalLeft (pureDensity (purifiedFiber (∅ : Finset X))) = 0 ∧
      Thermal.entropy (Thermal.marginalLeft
        (pureDensity (purifiedFiber (∅ : Finset X)))) = 0 := by
  refine ⟨purifiedFiber_empty, ?_, ?_⟩
  · simp [marginal_purifiedFiber, Thermal.realDiagonal, fiberWeight]
  · simp [entropy_marginal_purifiedFiber_all]

end OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

namespace OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

open scoped BigOperators ComplexOrder
open BoundaryReconstruction

theorem pureDensity_trace {I : Type} [Fintype I] (v : I → ℂ) :
    (pureDensity v).trace = (bornMass v : ℂ) := by
  simp [pureDensity, bornMass, Matrix.trace, Complex.mul_conj]

theorem purifiedFiber_density {X : Type} [Fintype X] [DecidableEq X]
    (C : Finset X) (hC : C.Nonempty) :
    (pureDensity (purifiedFiber C)).PosSemidef ∧
      (pureDensity (purifiedFiber C)).trace = 1 := by
  refine ⟨pureDensity_posSemidef _, ?_⟩
  rw [pureDensity_trace, purifiedFiber_normalized C hC]
  norm_num

theorem marginal_purifiedFiber_density {X : Type} [Fintype X] [DecidableEq X]
    (C : Finset X) (hC : C.Nonempty) :
    (Thermal.marginalLeft (pureDensity (purifiedFiber C))).PosSemidef ∧
      (Thermal.marginalLeft (pureDensity (purifiedFiber C))).trace = 1 := by
  refine ⟨Thermal.marginalLeft_posSemidef (purifiedFiber_density C hC).1, ?_⟩
  rw [Thermal.marginalLeft_trace]
  exact (purifiedFiber_density C hC).2

end OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

namespace OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

open scoped BigOperators ComplexOrder Kronecker
open BoundaryReconstruction
open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The actual observer fiber, including unattained records. -/
def fiber {Y : Type} (q : X → Y) (y : Y) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => q x = y)

omit [DecidableEq X] in
@[simp] theorem mem_fiber {Y : Type} (q : X → Y) (y : Y) (x : X) :
    x ∈ fiber q y ↔ q x = y := by
  classical
  simp [fiber]

/-- The basis permutation matrix with P_sigma e_x = e_(sigma x). -/
def permMatrix (σ : Equiv.Perm X) : Matrix X X ℂ :=
  fun i j => if j = σ.symm i then 1 else 0

/-- The same basis permutation acts on both registers. -/
def jointPerm (σ : Equiv.Perm X) (v : X × X → ℂ) : X × X → ℂ :=
  fun z => v (σ.symm z.1, σ.symm z.2)

/-- The coordinate action is the actual Kronecker matrix action. -/
theorem jointPerm_eq_matrix (σ : Equiv.Perm X) (v : X × X → ℂ) :
    jointPerm σ v = (permMatrix σ ⊗ₖ permMatrix σ).mulVec v := by
  funext z
  rcases z with ⟨i, j⟩
  simp [jointPerm, permMatrix, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, ite_mul]

omit [Fintype X] in
theorem purifiedFiber_diag_ne_zero_iff (C : Finset X) (x : X) :
    purifiedFiber C (x, x) ≠ 0 ↔ x ∈ C := by
  by_cases hx : x ∈ C
  · have hn : (0 : ℝ) < C.card := by
      exact_mod_cast Finset.card_pos.mpr (show C.Nonempty from ⟨x, hx⟩)
    have hs : Real.sqrt ((C.card : ℝ)⁻¹) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (inv_pos.mpr hn))
    simpa [purifiedFiber, hx] using hs
  · simp [purifiedFiber, hx]

omit [Fintype X] in
theorem purifiedFiber_injective :
    Function.Injective (purifiedFiber (X := X)) := by
  intro C D h
  apply Finset.ext
  intro x
  rw [← purifiedFiber_diag_ne_zero_iff C x, ← purifiedFiber_diag_ne_zero_iff D x]
  rw [h]

omit [Fintype X] in
theorem jointPerm_purifiedFiber (C : Finset X) (σ : Equiv.Perm X) :
    jointPerm σ (purifiedFiber C) = purifiedFiber (C.map σ.toEmbedding) := by
  funext z
  have hm : σ.symm z.1 ∈ C ↔ z.1 ∈ C.map σ.toEmbedding := by
    constructor
    · intro h
      exact Finset.mem_map.mpr ⟨σ.symm z.1, h, σ.apply_symm_apply z.1⟩
    · rintro h
      obtain ⟨x, hx, heq⟩ := Finset.mem_map.mp h
      have heq' : σ x = z.1 := heq
      simpa [← heq'] using hx
  have he : σ.symm z.1 = σ.symm z.2 ↔ z.1 = z.2 :=
    ⟨fun h => σ.symm.injective h, congrArg σ.symm⟩
  simp only [jointPerm, purifiedFiber, Finset.card_map, hm, he]

omit [Fintype X] in
/-- A permutation fixes the purified fiber of `C` if and only if it maps `C` onto itself; the
equivalence includes the empty fiber. -/
theorem jointPerm_fixes_iff (C : Finset X) (σ : Equiv.Perm X) :
    jointPerm σ (purifiedFiber C) = purifiedFiber C ↔ C.map σ.toEmbedding = C := by
  rw [jointPerm_purifiedFiber]
  exact ⟨fun h => purifiedFiber_injective h, congrArg purifiedFiber⟩

omit [DecidableEq X] in
theorem map_fiber_of_invisible {Y : Type} (q : X → Y) (σ : Equiv.Perm X)
    (hσ : σ ∈ licenseStabilizer q) (y : Y) :
    (fiber q y).map σ.toEmbedding = fiber q y := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_map.mp hx
    have hzx' : σ z = x := hzx
    rw [← hzx', mem_fiber]
    exact (hσ z).trans ((mem_fiber q y z).mp hz)
  · intro hx
    refine Finset.mem_map.mpr ⟨σ.symm x, ?_, σ.apply_symm_apply x⟩
    apply (mem_fiber q y _).mpr
    have hh := hσ (σ.symm x)
    rw [σ.apply_symm_apply] at hh
    exact hh.symm.trans ((mem_fiber q y x).mp hx)

theorem invisible_fixes_purifiedFiber {Y : Type} (q : X → Y) (σ : Equiv.Perm X)
    (hσ : σ ∈ licenseStabilizer q) (y : Y) :
    jointPerm σ (purifiedFiber (fiber q y)) = purifiedFiber (fiber q y) :=
  (jointPerm_fixes_iff (fiber q y) σ).2 (map_fiber_of_invisible q σ hσ y)

/-- The invisible permutations are exactly the simultaneous symmetries of all fiber states. -/
theorem invisible_iff_joint_fixes_fibers {Y : Type} (q : X → Y) (σ : Equiv.Perm X) :
    σ ∈ licenseStabilizer q ↔
      ∀ y, jointPerm σ (purifiedFiber (fiber q y)) = purifiedFiber (fiber q y) := by
  constructor
  · intro hσ y
    exact invisible_fixes_purifiedFiber q σ hσ y
  · intro h x
    have hm := (jointPerm_fixes_iff (fiber q (q x)) σ).mp (h (q x))
    have hx : σ x ∈ (fiber q (q x)).map σ.toEmbedding :=
      Finset.mem_map.mpr ⟨x, (mem_fiber q (q x) x).mpr rfl, rfl⟩
    rw [hm] at hx
    exact (mem_fiber q (q x) (σ x)).mp hx

end OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

namespace OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

open scoped BigOperators ComplexOrder Kronecker
open BoundaryReconstruction

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The native first-register record projector. -/
def recordMatrix {Y : Type} (q : X → Y) (y : Y) : Matrix X X ℂ := by
  classical
  exact Thermal.realDiagonal (fun x => if q x = y then 1 else 0)

def recordProjector {Y : Type} (q : X → Y) (y : Y)
    (v : X × X → ℂ) : X × X → ℂ := by
  classical
  exact fun z => if q z.1 = y then v z else 0

omit [Fintype X] in
theorem recordMatrix_hermitian {Y : Type} (q : X → Y) (y : Y) :
    (recordMatrix q y).IsHermitian := by
  classical
  exact Thermal.realDiagonal_hermitian _

theorem recordMatrix_idempotent {Y : Type} (q : X → Y) (y : Y) :
    recordMatrix q y * recordMatrix q y = recordMatrix q y := by
  classical
  unfold recordMatrix Thermal.realDiagonal
  rw [Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext x
  by_cases hx : q x = y <;> simp [hx]

theorem recordProjector_eq_matrix {Y : Type} (q : X → Y) (y : Y)
    (v : X × X → ℂ) :
    recordProjector q y v = (recordMatrix q y ⊗ₖ (1 : Matrix X X ℂ)).mulVec v := by
  classical
  funext z
  rcases z with ⟨i, j⟩
  by_cases hi : q i = y <;>
    simp [recordProjector, recordMatrix, Thermal.realDiagonal, Matrix.mulVec,
      dotProduct, Fintype.sum_prod_type, Matrix.diagonal,
      Matrix.one_apply, hi, ite_mul]

theorem sqrt_fraction_mul_sqrt_inv {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    Real.sqrt (a / b) * Real.sqrt a⁻¹ = Real.sqrt b⁻¹ := by
  rw [← Real.sqrt_mul (div_nonneg ha.le hb)]
  congr 1
  calc
    a / b * a⁻¹ = (a * a⁻¹) * b⁻¹ := by ring
    _ = b⁻¹ := by rw [mul_inv_cancel₀ (ne_of_gt ha), one_mul]

/-- The projection identity, including empty input spaces and unattained records. -/
theorem recordProjection_purifiedFiber {Y : Type} (q : X → Y) (y : Y) :
    recordProjector q y (purifiedFiber Finset.univ) =
      (Real.sqrt ((fiber q y).card / (Fintype.card X : ℝ)) : ℂ) •
        purifiedFiber (fiber q y) := by
  classical
  funext z
  rcases z with ⟨i, j⟩
  by_cases hi : q i = y
  · by_cases hij : i = j
    · subst j
      have hC : (fiber q y).Nonempty := ⟨i, (mem_fiber q y i).mpr hi⟩
      have hc : (0 : ℝ) < (fiber q y).card := by exact_mod_cast hC.card_pos
      have hs := sqrt_fraction_mul_sqrt_inv hc (Nat.cast_nonneg (Fintype.card X) : (0 : ℝ) ≤ _)
      have hs' : (Real.sqrt ((Fintype.card X : ℝ)⁻¹) : ℂ) =
          (Real.sqrt ((fiber q y).card / (Fintype.card X : ℝ)) : ℂ) *
            (Real.sqrt (((fiber q y).card : ℝ)⁻¹) : ℂ) := by
        exact_mod_cast hs.symm
      simpa [recordProjector, purifiedFiber, hi, Pi.smul_apply,
        smul_eq_mul] using hs'
    · simp [recordProjector, purifiedFiber, hi, hij, Pi.smul_apply]
  · simp [recordProjector, purifiedFiber, hi, Pi.smul_apply]

theorem bornMass_smul {I : Type} [Fintype I] (c : ℂ) (v : I → ℂ) :
    bornMass (c • v) = Complex.normSq c * bornMass v := by
  simp [bornMass, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

theorem recordProjection_bornMass {Y : Type} (q : X → Y) (y : Y) :
    bornMass (recordProjector q y (purifiedFiber Finset.univ)) =
      (fiber q y).card / (Fintype.card X : ℝ) := by
  rw [recordProjection_purifiedFiber, bornMass_smul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  by_cases hC : (fiber q y).Nonempty
  · rw [purifiedFiber_normalized _ hC, mul_one]
  · have hz : fiber q y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp [hz]

/-- Normalize by the actual Born norm; the zero vector remains zero. -/
def normalizeAmplitude {I : Type} [Fintype I] (v : I → ℂ) : I → ℂ :=
  (Real.sqrt (bornMass v) : ℂ)⁻¹ • v

theorem recordProjection_normalized {Y : Type} (q : X → Y) (y : Y)
    (hC : (fiber q y).Nonempty) :
    normalizeAmplitude (recordProjector q y (purifiedFiber Finset.univ)) =
      purifiedFiber (fiber q y) := by
  obtain ⟨x, hx⟩ := hC
  letI : Nonempty X := ⟨x⟩
  have hc : (0 : ℝ) < (fiber q y).card := by
    exact_mod_cast Finset.card_pos.mpr (show (fiber q y).Nonempty from ⟨x, hx⟩)
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt ((fiber q y).card / (Fintype.card X : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (div_pos hc hn))
  unfold normalizeAmplitude
  rw [recordProjection_bornMass, recordProjection_purifiedFiber, smul_smul,
    inv_mul_cancel₀ hs, one_smul]

omit [DecidableEq X] in
theorem fiber_attained_eq {Y : Type} (q : X → Y) (y : Set.range q) :
    fiber q y.1 =
      Finset.univ.filter (fun x : X => BitDivision.attainedObserver q x = y) := by
  classical
  ext x
  simp only [mem_fiber, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem attainedRecordMass_eq_bornMass {Y : Type} (q : X → Y) (y : Set.range q) :
    BitDivision.attainedUniformRecordMass q y =
      bornMass (recordProjector q y.1 (purifiedFiber Finset.univ)) := by
  rw [recordProjection_bornMass, fiber_attained_eq]
  rfl

/-- The mean of the actual spectral entropies of the conditional fiber marginals. -/
def expectedFiberEntropy {Y : Type} (q : X → Y) : ℝ := by
  classical
  letI : Fintype (Set.range q) := BitDivision.attainedRangeFintype q
  exact ∑ y : Set.range q, BitDivision.attainedUniformRecordMass q y *
    Thermal.entropy (Thermal.marginalLeft (pureDensity (purifiedFiber (fiber q y.1))))

theorem expectedFiberEntropy_eq_meanLog {Y : Type} (q : X → Y) :
    expectedFiberEntropy q = BitDivision.attainedUniformMeanLogFiber q := by
  classical
  unfold expectedFiberEntropy BitDivision.attainedUniformMeanLogFiber
  apply Finset.sum_congr rfl
  intro y _
  rw [entropy_marginal_purifiedFiber_all, fiber_attained_eq]

theorem expectedFiberEntropy_eq_conditional {Y : Type} [Nonempty X] (q : X → Y) :
    expectedFiberEntropy q = BitDivision.attainedUniformConditionalEntropy q := by
  rw [expectedFiberEntropy_eq_meanLog,
    BitDivision.attainedUniformConditionalEntropy_eq_meanLog]

/-- Actual state-record mutual information from its marginal and joint Shannon entropies. -/
def recordMutualInformation {Y : Type} (q : X → Y) : ℝ :=
  BitDivision.entropy (fun _ : X => (1 : ℝ) / Fintype.card X) +
    BitDivision.attainedUniformRecordEntropy q -
      BitDivision.attainedUniformRecordEntropy (fun x : X => (x, q x))

def resolvedFiberEntropy {Y : Type} (q : X → Y) : ℝ :=
  Thermal.entropy (Thermal.marginalLeft (pureDensity (purifiedFiber (Finset.univ : Finset X)))) -
    expectedFiberEntropy q

theorem resolvedFiberEntropy_eq_mutualInformation {Y : Type} [Nonempty X] (q : X → Y) :
    resolvedFiberEntropy q = recordMutualInformation q := by
  simp only [resolvedFiberEntropy, recordMutualInformation,
    entropy_marginal_purifiedFiber_all, Finset.card_univ, expectedFiberEntropy_eq_conditional,
    BitDivision.attainedUniformConditionalEntropy,
    BitDivision.attainedUniformJointEntropy_eq_state, BitDivision.entropy_uniform]
  ring

end OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

namespace OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

open scoped BigOperators
open BoundaryReconstruction
open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
theorem attained_fiber_nonempty {Y : Type} (q : X → Y) (y : Set.range q) :
    (fiber q y.1).Nonempty := by
  obtain ⟨x, hx⟩ := y.2
  exact ⟨x, (mem_fiber q y.1 x).mpr hx⟩

theorem expectedFiberEntropy_nonneg {Y : Type} (q : X → Y) :
    0 ≤ expectedFiberEntropy q := by
  classical
  unfold expectedFiberEntropy
  apply Finset.sum_nonneg
  intro y _
  rw [entropy_marginal_purifiedFiber_all]
  apply mul_nonneg (BitDivision.attainedUniformRecordMass_nonneg q y)
  apply Real.log_nonneg
  have hc : 1 ≤ (fiber q y.1).card := (attained_fiber_nonempty q y).card_pos
  exact_mod_cast hc

theorem expectedFiberEntropy_eq_zero_iff {Y : Type} [Nonempty X] (q : X → Y) :
    expectedFiberEntropy q = 0 ↔ Function.Injective q := by
  rw [expectedFiberEntropy_eq_conditional]
  exact BitDivision.attainedUniformConditionalEntropy_eq_zero_iff q

/-- Residual quantum entropy is positive exactly for a noninjective record. -/
theorem residual_pos_iff {Y : Type} [Nonempty X] (q : X → Y) :
    0 < expectedFiberEntropy q ↔ ¬ Function.Injective q := by
  constructor
  · intro h hinj
    have hz := (expectedFiberEntropy_eq_zero_iff q).mpr hinj
    linarith
  · intro h
    by_contra hn
    have hz : expectedFiberEntropy q = 0 :=
      le_antisymm (le_of_not_gt hn) (expectedFiberEntropy_nonneg q)
    exact h ((expectedFiberEntropy_eq_zero_iff q).mp hz)

theorem residual_pos_iff_mergedPair {Y : Type} [Nonempty X] (q : X → Y) :
    0 < expectedFiberEntropy q ↔ ∃ x x', MergedPair.IsMergedPair q x x' := by
  classical
  rw [residual_pos_iff]
  constructor
  · intro h
    by_contra hn
    apply h
    intro x x' hq
    by_contra hne
    exact hn ⟨x, x', hne, hq⟩
  · rintro ⟨x, x', hne, hq⟩ hinj
    exact hne (hinj hq)

theorem residual_pos_iff_nontrivial_orbit {Y : Type} [Nonempty X] (q : X → Y) :
    0 < expectedFiberEntropy q ↔
      ∃ x x', x ≠ x' ∧ ∃ σ ∈ licenseStabilizer q, σ x = x' := by
  rw [residual_pos_iff_mergedPair]
  simp only [MergedPair.IsMergedPair, MergedPair.same_record_iff_orbit]

end OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

namespace OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

open scoped BigOperators ComplexOrder
open BoundaryReconstruction

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Average marginal entropy of the actual normalized projected uniform amplitudes. -/
def postMeasurementExpectedEntropy {Y : Type} (q : X → Y) : ℝ := by
  classical
  letI : Fintype (Set.range q) := BitDivision.attainedRangeFintype q
  exact ∑ y : Set.range q,
    bornMass (recordProjector q y.1 (purifiedFiber Finset.univ)) *
      Thermal.entropy (Thermal.marginalLeft (pureDensity
        (normalizeAmplitude (recordProjector q y.1 (purifiedFiber Finset.univ)))))

theorem postMeasurementExpectedEntropy_eq_expected {Y : Type} (q : X → Y) :
    postMeasurementExpectedEntropy q = expectedFiberEntropy q := by
  classical
  unfold postMeasurementExpectedEntropy expectedFiberEntropy
  apply Finset.sum_congr rfl
  intro y _
  rw [recordProjection_normalized q y.1 (attained_fiber_nonempty q y),
    ← attainedRecordMass_eq_bornMass q y]

theorem postMeasurementExpectedEntropy_eq_conditional {Y : Type} [Nonempty X] (q : X → Y) :
    postMeasurementExpectedEntropy q = BitDivision.attainedUniformConditionalEntropy q := by
  rw [postMeasurementExpectedEntropy_eq_expected, expectedFiberEntropy_eq_conditional]

end OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

namespace OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

open scoped BigOperators ComplexOrder
open BoundaryReconstruction
open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

variable {T : Type}

/-- The actual counted states with fixed content and counts from zero through n. -/
def CountedPasses (R : T) (n : ℕ) :=
  {s : T × ℕ // s.1 = R ∧ s.2 ≤ n}

def countedPassEquiv (R : T) (n : ℕ) : CountedPasses R n ≃ Fin (n + 1) where
  toFun s := ⟨s.1.2, Nat.lt_succ_of_le s.2.2⟩
  invFun i := ⟨(R, i.val), rfl, Nat.le_of_lt_succ i.isLt⟩
  left_inv s := Subtype.ext (Prod.ext s.2.1.symm rfl)
  right_inv _ := Fin.ext rfl

instance countedPassesFintype (R : T) (n : ℕ) : Fintype (CountedPasses R n) :=
  Fintype.ofEquiv (Fin (n + 1)) (countedPassEquiv R n).symm

instance countedPassesDecidableEq (R : T) (n : ℕ) : DecidableEq (CountedPasses R n) :=
  Classical.decEq _

instance countedPassesNonempty (R : T) (n : ℕ) : Nonempty (CountedPasses R n) :=
  ⟨⟨(R, 0), rfl, Nat.zero_le n⟩⟩

/-- The existing content observer restricted to the actual bounded pass states. -/
def countedContent (R : T) (n : ℕ) : CountedPasses R n → T :=
  fun s => RecursorDecidability.content s.1

theorem countedContent_eq (R : T) (n : ℕ) (s : CountedPasses R n) :
    countedContent R n s = R := s.2.1

theorem countedPasses_card (R : T) (n : ℕ) :
    Fintype.card (CountedPasses R n) = n + 1 := by
  simpa using Fintype.card_congr (countedPassEquiv R n)

theorem countedContent_fiber (R : T) (n : ℕ) :
    fiber (countedContent R n) R = Finset.univ := by
  ext s
  simp [countedContent_eq]

theorem countedContent_fiber_card (R : T) (n : ℕ) :
    (fiber (countedContent R n) R).card = n + 1 := by
  rw [countedContent_fiber, Finset.card_univ, countedPasses_card]

/-- Every permutation of the counted content fiber is invisible. -/
def countedStabilizerAll (R : T) (n : ℕ) :
    licenseStabilizer (countedContent R n) ≃* Equiv.Perm (CountedPasses R n) where
  toFun σ := σ.1
  invFun σ := ⟨σ, fun s => (countedContent_eq R n (σ s)).trans
    (countedContent_eq R n s).symm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The group on the actual fiber is the full symmetric group on n+1 counts. -/
def countedPasses_groupEquiv (R : T) (n : ℕ) :
    licenseStabilizer (countedContent R n) ≃* Equiv.Perm (Fin (n + 1)) :=
  (countedStabilizerAll R n).trans (Equiv.Perm.permCongrHom (countedPassEquiv R n))

/-- Extend a fiber permutation to all counted states by fixing its complement. -/
def countedPassLift (R : T) (n : ℕ) (σ : Equiv.Perm (CountedPasses R n)) :
    Equiv.Perm (T × ℕ) := by
  classical
  exact Equiv.Perm.ofSubtype σ

theorem countedPassLift_restrict (R : T) (n : ℕ)
    (σ : Equiv.Perm (CountedPasses R n)) (s : CountedPasses R n) :
    countedPassLift R n σ s.1 = (σ s).1 := by
  classical
  exact Equiv.Perm.ofSubtype_apply_coe σ s

theorem countedPassLift_invisible (R : T) (n : ℕ)
    (σ : Equiv.Perm (CountedPasses R n)) :
    countedPassLift R n σ ∈ licenseStabilizer (RecursorDecidability.content (T := T)) := by
  classical
  intro s
  by_cases hs : s.1 = R ∧ s.2 ≤ n
  · unfold countedPassLift
    rw [Equiv.Perm.ofSubtype_apply_of_mem σ hs]
    exact (σ ⟨s, hs⟩).2.1.trans hs.1.symm
  · unfold countedPassLift
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem σ hs]

theorem countedPasses_entropy (R : T) (n : ℕ) :
    Thermal.entropy (Thermal.marginalLeft
      (pureDensity (purifiedFiber (fiber (countedContent R n) R)))) =
        Real.log (n + 1) := by
  rw [entropy_marginal_purifiedFiber_all, countedContent_fiber_card]
  norm_cast

theorem countedPasses_entropy_eq_leftEntropy (R : T) (n : ℕ) :
    Thermal.entropy (Thermal.marginalLeft
      (pureDensity (purifiedFiber (fiber (countedContent R n) R)))) =
        RecursorDecidability.leftEntropy (fun _ : Fin (n + 1) => ()) := by
  rw [countedPasses_entropy, RecursorDecidability.content_leaves_log]

/-- The quantum fiber recovers the established counted-recursion bit law. -/
theorem countedPasses_entropy_bits (R : T) (n : ℕ) :
    Thermal.entropy (Thermal.marginalLeft
      (pureDensity (purifiedFiber (fiber (countedContent R n) R)))) / Real.log 2 =
        Real.logb 2 (n + 1) := by
  rw [countedPasses_entropy_eq_leftEntropy]
  exact CountedRecursionLaws.countedRecursion_passes_logb_two n

def countedPassInclusion (R : T) (n : ℕ) :
    CountedPasses R n ↪ CountedPasses R (n + 1) where
  toFun s := ⟨s.1, s.2.1, Nat.le_trans s.2.2 (Nat.le_succ n)⟩
  inj' := by
    intro s t h
    exact Subtype.ext (congrArg (fun u : CountedPasses R (n + 1) => u.val) h)

def countedNewState (R : T) (n : ℕ) : CountedPasses R (n + 1) :=
  ⟨(R, n + 1), rfl, le_rfl⟩

theorem countedNewState_not_in_range (R : T) (n : ℕ) :
    countedNewState R n ∉ Set.range (countedPassInclusion R n) := by
  rintro ⟨s, hs⟩
  have hc : s.1.2 = n + 1 := congrArg (fun z : CountedPasses R (n + 1) => z.1.2) hs
  have hb := s.2.2
  omega

theorem countedPasses_successor_partition (R : T) (n : ℕ) (s : CountedPasses R (n + 1)) :
    s = countedNewState R n ∨ ∃ t, countedPassInclusion R n t = s := by
  by_cases hs : s.1.2 ≤ n
  · right
    exact ⟨⟨s.1, s.2.1, hs⟩, Subtype.ext rfl⟩
  · left
    apply Subtype.ext
    apply Prod.ext
    · exact s.2.1
    · have hb := s.2.2
      change s.1.2 = n + 1
      omega

theorem countedPasses_card_successor (R : T) (n : ℕ) :
    Fintype.card (CountedPasses R (n + 1)) =
      Fintype.card (CountedPasses R n) + 1 := by
  rw [countedPasses_card, countedPasses_card]

/-- The added counted state makes precisely one actual pass to the previous count. -/
theorem countedNewState_pass (R : T) (n : ℕ) :
    RecursorDecidability.Pass (countedNewState R n).1 (R, n) :=
  RecursorDecidability.pass_of_step (R, n)

theorem countedPasses_entropy_successor (R : T) (n : ℕ) :
    Thermal.entropy (Thermal.marginalLeft
      (pureDensity (purifiedFiber (fiber (countedContent R (n + 1)) R)))) -
      Thermal.entropy (Thermal.marginalLeft
        (pureDensity (purifiedFiber (fiber (countedContent R n) R)))) =
      Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
  rw [countedPasses_entropy, countedPasses_entropy,
    Real.log_div (by positivity : (n : ℝ) + 2 ≠ 0)
      (by positivity : (n : ℝ) + 1 ≠ 0)]
  congr 1; congr 1; push_cast; ring

end OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

namespace OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

variable {T : Type}

/-- The image of the actual old-state inclusion inside the successor prefix. -/
def countedPassRangeEquiv (R : T) (n : ℕ) :
    CountedPasses R n ≃ {s : CountedPasses R (n + 1) // s.1.2 ≤ n} where
  toFun s := ⟨countedPassInclusion R n s, s.2.2⟩
  invFun s := ⟨s.1.1, s.1.2.1, s.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

/-- Extend each old permutation across the actual inclusion and fix the new state. -/
def countedPermEmbedding (R : T) (n : ℕ) :
    Equiv.Perm (CountedPasses R n) →* Equiv.Perm (CountedPasses R (n + 1)) := by
  classical
  exact Equiv.Perm.ofSubtype.comp
    (Equiv.Perm.permCongrHom (countedPassRangeEquiv R n)).toMonoidHom

theorem countedPermEmbedding_apply_inclusion (R : T) (n : ℕ)
    (σ : Equiv.Perm (CountedPasses R n)) (s : CountedPasses R n) :
    countedPermEmbedding R n σ (countedPassInclusion R n s) =
      countedPassInclusion R n (σ s) := by
  classical
  change Equiv.Perm.ofSubtype ((countedPassRangeEquiv R n).permCongr σ)
      ((countedPassRangeEquiv R n s).1) = (countedPassRangeEquiv R n (σ s)).1
  rw [Equiv.Perm.ofSubtype_apply_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]

theorem countedPermEmbedding_fixes_new (R : T) (n : ℕ)
    (σ : Equiv.Perm (CountedPasses R n)) :
    countedPermEmbedding R n σ (countedNewState R n) = countedNewState R n := by
  classical
  exact Equiv.Perm.ofSubtype_apply_of_not_mem
    ((countedPassRangeEquiv R n).permCongr σ) (by
      change ¬ n + 1 ≤ n
      omega)

theorem countedPermEmbedding_injective (R : T) (n : ℕ) :
    Function.Injective (countedPermEmbedding R n) := by
  intro σ τ h
  ext s
  apply (countedPassInclusion R n).injective
  have he := congrArg (fun π : Equiv.Perm (CountedPasses R (n + 1)) =>
    π (countedPassInclusion R n s)) h
  simpa only [countedPermEmbedding_apply_inclusion] using he

def countedLastState (R : T) (n : ℕ) : CountedPasses R n :=
  ⟨(R, n), rfl, le_rfl⟩

/-- The new adjacent transposition exchanges counters n+1 and n. -/
def countedNewSwap (R : T) (n : ℕ) : Equiv.Perm (CountedPasses R (n + 1)) :=
  Equiv.swap (countedNewState R n)
    (countedPassInclusion R n (countedLastState R n))

theorem countedNewSwap_moves_new (R : T) (n : ℕ) :
    countedNewSwap R n (countedNewState R n) =
      countedPassInclusion R n (countedLastState R n) := by
  exact Equiv.swap_apply_left _ _

theorem countedNewSwap_not_mem_range (R : T) (n : ℕ) :
    countedNewSwap R n ∉ (countedPermEmbedding R n).range := by
  rintro ⟨σ, hσ⟩
  have he := congrArg (fun π : Equiv.Perm (CountedPasses R (n + 1)) =>
    π (countedNewState R n)) hσ
  dsimp only at he
  rw [countedPermEmbedding_fixes_new, countedNewSwap_moves_new] at he
  exact countedNewState_not_in_range R n ⟨countedLastState R n, he.symm⟩

theorem countedPermEmbedding_range_lt_top (R : T) (n : ℕ) :
    (countedPermEmbedding R n).range < ⊤ := by
  rw [lt_iff_le_not_ge]
  refine ⟨le_top, ?_⟩
  intro h
  exact countedNewSwap_not_mem_range R n (h (by trivial))

theorem countedPermEmbedding_not_surjective (R : T) (n : ℕ) :
    ¬ Function.Surjective (countedPermEmbedding R n) := by
  intro h
  exact countedNewSwap_not_mem_range R n (h (countedNewSwap R n))

/-- The same proper embedding in the standard symmetric-group coordinates. -/
def countedSymmetricEmbedding (R : T) (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) →* Equiv.Perm (Fin (n + 2)) :=
  (Equiv.Perm.permCongrHom (countedPassEquiv R (n + 1))).toMonoidHom.comp
    ((countedPermEmbedding R n).comp
      (Equiv.Perm.permCongrHom (countedPassEquiv R n)).symm.toMonoidHom)

theorem countedSymmetricEmbedding_injective (R : T) (n : ℕ) :
    Function.Injective (countedSymmetricEmbedding R n) :=
  (Equiv.Perm.permCongrHom (countedPassEquiv R (n + 1))).injective.comp
    ((countedPermEmbedding_injective R n).comp
      (Equiv.Perm.permCongrHom (countedPassEquiv R n)).symm.injective)

theorem countedSymmetricEmbedding_not_surjective (R : T) (n : ℕ) :
    ¬ Function.Surjective (countedSymmetricEmbedding R n) := by
  intro h
  apply countedPermEmbedding_not_surjective R n
  intro τ
  obtain ⟨σ, hσ⟩ := h (Equiv.Perm.permCongrHom (countedPassEquiv R (n + 1)) τ)
  refine ⟨(Equiv.Perm.permCongrHom (countedPassEquiv R n)).symm σ, ?_⟩
  apply (Equiv.Perm.permCongrHom (countedPassEquiv R (n + 1))).injective
  exact hσ

end OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

namespace OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

/-- Distinct consecutive counter edges give distinct adjacent transpositions. -/
theorem adjacentSwap_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
  intro i j h
  have he := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ i.castSucc) h
  dsimp only at he
  rw [Equiv.swap_apply_left] at he
  by_cases h₀ : i.castSucc = j.castSucc
  · exact Fin.ext (congrArg (fun z : Fin (n + 1) => z.val) h₀)
  · by_cases h₁ : i.castSucc = j.succ
    · have h₂ : i.succ = j.castSucc := by
        simpa [Equiv.swap_apply_def, h₀, h₁] using he
      have v₁ := congrArg (fun z : Fin (n + 1) => z.val) h₁
      have v₂ := congrArg (fun z : Fin (n + 1) => z.val) h₂
      change i.val = j.val + 1 at v₁
      change i.val + 1 = j.val at v₂
      omega
    · have h₂ : i.succ = i.castSucc := by
        simpa [Equiv.swap_apply_def, h₀, h₁] using he
      have v₂ := congrArg (fun z : Fin (n + 1) => z.val) h₂
      change i.val + 1 = i.val at v₂
      omega

/-- The canonical adjacent generating family, transported to the actual counted fiber. -/
def countedAdjacentGenerator {T : Type} (R : T) (n : ℕ) (i : Fin n) :
    licenseStabilizer (countedContent R n) :=
  (countedPasses_groupEquiv R n).symm (Equiv.swap i.castSucc i.succ)

theorem countedAdjacentGenerator_injective {T : Type} (R : T) (n : ℕ) :
    Function.Injective (countedAdjacentGenerator R n) :=
  (countedPasses_groupEquiv R n).symm.injective.comp (adjacentSwap_injective n)

theorem countedAdjacentGenerator_generates {T : Type} (R : T) (n : ℕ) :
    Subgroup.closure (Set.range (countedAdjacentGenerator R n)) = ⊤ := by
  let e := countedPasses_groupEquiv R n
  have hr : Set.range (countedAdjacentGenerator R n) =
      e.symm '' Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    ext σ
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨τ, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  have hg : Subgroup.closure
      (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top
      (Equiv.Perm.mclosure_swap_castSucc_succ n)
  rw [hr]
  change Subgroup.closure
    (e.symm.toMonoidHom '' Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) = ⊤
  rw [← MonoidHom.map_closure e.symm.toMonoidHom, hg,
    Subgroup.map_top_of_surjective _ e.symm.surjective]

def countedGenerators {T : Type} (R : T) (n : ℕ) :
    Finset (licenseStabilizer (countedContent R n)) := by
  classical
  exact Finset.univ.image (countedAdjacentGenerator R n)

theorem countedGenerators_card {T : Type} (R : T) (n : ℕ) :
    (countedGenerators R n).card = n := by
  classical
  rw [countedGenerators, Finset.card_image_of_injective _
    (countedAdjacentGenerator_injective R n), Finset.card_univ, Fintype.card_fin]

/-- One additional adjacent generator, without a claim about minimal generating sets. -/
theorem countedGenerators_card_successor {T : Type} (R : T) (n : ℕ) :
    (countedGenerators R (n + 1)).card = (countedGenerators R n).card + 1 := by
  rw [countedGenerators_card, countedGenerators_card]

end OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

namespace OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

variable {T : Type}

theorem countedPermEmbedding_map_swap (R : T) (n : ℕ) (x y : CountedPasses R n) :
    countedPermEmbedding R n (Equiv.swap x y) =
      Equiv.swap (countedPassInclusion R n x) (countedPassInclusion R n y) := by
  ext s
  rcases countedPasses_successor_partition R n s with rfl | ⟨s, rfl⟩
  · rw [countedPermEmbedding_fixes_new]
    symm
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      exact countedNewState_not_in_range R n ⟨x, h.symm⟩
    · intro h
      exact countedNewState_not_in_range R n ⟨y, h.symm⟩
  · rw [countedPermEmbedding_apply_inclusion]
    exact (countedPassInclusion R n).injective.map_swap x y s

/-- The old symmetric group and the single new adjacent transposition generate the successor. -/
theorem countedPasses_one_new_generator (R : T) (n : ℕ) :
    Subgroup.closure
      (((countedPermEmbedding R n).range :
        Set (Equiv.Perm (CountedPasses R (n + 1)))) ∪ {countedNewSwap R n}) = ⊤ := by
  let H : Subgroup (Equiv.Perm (CountedPasses R (n + 1))) :=
    Subgroup.closure
      (((countedPermEmbedding R n).range :
        Set (Equiv.Perm (CountedPasses R (n + 1)))) ∪ {countedNewSwap R n})
  have hold (x y : CountedPasses R n) :
      Equiv.swap (countedPassInclusion R n x) (countedPassInclusion R n y) ∈ H := by
    rw [← countedPermEmbedding_map_swap]
    exact Subgroup.subset_closure (Or.inl ⟨Equiv.swap x y, rfl⟩)
  have hstep :
      Equiv.swap (countedNewState R n)
        (countedPassInclusion R n (countedLastState R n)) ∈ H :=
    Subgroup.subset_closure (Or.inr rfl)
  have hnew (x : CountedPasses R n) :
      Equiv.swap (countedNewState R n) (countedPassInclusion R n x) ∈ H :=
    SubmonoidClass.swap_mem_trans H hstep (hold (countedLastState R n) x)
  have hswap (x y : CountedPasses R (n + 1)) : Equiv.swap x y ∈ H := by
    rcases countedPasses_successor_partition R n x with rfl | ⟨x, rfl⟩
    · rcases countedPasses_successor_partition R n y with rfl | ⟨y, rfl⟩
      · simpa only [Equiv.swap_self] using H.one_mem
      · exact hnew y
    · rcases countedPasses_successor_partition R n y with rfl | ⟨y, rfl⟩
      · rw [Equiv.swap_comm]
        exact hnew x
      · exact hold x y
  apply top_unique
  intro σ _
  change σ ∈ H
  exact Equiv.Perm.swap_induction_on σ H.one_mem
    (fun τ x y _ hτ => H.mul_mem (hswap x y) hτ)

end OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

namespace OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

open OperatorKO7.Meta.UUET
open OperatorKO7.Meta.UUET.Quantum
open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
open BoundaryReconstruction PairPurification
open scoped BigOperators Matrix Kronecker ComplexOrder Classical

set_option autoImplicit false

/-- The conjunction of the entangled-pair and purified-fiber results, with the fair-pair density
as an instance. -/
def EntangledMergedPairsGoal : Prop :=
  (∀ w : TwoBranchWeight,
    amplitudeEntanglement w.swap = amplitudeEntanglement w ∧
      (amplitudeEntanglement w = 1 / 4 ↔ w.p = 1 / 2)) ∧
  (∀ (X Y : Type) (q : X → Y) (x₀ x₁ : X), x₀ ≠ x₁ →
      ∀ p : X → ℝ, EntangledMergedPair.PairLaw p x₀ x₁ →
    EntangledMergedPair.residualEntanglement q p x₀ x₁ =
        (if q x₀ = q x₁ then p x₀ * p x₁ else 0) ∧
      (0 < EntangledMergedPair.residualEntanglement q p x₀ x₁ ↔
        q x₀ = q x₁ ∧ 0 < p x₀ ∧ 0 < p x₁)) ∧
  (∀ w : TwoBranchWeight,
    amplitudeDet (schmidtAmp w) = (Real.sqrt (amplitudeEntanglement w) : ℂ) ∧
      (QuantumEntangled (schmidtAmp w) ↔ 0 < amplitudeEntanglement w) ∧
      (ProductAmplitude (schmidtAmp w) ↔ amplitudeEntanglement w = 0)) ∧
  (∀ w : TwoBranchWeight,
    concurrence (schmidtAmp w) = 2 * Real.sqrt (amplitudeEntanglement w) ∧
      concurrence (schmidtAmp w) ^ 2 = 4 * amplitudeEntanglement w ∧
      (w.p - w.q) ^ 2 + concurrence (schmidtAmp w) ^ 2 = 1) ∧
  (∀ (w : TwoBranchWeight) (A : TwoQubitAmplitude),
    Matrix.of A * (Matrix.of A)ᴴ = Matrix.diagonal ![(w.p : ℂ), (w.q : ℂ)] →
      concurrence A ^ 2 = 4 * amplitudeEntanglement w) ∧
  -- Over every permitted quadruple of sign tests.
  (∀ w : TwoBranchWeight,
    IsGreatest (signScores (schmidtDensity w))
        (2 * Real.sqrt (1 + 4 * amplitudeEntanglement w)) ∧
      IsGreatest (signScores (schmidtDensity w))
        (2 * Real.sqrt (1 + concurrence (schmidtAmp w) ^ 2)) ∧
      IsGreatest (signScores (schmidtDensity w))
        (2 * Real.sqrt (2 - (w.p - w.q) ^ 2))) ∧
  -- With the finite convex product-density definition.
  (∀ ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ, IsSeparable ρ →
    ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ,
        PairBell.SignTest a₀ → PairBell.SignTest a₁ →
        PairBell.SignTest b₀ → PairBell.SignTest b₁ →
        signScore ρ a₀ a₁ b₀ b₁ ≤ 2 ∧ |signScore ρ a₀ a₁ b₀ b₁| ≤ 2) ∧
  (∀ w : TwoBranchWeight,
    (IsSeparable (schmidtDensity w) ↔ amplitudeEntanglement w = 0) ∧
      (amplitudeEntanglement w = 0 ↔ ProductAmplitude (schmidtAmp w))) ∧
  -- Including the side-register unitary action.
  ((∃ U : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ,
      QuantumEntangled bellAmplitude ∧
        ProductAmplitude (applyUnitaryAmplitude U bellAmplitude)) ∧
    (∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) (A : TwoQubitAmplitude),
      Thermal.marginalLeft (amplitudeDensity (sideUnitaryAmplitude U A)) =
          Thermal.marginalLeft (amplitudeDensity A) ∧
        concurrence (sideUnitaryAmplitude U A) ^ 2 = concurrence A ^ 2) ∧
    (∀ (w : TwoBranchWeight) (A : TwoQubitAmplitude),
      Matrix.of A * (Matrix.of A)ᴴ = Matrix.diagonal ![(w.p : ℂ), (w.q : ℂ)] →
        ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
          concurrence (sideUnitaryAmplitude U A) ^ 2 = 4 * amplitudeEntanglement w)) ∧
  (∀ (X : Type) [Fintype X] [DecidableEq X] (C : Finset X),
    Thermal.marginalLeft (pureDensity (purifiedFiber C)) =
        Thermal.realDiagonal (fiberWeight C) ∧
      Thermal.entropy (Thermal.marginalLeft (pureDensity (purifiedFiber C))) =
        Real.log C.card ∧
      (C.Nonempty →
        (pureDensity (purifiedFiber C)).PosSemidef ∧
        (pureDensity (purifiedFiber C)).trace = 1 ∧
        Thermal.entropy (Thermal.marginalLeft (pureDensity (purifiedFiber C))) /
          Real.log 2 = Real.logb 2 C.card)) ∧
  -- Stated with the tensor permutation matrices.
  ((∀ (X : Type) [Fintype X] [DecidableEq X] (C : Finset X) (σ : Equiv.Perm X),
    (permMatrix σ ⊗ₖ permMatrix σ).mulVec (purifiedFiber C) = purifiedFiber C ↔
      C.map σ.toEmbedding = C) ∧
    (∀ (X Y : Type) [Fintype X] [DecidableEq X] (q : X → Y) (σ : Equiv.Perm X),
      σ ∈ licenseStabilizer q ↔
        ∀ y, (permMatrix σ ⊗ₖ permMatrix σ).mulVec (purifiedFiber (fiber q y)) =
          purifiedFiber (fiber q y))) ∧
  -- Including the normalized post-measurement entropy.
  ((∀ (X Y : Type) [Fintype X] [DecidableEq X] (q : X → Y) (y : Y),
    (recordMatrix q y).IsHermitian ∧
      recordMatrix q y * recordMatrix q y = recordMatrix q y ∧
      (recordMatrix q y ⊗ₖ (1 : Matrix X X ℂ)).mulVec (purifiedFiber Finset.univ) =
        (Real.sqrt ((fiber q y).card / (Fintype.card X : ℝ)) : ℂ) •
          purifiedFiber (fiber q y) ∧
      bornMass ((recordMatrix q y ⊗ₖ (1 : Matrix X X ℂ)).mulVec
        (purifiedFiber Finset.univ)) = (fiber q y).card / (Fintype.card X : ℝ) ∧
      ((fiber q y).Nonempty →
        normalizeAmplitude ((recordMatrix q y ⊗ₖ (1 : Matrix X X ℂ)).mulVec
          (purifiedFiber Finset.univ)) = purifiedFiber (fiber q y))) ∧
    (∀ (X Y : Type) [Fintype X] [DecidableEq X] [Nonempty X] (q : X → Y),
      postMeasurementExpectedEntropy q = BitDivision.attainedUniformConditionalEntropy q ∧
        expectedFiberEntropy q = BitDivision.attainedUniformConditionalEntropy q ∧
        resolvedFiberEntropy q = recordMutualInformation q)) ∧
  -- On the post-measurement entropy.
  (∀ (X Y : Type) [Fintype X] [DecidableEq X] [Nonempty X] (q : X → Y),
    (postMeasurementExpectedEntropy q = 0 ↔ Function.Injective q) ∧
      (0 < postMeasurementExpectedEntropy q ↔ ¬ Function.Injective q) ∧
      (0 < postMeasurementExpectedEntropy q ↔ ∃ x x', MergedPair.IsMergedPair q x x') ∧
      (0 < postMeasurementExpectedEntropy q ↔
        ∃ x x', x ≠ x' ∧ ∃ σ ∈ licenseStabilizer q, σ x = x')) ∧
  -- The counted fiber, its ambient extensions, and one new state and generator.
  (∀ (T : Type) (R : T) (n : ℕ),
    let E : ℕ → ℝ := fun k => Thermal.entropy (Thermal.marginalLeft
      (pureDensity (purifiedFiber (fiber (countedContent R k) R))))
    (fiber (countedContent R n) R).card = n + 1 ∧
      Nonempty (licenseStabilizer (countedContent R n) ≃* Equiv.Perm (Fin (n + 1))) ∧
      (∀ σ : Equiv.Perm (CountedPasses R n),
        countedPassLift R n σ ∈ licenseStabilizer (RecursorDecidability.content (T := T)) ∧
          ∀ s : CountedPasses R n, countedPassLift R n σ s.1 = (σ s).1) ∧
      E n = Real.log (n + 1) ∧
      E n / Real.log 2 = Real.logb 2 (n + 1) ∧
      (Fintype.card (CountedPasses R (n + 1)) = Fintype.card (CountedPasses R n) + 1 ∧
        countedNewState R n ∉ Set.range (countedPassInclusion R n) ∧
        (∀ s : CountedPasses R (n + 1),
          s = countedNewState R n ∨ ∃ t, countedPassInclusion R n t = s) ∧
        RecursorDecidability.Pass (countedNewState R n).1 (R, n)) ∧
      E (n + 1) - E n = Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) ∧
      ((countedGenerators R n).card = n ∧
        (countedGenerators R (n + 1)).card = (countedGenerators R n).card + 1 ∧
        Function.Injective (countedAdjacentGenerator R n) ∧
        Subgroup.closure (Set.range (countedAdjacentGenerator R n)) = ⊤) ∧
      (Function.Injective (countedPermEmbedding R n) ∧
        countedNewSwap R n ∉ (countedPermEmbedding R n).range ∧
        (countedPermEmbedding R n).range < ⊤ ∧
        Subgroup.closure
          (((countedPermEmbedding R n).range :
            Set (Equiv.Perm (CountedPasses R (n + 1)))) ∪ {countedNewSwap R n}) = ⊤)) ∧
  -- Werner densities, the partial-transpose eigenvalue, and the CHSH threshold over all tests.
  ((∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      (wernerState p).PosSemidef ∧ (wernerState p).trace = 1) ∧
    (∀ ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ, IsSeparable ρ →
      (partialTransposeRight ρ).PosSemidef) ∧
    (∀ p : ℝ, ∃ v : Bool × Bool → ℂ, v ≠ 0 ∧
      partialTransposeRight (wernerState p) *ᵥ v =
        (((1 - 3 * p) / 4 : ℝ) : ℂ) • v) ∧
    (∀ p : ℝ, (1 : ℝ) / 3 < p → ¬ IsSeparable (wernerState p)) ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 / Real.sqrt 2 →
      ∀ a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ,
        PairBell.SignTest a₀ → PairBell.SignTest a₁ →
        PairBell.SignTest b₀ → PairBell.SignTest b₁ →
        |signScore (wernerState p) a₀ a₁ b₀ b₁| ≤ 2) ∧
    (∃ ρ : DensityMatrix (Bool × Bool), ¬ IsSeparable ρ.matrix ∧
      ∀ a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ,
        PairBell.SignTest a₀ → PairBell.SignTest a₁ →
        PairBell.SignTest b₀ → PairBell.SignTest b₁ →
        |signScore ρ.matrix a₀ a₁ b₀ b₁| ≤ 2)) ∧
  -- Fair-pair nonvacuity, with the actual source density and the full maximum.
  (amplitudeEntanglement balancedBranch = 1 / 4 ∧
    EntangledMergedPair.residualEntanglement (fun _ : Bool => ())
      (fun _ => (1 : ℝ) / 2) false true = 1 / 4 ∧
    QuantumEntangled (schmidtAmp balancedBranch) ∧
    ¬ IsSeparable (schmidtDensityState balancedBranch).matrix ∧
    IsGreatest (signScores (schmidtDensityState balancedBranch).matrix)
      (2 * Real.sqrt 2))

/-- The entangled-pair and purified-fiber results, proved together. -/
theorem entangledMergedPairs : EntangledMergedPairsGoal := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    exact ⟨EntangledMergedPair.amplitudeEntanglement_swap w,
      EntangledMergedPair.amplitudeEntanglement_eq_quarter_iff w⟩
  · intro X Y q x₀ x₁ h p hp
    exact ⟨EntangledMergedPair.residualEntanglement_eq q h p hp,
      EntangledMergedPair.entangledUnder_iff q h p hp⟩
  · intro w
    exact ⟨amplitudeDet_schmidtAmp w, quantumEntangled_schmidtAmp_iff w,
      productAmplitude_schmidtAmp_iff w⟩
  · intro w
    exact ⟨concurrence_schmidtAmp w, concurrence_sq_schmidtAmp w,
      concurrence_complementarity w⟩
  · exact concurrence_sq_of_marginal
  · intro w
    refine ⟨schmidt_chsh_isGreatest w, schmidt_chsh_isGreatest_concurrence w, ?_⟩
    have hrad : 2 - (w.p - w.q) ^ 2 = 1 + 4 * amplitudeEntanglement w := by
      dsimp [amplitudeEntanglement, TwoBranchWeight.q]
      ring
    rw [hrad]
    exact schmidt_chsh_isGreatest w
  · intro ρ hρ
    refine ⟨isSeparable_posSemidef hρ, isSeparable_trace hρ, ?_⟩
    intro a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
    exact ⟨separable_chsh_le_two hρ a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁,
      separable_abs_chsh_le_two hρ a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁⟩
  · exact purified_pair_separability
  · exact ⟨entanglement_split_unitary,
      fun U A => ⟨sideUnitary_marginal U A, sideUnitary_concurrence_sq U A⟩,
      sideUnitary_pair_quantity⟩
  · intro X _ _ C
    refine ⟨marginal_purifiedFiber C, entropy_marginal_purifiedFiber_all C, ?_⟩
    intro hC
    exact ⟨(purifiedFiber_density C hC).1, (purifiedFiber_density C hC).2,
      entropy_marginal_purifiedFiber_bits C hC⟩
  · constructor
    · intro X _ _ C σ
      simpa only [jointPerm_eq_matrix] using (jointPerm_fixes_iff C σ)
    · intro X Y _ _ q σ
      simpa only [jointPerm_eq_matrix] using (invisible_iff_joint_fixes_fibers q σ)
  · constructor
    · intro X Y _ _ q y
      refine ⟨recordMatrix_hermitian q y, recordMatrix_idempotent q y, ?_, ?_, ?_⟩
      · simpa only [recordProjector_eq_matrix] using (recordProjection_purifiedFiber q y)
      · simpa only [recordProjector_eq_matrix] using (recordProjection_bornMass q y)
      · intro hC
        simpa only [recordProjector_eq_matrix] using (recordProjection_normalized q y hC)
    · intro X Y _ _ _ q
      exact ⟨postMeasurementExpectedEntropy_eq_conditional q,
        expectedFiberEntropy_eq_conditional q, resolvedFiberEntropy_eq_mutualInformation q⟩
  · intro X Y _ _ _ q
    simp only [postMeasurementExpectedEntropy_eq_expected]
    exact ⟨expectedFiberEntropy_eq_zero_iff q, residual_pos_iff q,
      residual_pos_iff_mergedPair q, residual_pos_iff_nontrivial_orbit q⟩
  · intro T R n
    dsimp only
    refine ⟨countedContent_fiber_card R n, ⟨countedPasses_groupEquiv R n⟩, ?_,
      countedPasses_entropy R n, countedPasses_entropy_bits R n, ?_,
      countedPasses_entropy_successor R n, ?_, ?_⟩
    · intro σ
      exact ⟨countedPassLift_invisible R n σ, countedPassLift_restrict R n σ⟩
    · exact ⟨countedPasses_card_successor R n, countedNewState_not_in_range R n,
        countedPasses_successor_partition R n, countedNewState_pass R n⟩
    · exact ⟨countedGenerators_card R n, countedGenerators_card_successor R n,
        countedAdjacentGenerator_injective R n, countedAdjacentGenerator_generates R n⟩
    · exact ⟨countedPermEmbedding_injective R n, countedNewSwap_not_mem_range R n,
        countedPermEmbedding_range_lt_top R n, countedPasses_one_new_generator R n⟩
  · refine ⟨?_, fun _ hρ => separable_partialTranspose_pos hρ,
      werner_partialTranspose_has_eigenvalue, werner_entangled,
      werner_abs_chsh_le_two, werner_entangled_without_violation⟩
    intro p hp₀ hp₁
    exact ⟨wernerState_posSemidef p hp₀ hp₁, wernerState_trace p⟩
  · refine ⟨balancedBranch_amplitude, EntangledMergedPair.fair_merged_residual,
      schmidtAmp_nonvacuous.1, schmidt_separability_nonvacuous.1, ?_⟩
    have h := schmidt_chsh_isGreatest balancedBranch
    norm_num [balancedBranch_amplitude] at h
    exact h

end OperatorKO7.Meta.BoundaryObserver.PurifiedFiber