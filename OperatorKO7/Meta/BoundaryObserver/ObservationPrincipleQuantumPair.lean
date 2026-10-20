import OperatorKO7.Meta.BoundaryObserver.PairPurification
import OperatorKO7.Meta.BoundaryObserver.EntangledMergedPair
import OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

set_option autoImplicit false

/-!
# The quantum sentences of a merged pair in the Boundary-Observation Principle

The statements of the sections on the overlap, the entanglement of a merged pair and the tables
with vectors that no earlier declaration states: the overlap `2√(κρ)` as a sum over the pair, the
two forms `⟨ψ, Zψ⟩ = p(x₀) - p(x₁)` and `⟨ψ, Tψ⟩ = 2√(κρ)` of the square-root amplitude, the
label test and the transposition as orthonormal vectors for `½ tr(MN)` and the vectors
`Z, T, (Z ± T)/√2` of the extreme table, the angles of the extreme table, the Bloch vector of the
marginal of the purified pair, the forms `2√(2 - r²) = 2√(1 + 4κρ)` of its largest CHSH score
with the values at the fair and point laws, and the Werner densities on the whole interval
`1/3 < t ≤ 1/√2` with the instance `t = 1/2`.

Relation: none beyond the matrices and densities of the imported modules.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleQuantumPair

open OperatorKO7.Meta.UUET
open OperatorKO7.Meta.BoundaryObserver.FourTestTables
open OperatorKO7.Meta.BoundaryObserver.PairPurification

/-! ## Proposition `prop:overlap` -/

/-- The overlap `2√(κρ)` is the sum `∑_x √(p(x) p(τ x))` over the pair. -/
theorem overlap_sum (p : Bool → ℝ) :
    ∑ b, Real.sqrt (p b * p (!b)) = 2 * Real.sqrt (p true * p false) := by
  rw [Fintype.sum_bool]
  simp only [Bool.not_true, Bool.not_false]
  rw [mul_comm (p false) (p true)]
  ring

/-- The square-root amplitude `ψ = √p` of a law on the pair. -/
noncomputable def sqrtAmplitude (p : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => Real.sqrt (p i)

/-- `⟨ψ, Zψ⟩ = p(x₀) - p(x₁)` for the label test `Z`. -/
theorem sqrtAmplitude_label_form (p : Fin 2 → ℝ) (hp : ∀ i, 0 ≤ p i) :
    dotProduct (sqrtAmplitude p) (Matrix.mulVec labelMat (sqrtAmplitude p)) = p 0 - p 1 := by
  simp [sqrtAmplitude, labelMat, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
    Real.mul_self_sqrt (hp 0), Real.mul_self_sqrt (hp 1)]
  ring

/-- `⟨ψ, Tψ⟩ = 2√(κρ)` for the transposition `T`. -/
theorem sqrtAmplitude_swap_form (p : Fin 2 → ℝ) (hp : ∀ i, 0 ≤ p i) :
    dotProduct (sqrtAmplitude p) (Matrix.mulVec swapMat (sqrtAmplitude p)) =
      2 * Real.sqrt (p 0 * p 1) := by
  simp [sqrtAmplitude, swapMat, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Real.sqrt_mul (hp 0)]
  ring

/-- The inner product `⟨M, N⟩ = ½ tr(MN)` on real two-by-two matrices. -/
noncomputable def halfTraceInner (M N : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (1 / 2) * (M * N).trace

/-- The label test and the transposition are orthonormal for `½ tr(MN)`. -/
theorem label_swap_orthonormal :
    halfTraceInner labelMat labelMat = 1 ∧ halfTraceInner swapMat swapMat = 1 ∧
      halfTraceInner labelMat swapMat = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [halfTraceInner, labelMat_mul_self]
    simp [Matrix.trace]
  · rw [halfTraceInner, swapMat_mul_self]
    simp [Matrix.trace]
  · rw [halfTraceInner, label_swap_trace, mul_zero]

/-- The vectors `u₀ = Z`, `u₁ = T`, `v₀ = (Z + T)/√2`, `v₁ = (Z - T)/√2` of the extreme table. -/
noncomputable def extremeU (x : Bool) : Matrix (Fin 2) (Fin 2) ℝ := if x then swapMat else labelMat

/-- The second family of vectors of the extreme table. -/
noncomputable def extremeV (y : Bool) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / Real.sqrt 2) • (if y then labelMat - swapMat else labelMat + swapMat)

/-- `Z`, `T` and `(Z ± T)/√2` are unit vectors for `½ tr(MN)` whose inner products are the
correlations of the extreme table, of score `2√2`. -/
theorem extreme_vectors_realize :
    (∀ x, halfTraceInner (extremeU x) (extremeU x) = 1) ∧
      (∀ y, halfTraceInner (extremeV y) (extremeV y) = 1) ∧
      (∀ x y, halfTraceInner (extremeU x) (extremeV y) = corr extremeTable x y) ∧
      score extremeTable = 2 * Real.sqrt 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have hZZ : (labelMat * labelMat).trace = 2 := by rw [labelMat_mul_self]; simp [Matrix.trace]
  have hTT : (swapMat * swapMat).trace = 2 := by rw [swapMat_mul_self]; simp [Matrix.trace]
  have hZT : (labelMat * swapMat).trace = 0 := label_swap_trace
  have hTZ : (swapMat * labelMat).trace = 0 := by rw [Matrix.trace_mul_comm]; exact hZT
  refine ⟨fun x => ?_, fun y => ?_, fun x y => ?_, extremeTable_score⟩
  · cases x <;> simp only [extremeU, Bool.false_eq_true, if_false, if_true, halfTraceInner,
      hZZ, hTT] <;> norm_num
  · cases y <;> simp only [extremeV, Bool.false_eq_true, if_false, if_true, halfTraceInner,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub, hZZ, hTT, hZT, hTZ,
      smul_eq_mul] <;> field_simp
  · cases x <;> cases y <;> simp only [extremeU, extremeV, Bool.false_eq_true, if_false, if_true,
      halfTraceInner, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.trace_add, Matrix.trace_sub, hZZ, hTT, hZT, hTZ, smul_eq_mul, corr, extremeTable,
      Bool.and_false, Bool.and_true] <;> ring

/-! ## Theorem `thm:vector-tables`(iii): the angles of the extreme table -/

/-- The extreme table has the angles `π/4, π/4, π/4, 3π/4`, with `3π/4` at the pair `(1, 1)`. -/
theorem extremeTable_angles (x y : Bool) :
    Real.arccos (corr extremeTable x y) = if x && y then 3 * Real.pi / 4 else Real.pi / 4 := by
  have h1 : corr extremeTable x y = if x && y then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2 := by
    cases x <;> cases y <;> simp [corr, extremeTable] <;> ring
  rw [h1]
  have hcos : Real.cos (Real.pi / 4) = 1 / Real.sqrt 2 := by
    rw [Real.cos_pi_div_four, one_div, ← Real.sqrt_inv]
    rw [show (2 : ℝ)⁻¹ = 2 / 4 by norm_num, Real.sqrt_div' 2 (by norm_num : (0:ℝ) ≤ 4)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have harc : Real.arccos (1 / Real.sqrt 2) = Real.pi / 4 := by
    rw [← hcos, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
  split_ifs
  · rw [Real.arccos_neg, harc]
    ring
  · exact harc

/-! ## Theorem `thm:entangled-pair`(ii): the Bloch vector and the score forms -/

/-- The marginal of the purified pair `√κ |x₀x₀⟩ + √ρ |x₁x₁⟩` has the Bloch vector
`(0, 0, κ - ρ)`. -/
theorem schmidt_bloch_components (w : TwoBranchWeight) :
    (BoundaryReconstruction.Thermal.marginalLeft (schmidtDensity w) * PairQubit.pairX).trace.re = 0 ∧
      (BoundaryReconstruction.Thermal.marginalLeft (schmidtDensity w) *
        PairQubit.pairY).trace.re = 0 ∧
      (BoundaryReconstruction.Thermal.marginalLeft (schmidtDensity w) *
        PairQubit.pairZ).trace.re = w.p - w.q := by
  rw [schmidtDensity_marginal]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.trace, Matrix.mul_apply, PairQubit.pairX, PairQubit.pairY,
      PairQubit.pairZ, Matrix.diagonal]
  ring

/-- The largest CHSH score of the purified pair is `2√(2 - r²) = 2√(1 + 4κρ)` with `r = κ - ρ`:
`2√2` for the fair pair and the shared-record bound `2` for a point law. -/
theorem schmidt_score_forms (w : TwoBranchWeight) :
    IsGreatest (signScores (schmidtDensity w)) (2 * Real.sqrt (2 - (w.p - w.q) ^ 2)) ∧
      2 * Real.sqrt (2 - (w.p - w.q) ^ 2) = 2 * Real.sqrt (1 + 4 * (w.p * w.q)) ∧
      (w.p = 1 / 2 → 2 * Real.sqrt (2 - (w.p - w.q) ^ 2) = 2 * Real.sqrt 2) ∧
      (w.p * w.q = 0 → 2 * Real.sqrt (2 - (w.p - w.q) ^ 2) = 2) := by
  have hq : w.q = 1 - w.p := rfl
  have hc := concurrence_complementarity w
  have h1 : 1 + concurrence (schmidtAmp w) ^ 2 = 2 - (w.p - w.q) ^ 2 := by linarith
  have h2 : 2 - (w.p - w.q) ^ 2 = 1 + 4 * (w.p * w.q) := by rw [hq]; ring
  refine ⟨h1 ▸ schmidt_chsh_isGreatest_concurrence w, by rw [h2], fun hp => ?_, fun h0 => ?_⟩
  · rw [h2, hq, hp]
    norm_num
  · rw [h2, h0]
    norm_num

/-! ## Proposition `rem:entanglement-definition`(v): the Werner interval -/

/-- For `1/3 < t ≤ 1/√2` the Werner density is entangled and every four sign tests have absolute
CHSH score at most two. -/
theorem werner_interval (t : ℝ) (h1 : 1 / 3 < t) (h2 : t ≤ 1 / Real.sqrt 2) :
    ¬ IsSeparable (wernerState t) ∧
      ∀ a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ, PairBell.SignTest a₀ → PairBell.SignTest a₁ →
        PairBell.SignTest b₀ → PairBell.SignTest b₁ →
          |signScore (wernerState t) a₀ a₁ b₀ b₁| ≤ 2 :=
  ⟨werner_entangled t h1, fun a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁ =>
    werner_abs_chsh_le_two t (by linarith) h2 a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁⟩

/-- The value `t = 1/2` lies in the Werner interval and supplies such a density. -/
theorem werner_half :
    ¬ IsSeparable (wernerState (1 / 2)) ∧
      ∀ a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ, PairBell.SignTest a₀ → PairBell.SignTest a₁ →
        PairBell.SignTest b₀ → PairBell.SignTest b₁ →
          |signScore (wernerState (1 / 2)) a₀ a₁ b₀ b₁| ≤ 2 := by
  apply werner_interval
  · norm_num
  · rw [le_div_iff₀ (by positivity)]
    have : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith

/-! ## Theorem `thm:resolved-pair`: the complex trace is real and its modulus is bounded -/

open scoped Kronecker ComplexOrder in
/-- Theorem `thm:resolved-pair` for the complex trace: the trace of `ρ` against the CHSH operator
of four sign tests is a real number, and its modulus is at most `2 √(2 - r²)`, with `r²` the
squared Bloch length of the first pair. -/
theorem chsh_trace_real_bound (ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (a₀ a₁ b₀ b₁ : Matrix Bool Bool ℂ) (ha₀ : PairBell.SignTest a₀)
    (ha₁ : PairBell.SignTest a₁) (hb₀ : PairBell.SignTest b₀) (hb₁ : PairBell.SignTest b₁) :
    (ρ * (a₀ ⊗ₖ b₀ + a₀ ⊗ₖ b₁ + a₁ ⊗ₖ b₀ - a₁ ⊗ₖ b₁)).trace.im = 0 ∧
      ‖(ρ * (a₀ ⊗ₖ b₀ + a₀ ⊗ₖ b₁ + a₁ ⊗ₖ b₀ - a₁ ⊗ₖ b₁)).trace‖ ≤
        2 * Real.sqrt (2 - PairBell.localBlochSq ρ) := by
  have hB := chshOperator_hermitian a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
  have hR : ρ.IsHermitian := hρ.isHermitian
  have hstar : star (ρ * chshOperator a₀ a₁ b₀ b₁).trace =
      (ρ * chshOperator a₀ a₁ b₀ b₁).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hB.eq, hR.eq,
      Matrix.trace_mul_comm]
  have him : (ρ * chshOperator a₀ a₁ b₀ b₁).trace.im = 0 := Complex.conj_eq_iff_im.1 hstar
  refine ⟨him, ?_⟩
  have hre : (ρ * chshOperator a₀ a₁ b₀ b₁).trace = ((signScore ρ a₀ a₁ b₀ b₁ : ℝ) : ℂ) :=
    Complex.ext (by simp [signScore]) (by simp [him])
  change ‖(ρ * chshOperator a₀ a₁ b₀ b₁).trace‖ ≤ _
  rw [hre, Complex.norm_real, Real.norm_eq_abs]
  exact mixedExcess_abs ρ hρ htr a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁

/-! ## Proposition `prop:purified-fiber`(i): the marginal on the second copy -/

section PurifiedSecondCopy

open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction
open OperatorKO7.Meta.BoundaryObserver.PurifiedFiber

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Proposition `prop:purified-fiber`(i) on the second copy: the marginal of the purified fiber on
the second copy is the uniform law on the fiber, as on the first copy. -/
theorem marginalRight_purifiedFiber (C : Finset X) :
    Thermal.marginalRight (pureDensity (purifiedFiber C)) =
      Thermal.realDiagonal (fiberWeight C) := by
  have hswap : (fun z : X × X => purifiedFiber C z.swap) = purifiedFiber C := by
    funext z
    unfold purifiedFiber
    by_cases h : z.1 = z.2
    · simp [Prod.swap, h]
    · have h' : ¬ z.2 = z.1 := fun e => h e.symm
      simp [Prod.swap, h, h']
  have hgen : ∀ v : X × X → ℂ, Thermal.marginalRight (pureDensity v) =
      Thermal.marginalLeft (pureDensity (fun z => v z.swap)) := by
    intro v
    ext r s
    simp [Thermal.marginalLeft, Thermal.marginalRight, pureDensity, Prod.swap]
  rw [hgen, hswap, marginal_purifiedFiber]

/-- Proposition `prop:purified-fiber`(i) on the second copy, in bits: the entropy of the marginal of
the purified fiber on the second copy is `log₂ n` for a fiber of `n` states. -/
theorem entropy_marginalRight_purifiedFiber_bits (C : Finset X) (hC : C.Nonempty) :
    Thermal.entropy (Thermal.marginalRight (pureDensity (purifiedFiber C))) / Real.log 2 =
      Real.logb 2 C.card := by
  rw [marginalRight_purifiedFiber, ← marginal_purifiedFiber]
  exact entropy_marginal_purifiedFiber_bits C hC

end PurifiedSecondCopy

end OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleQuantumPair
