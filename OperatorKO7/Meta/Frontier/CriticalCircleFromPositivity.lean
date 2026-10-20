import Mathlib

/-!
# Critical-circle mechanism from positive quadratic forms

This file isolates the elementary positive-form calculation used by the function-field model
example. Integer-lattice positivity is transported through rational scaling and continuity to the
real-vector discriminant and the critical-circle calculation. No consequence for the Riemann
hypothesis is claimed; the module records the mechanism only. The algebra is finite, over `Real`
and `Complex`, with explicit circle roots.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Frontier.CriticalCircleFromPositivity

open Complex

/-- The quadratic commit form `x ^ 2 + a * x * y + q * y ^ 2`. -/
def commitQuadratic (a q x y : ℝ) : ℝ :=
  x ^ 2 + a * x * y + q * y ^ 2

/--
A positive-semidefinite commit form over the real plane forces the
discriminant inequality. In the function-field example, a positive-semidefinite commit form
forces the zeta zeros of the instance onto the critical circle, after the root calculation
below.
-/
theorem critical_circle_of_posdef (a q : ℝ) (_hq : 0 < q)
    (hpos : ∀ x y : ℝ, 0 ≤ commitQuadratic a q x y) :
    a ^ 2 ≤ 4 * q := by
  have htest := hpos (-a) 2
  unfold commitQuadratic at htest
  nlinarith

/-- Nonnegativity of the commit quadratic at every integer vector. -/
def integerLatticePositivity (a q : ℝ) : Prop :=
  ∀ m n : ℤ, 0 ≤ commitQuadratic a q (m : ℝ) (n : ℝ)

/--
Compatibility carrier for lattice-to-real transport. The canonical
`integerLatticeTransportProved` below fills it with the proved homogeneous
quadratic transport.
-/
structure IntegerLatticeTransportCitation (a q : ℝ) where
  source : String
  theoremName : String
  applies :
    integerLatticePositivity a q →
      ∀ x y : ℝ, 0 ≤ commitQuadratic a q x y

/--
The original explicit-carrier interface for the integer-lattice form.
The direct theorem `critical_circle_of_integer_lattice` below requires no carrier.
-/
theorem critical_circle_of_integer_posdef (a q : ℝ) (hq : 0 < q)
    (C : IntegerLatticeTransportCitation a q)
    (hpos : integerLatticePositivity a q) :
    a ^ 2 ≤ 4 * q :=
  critical_circle_of_posdef a q hq (C.applies hpos)

/-- `X^2 - a X + q` evaluated at a complex point. -/
def quadraticValue (a q : ℝ) (z : ℂ) : ℂ :=
  z ^ 2 - (a : ℂ) * z + (q : ℂ)

/-- The upper explicit root in the nonpositive-discriminant case. -/
noncomputable def criticalRootPlus (a q : ℝ) : ℂ :=
  ((a / 2 : ℝ) : ℂ) +
    ((Real.sqrt (q - a ^ 2 / 4) : ℝ) : ℂ) * Complex.I

/-- The lower explicit root in the nonpositive-discriminant case. -/
noncomputable def criticalRootMinus (a q : ℝ) : ℂ :=
  ((a / 2 : ℝ) : ℂ) +
    ((-Real.sqrt (q - a ^ 2 / 4) : ℝ) : ℂ) * Complex.I

private lemma critical_root_sumsq (a q : ℝ) (hdisc : a ^ 2 ≤ 4 * q) :
    (a / 2) ^ 2 + (Real.sqrt (q - a ^ 2 / 4)) ^ 2 = q := by
  have hnonneg : 0 ≤ q - a ^ 2 / 4 := by
    nlinarith
  rw [Real.sq_sqrt hnonneg]
  ring

/-- The upper explicit root lies on the circle of radius `sqrt q`. -/
theorem criticalRootPlus_norm_eq_sqrt_q (a q : ℝ) (hq : 0 ≤ q)
    (hdisc : a ^ 2 ≤ 4 * q) :
    ‖criticalRootPlus a q‖ = Real.sqrt q := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg q)]
  rw [Complex.sq_norm, criticalRootPlus, Complex.normSq_add_mul_I,
    Real.sq_sqrt hq]
  exact critical_root_sumsq a q hdisc

/-- The lower explicit root lies on the circle of radius `sqrt q`. -/
theorem criticalRootMinus_norm_eq_sqrt_q (a q : ℝ) (hq : 0 ≤ q)
    (hdisc : a ^ 2 ≤ 4 * q) :
    ‖criticalRootMinus a q‖ = Real.sqrt q := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg q)]
  rw [Complex.sq_norm, criticalRootMinus, Complex.normSq_add_mul_I,
    Real.sq_sqrt hq]
  have hs := critical_root_sumsq a q hdisc
  ring_nf at hs ⊢
  exact hs

/-- The two explicit roots have modulus exactly `sqrt q`. -/
theorem critical_roots_on_circle (a q : ℝ) (hq : 0 ≤ q)
    (hdisc : a ^ 2 ≤ 4 * q) :
    ‖criticalRootPlus a q‖ = Real.sqrt q ∧
      ‖criticalRootMinus a q‖ = Real.sqrt q := by
  exact ⟨criticalRootPlus_norm_eq_sqrt_q a q hq hdisc,
    criticalRootMinus_norm_eq_sqrt_q a q hq hdisc⟩

/-- Factorization of `X^2 - a X + q` in the nonpositive-discriminant case. -/
theorem quadraticValue_factor_critical (a q : ℝ) (hdisc : a ^ 2 ≤ 4 * q)
    (z : ℂ) :
    quadraticValue a q z =
      (z - criticalRootPlus a q) * (z - criticalRootMinus a q) := by
  have hnonneg : 0 ≤ q - a ^ 2 / 4 := by
    nlinarith
  have hnonneg' : 0 ≤ a ^ 2 * (-1 / 4) + q := by
    nlinarith
  apply Complex.ext
  · simp [quadraticValue, criticalRootPlus, criticalRootMinus,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, pow_two]
    ring_nf
    rw [Real.sq_sqrt hnonneg']
    ring
  · simp [quadraticValue, criticalRootPlus, criticalRootMinus,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, pow_two]
    ring

/-- Any complex root of `X^2 - a X + q` lies on the circle of radius `sqrt q`. -/
theorem quadratic_root_norm_eq_sqrt_q (a q : ℝ) (hq : 0 ≤ q)
    (hdisc : a ^ 2 ≤ 4 * q) {z : ℂ}
    (hz : quadraticValue a q z = 0) :
    ‖z‖ = Real.sqrt q := by
  have hfactor := quadraticValue_factor_critical a q hdisc z
  rw [hfactor] at hz
  rcases mul_eq_zero.mp hz with hplus | hminus
  · have hz' : z = criticalRootPlus a q := sub_eq_zero.mp hplus
    rw [hz']
    exact criticalRootPlus_norm_eq_sqrt_q a q hq hdisc
  · have hz' : z = criticalRootMinus a q := sub_eq_zero.mp hminus
    rw [hz']
    exact criticalRootMinus_norm_eq_sqrt_q a q hq hdisc

#print axioms critical_circle_of_posdef
#print axioms critical_circle_of_integer_posdef
#print axioms criticalRootPlus_norm_eq_sqrt_q
#print axioms criticalRootMinus_norm_eq_sqrt_q
#print axioms critical_roots_on_circle
#print axioms quadraticValue_factor_critical
#print axioms quadratic_root_norm_eq_sqrt_q

/-! ## Kernel proof of the lattice-to-real transport

Homogeneity clears a
common rational denominator; closedness extends positivity to the real plane.
-/

/-- Clearing the two denominators transports integer positivity to rational vectors. -/
theorem integerLatticePositivity_rat (a q : ℝ) (hpos : integerLatticePositivity a q)
    (x y : ℚ) : 0 ≤ commitQuadratic a q (x : ℝ) (y : ℝ) := by
  have hx : (x.den : ℝ) ≠ 0 := by exact_mod_cast x.den_nz
  have hy : (y.den : ℝ) ≠ 0 := by exact_mod_cast y.den_nz
  have h := hpos (x.num * (y.den : ℤ)) (y.num * (x.den : ℤ))
  have hid :
      commitQuadratic a q ((x.num * (y.den : ℤ) : ℤ) : ℝ)
        ((y.num * (x.den : ℤ) : ℤ) : ℝ) =
      ((x.den : ℝ) * (y.den : ℝ)) ^ 2 * commitQuadratic a q (x : ℝ) (y : ℝ) := by
    simp only [Int.cast_mul, Int.cast_natCast, Rat.cast_def, commitQuadratic]
    field_simp
    ring
  rw [hid] at h
  have hp : 0 < ((x.den : ℝ) * (y.den : ℝ)) ^ 2 :=
    sq_pos_of_ne_zero (mul_ne_zero hx hy)
  by_contra hn
  exact (not_lt_of_ge h) (mul_neg_of_pos_of_neg hp (lt_of_not_ge hn))

/-- Polynomial continuity and rational density give positivity at every real vector. -/
theorem integerLatticePositivity_real (a q : ℝ) (hpos : integerLatticePositivity a q) :
    ∀ x y : ℝ, 0 ≤ commitQuadratic a q x y := by
  have hc : Continuous (fun z : ℝ × ℝ => commitQuadratic a q z.1 z.2) := by
    unfold commitQuadratic
    fun_prop
  exact Rat.denseRange_cast.induction_on₂ (isClosed_le continuous_const hc)
    (integerLatticePositivity_rat a q hpos)

/-- The integer and real positivity conditions coincide for this homogeneous form. -/
theorem integerLatticePositivity_iff_real (a q : ℝ) :
    integerLatticePositivity a q ↔ ∀ x y : ℝ, 0 ≤ commitQuadratic a q x y :=
  ⟨integerLatticePositivity_real a q, fun h m n => h m n⟩

/-- Completing the square gives the exact nonnegative-discriminant region. -/
theorem integerLatticePositivity_iff_discriminant (a q : ℝ) :
    integerLatticePositivity a q ↔ a ^ 2 ≤ 4 * q := by
  constructor
  · intro h
    have ht := integerLatticePositivity_real a q h (-a) 2
    unfold commitQuadratic at ht
    nlinarith
  · intro h m n
    have hid : 4 * commitQuadratic a q (m : ℝ) (n : ℝ) =
        (2 * (m : ℝ) + a * (n : ℝ)) ^ 2 + (4 * q - a ^ 2) * (n : ℝ) ^ 2 := by
      unfold commitQuadratic
      ring
    have hr : 0 ≤ (2 * (m : ℝ) + a * (n : ℝ)) ^ 2 +
        (4 * q - a ^ 2) * (n : ℝ) ^ 2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr h) (sq_nonneg _))
    rw [← hid] at hr
    linarith

/-- The historical transport record is now inhabited by a proved transport. -/
def integerLatticeTransportProved (a q : ℝ) : IntegerLatticeTransportCitation a q where
  source := "OperatorKO7.Meta.Frontier.CriticalCircleFromPositivity"
  theoremName := "integerLatticePositivity_real"
  applies := integerLatticePositivity_real a q

/-- The integer-lattice discriminant conclusion requires no citation premise. -/
theorem critical_circle_of_integer_lattice (a q : ℝ)
    (hpos : integerLatticePositivity a q) : a ^ 2 ≤ 4 * q :=
  (integerLatticePositivity_iff_discriminant a q).mp hpos

/-- Every actual root has the critical modulus directly from lattice positivity. -/
theorem quadratic_root_norm_of_integer_lattice (a q : ℝ)
    (hpos : integerLatticePositivity a q) {z : ℂ}
    (hz : quadraticValue a q z = 0) : ‖z‖ = Real.sqrt q := by
  have hd := critical_circle_of_integer_lattice a q hpos
  have hq : 0 ≤ q := by nlinarith [sq_nonneg a]
  exact quadratic_root_norm_eq_sqrt_q a q hq hd hz

/-- The actual symmetric matrix of the binary quadratic form. -/
noncomputable def commitMatrix (a q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, a / 2; a / 2, q]

/-- Integer positivity also gives positive semidefiniteness of the actual matrix. -/
theorem commitMatrix_posSemidef (a q : ℝ) (hpos : integerLatticePositivity a q) :
    (commitMatrix a q).PosSemidef := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [commitMatrix, Matrix.conjTranspose_apply]
  · intro v
    have h := integerLatticePositivity_real a q hpos (v 0) (v 1)
    convert h using 1
    simp [commitMatrix, commitQuadratic, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-! ## Generic transport for homogeneous functions of degree two

The floors of `n x` form integer vectors; homogeneity of degree two moves their sign to the
rescaled vectors `⌊n x⌋ / n`, which converge to `x`. -/

/-- On a finite index type, a continuous function on real vectors that is homogeneous of
degree two and nonnegative at every integer vector is nonnegative at every real vector. -/
theorem homogeneous_nonneg_of_integer_nonneg {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ) (hcont : Continuous f)
    (hhom : ∀ (t : ℝ) (x : ι → ℝ), f (t • x) = t ^ 2 * f x)
    (hint : ∀ m : ι → ℤ, 0 ≤ f (fun i => (m i : ℝ))) (x : ι → ℝ) : 0 ≤ f x := by
  let g : ℕ → ι → ℝ := fun n i => (⌊(n : ℝ) * x i⌋ : ℝ) / n
  have hg : Filter.Tendsto g Filter.atTop (nhds x) := by
    rw [tendsto_pi_nhds]
    intro i
    have hlow : ∀ᶠ n : ℕ in Filter.atTop, x i - 1 / (n : ℝ) ≤ g n i := by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      show x i - 1 / (n : ℝ) ≤ (⌊(n : ℝ) * x i⌋ : ℝ) / n
      rw [le_div_iff₀ hn', sub_mul, one_div, inv_mul_cancel₀ hn'.ne']
      have := Int.lt_floor_add_one ((n : ℝ) * x i)
      linarith
    have hup : ∀ᶠ n : ℕ in Filter.atTop, g n i ≤ x i := by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      show (⌊(n : ℝ) * x i⌋ : ℝ) / n ≤ x i
      rw [div_le_iff₀ hn']
      have := Int.floor_le ((n : ℝ) * x i)
      linarith
    have hlim : Filter.Tendsto (fun n : ℕ => x i - 1 / (n : ℝ)) Filter.atTop (nhds (x i)) := by
      simpa using tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlow hup
  have hpos : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ f (g n) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hn0 : (n : ℝ) ≠ 0 := hn'.ne'
    have hscale : (n : ℝ) • g n = fun i => ((⌊(n : ℝ) * x i⌋ : ℤ) : ℝ) := by
      funext i
      show (n : ℝ) * ((⌊(n : ℝ) * x i⌋ : ℝ) / n) = ((⌊(n : ℝ) * x i⌋ : ℤ) : ℝ)
      field_simp
    have h : 0 ≤ f ((n : ℝ) • g n) := by
      rw [hscale]
      exact hint _
    rw [hhom] at h
    by_contra hneg
    exact (not_lt_of_ge h) (mul_neg_of_pos_of_neg (pow_pos hn' 2) (lt_of_not_ge hneg))
  exact ge_of_tendsto ((hcont.tendsto x).comp hg) hpos

/-- The binary transport is `homogeneous_nonneg_of_integer_nonneg` at the commit form on
`Fin 2 → ℝ`. -/
theorem integerLatticePositivity_real_of_homogeneous (a q : ℝ)
    (hpos : integerLatticePositivity a q) (x y : ℝ) : 0 ≤ commitQuadratic a q x y := by
  have h := homogeneous_nonneg_of_integer_nonneg
    (fun v : Fin 2 → ℝ => commitQuadratic a q (v 0) (v 1))
    (by unfold commitQuadratic; fun_prop)
    (fun t v => by simp only [Pi.smul_apply, smul_eq_mul, commitQuadratic]; ring)
    (fun m => hpos (m 0) (m 1)) ![x, y]
  simpa using h

#check @homogeneous_nonneg_of_integer_nonneg
#print axioms homogeneous_nonneg_of_integer_nonneg
#check @integerLatticePositivity_real_of_homogeneous
#print axioms integerLatticePositivity_real_of_homogeneous
#check @integerLatticePositivity_rat
#print axioms integerLatticePositivity_rat
#check @integerLatticePositivity_real
#print axioms integerLatticePositivity_real
#check @integerLatticePositivity_iff_real
#print axioms integerLatticePositivity_iff_real
#check @integerLatticePositivity_iff_discriminant
#print axioms integerLatticePositivity_iff_discriminant
#check @integerLatticeTransportProved
#print axioms integerLatticeTransportProved
#check @critical_circle_of_integer_lattice
#print axioms critical_circle_of_integer_lattice
#check @quadratic_root_norm_of_integer_lattice
#print axioms quadratic_root_norm_of_integer_lattice
#check @commitMatrix
#print axioms commitMatrix
#check @commitMatrix_posSemidef
#print axioms commitMatrix_posSemidef

end OperatorKO7.Meta.Frontier.CriticalCircleFromPositivity
