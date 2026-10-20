import OperatorKO7.Meta.BoundaryObserver.PurifiedFiber
import OperatorKO7.Meta.BoundaryObserver.ConditionalReset

/-!
# The purified fiber under every law: record projections and the record-object state

Manuscript: Proposition `prop:purified-fiber`, the law-weighted record
projection of part (iii) and the record-object state of part (v).

For a law `p` on a finite `X` and an observer `q : X → Y`, the weighted copy
`ψ_p = ∑ₓ √p(x) |x⟩|x⟩` has record projection `(Π_y ⊗ I) ψ_p = √P(q = y) · ψ_{p(· | y)}`, Born
mass `P(q = y)`, branch marginal `p(· | y)` with entropy `H(X | q(X) = y)`, and expected branch
entropy `H(X | q(X)) = H(p) - H(q(X))`. For a law constant on every fiber the branch is the uniform
purified fiber and the branch entropy is `log n_y`. The record-object state
`χ_p = ∑ₓ √p(x) |x⟩|q(x)⟩` has the Schmidt form `∑_y √P(q = y) v_y ⊗ e_y` with orthonormal fiber
vectors `v_y` over the attained records, its record marginal is the diagonal law of `q(X)`, its
entanglement entropy is `H(q(X)) = I(X; q(X))`, and the remaining `H(X | q(X))` sits inside the
fibers.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators ComplexOrder
open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction
open OperatorKO7.Meta.BoundaryObserver.PurifiedFiber
open OperatorKO7.Meta.BoundaryObserver.ConditionalReset

namespace OperatorKO7.Meta.BoundaryObserver.PurifiedFiberGeneralLaw

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The weighted copy `ψ_p = ∑ₓ √p(x) |x⟩|x⟩`. -/
noncomputable def weightedCopy (p : X → ℝ) : X × X → ℂ :=
  fun z => if z.1 = z.2 then (Real.sqrt (p z.1) : ℂ) else 0

theorem sqrt_mass_mul_sqrt_cond (p : X → ℝ) (q : X → Y) (hp : ∀ x, 0 ≤ p x) (x : X) :
    Real.sqrt (recordMass p q (q x)) * Real.sqrt (condLaw p q (q x) x) = Real.sqrt (p x) := by
  rw [← Real.sqrt_mul (recordMass_nonneg p q hp _)]
  congr 1
  unfold condLaw
  rw [if_pos rfl]
  rcases (recordMass_nonneg p q hp (q x)).eq_or_lt with h0 | h0
  · have hx := le_recordMass p q hp x
    rw [← h0] at hx ⊢
    have : p x = 0 := le_antisymm hx (hp x)
    rw [this]
    ring
  · field_simp

/-- **The law-weighted record projection:** `(Π_y ⊗ I) ψ_p = √P(q = y) · ψ_{p(· | y)}`. -/
theorem recordProjection_weightedCopy (p : X → ℝ) (q : X → Y) (hp : ∀ x, 0 ≤ p x) (y : Y) :
    recordProjector q y (weightedCopy p) =
      (Real.sqrt (recordMass p q y) : ℂ) • weightedCopy (condLaw p q y) := by
  funext z
  rcases z with ⟨i, j⟩
  simp only [recordProjector, weightedCopy, Pi.smul_apply, smul_eq_mul]
  by_cases hi : q i = y
  · subst hi
    by_cases hij : i = j
    · subst hij
      simp only [if_true, if_pos rfl]
      rw [← Complex.ofReal_mul, sqrt_mass_mul_sqrt_cond p q hp i]
    · simp [hij]
  · have hc : condLaw p q y i = 0 := by simp [condLaw, hi]
    by_cases hij : i = j
    · subst hij
      simp [hi, hc]
    · simp [hi, hij]

/-- The Born mass of the record `y` is `P(q = y)`. -/
theorem bornMass_recordProjection_weightedCopy (p : X → ℝ) (q : X → Y) (hp : ∀ x, 0 ≤ p x)
    (y : Y) : bornMass (recordProjector q y (weightedCopy p)) = recordMass p q y := by
  unfold bornMass recordMass
  rw [Fintype.sum_prod_type, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => q x = y)]
  have hout : ∑ x ∈ Finset.univ.filter (fun x => ¬ q x = y),
      ∑ x', Complex.normSq (recordProjector q y (weightedCopy p) (x, x')) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      rw [Finset.mem_filter] at hx
      simp [recordProjector, hx.2]
  rw [hout, add_zero]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mem_filter] at hx
  rw [Finset.sum_eq_single x]
  · simp [recordProjector, weightedCopy, hx.2, Complex.normSq_ofReal, Real.mul_self_sqrt (hp x)]
  · intro x' _ hx'
    simp [recordProjector, weightedCopy, hx.2, Ne.symm hx']
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- The marginal of the weighted copy on the first copy is the diagonal law. -/
theorem marginal_weightedCopy (r : X → ℝ) (hr : ∀ x, 0 ≤ r x) :
    Thermal.marginalLeft (pureDensity (weightedCopy r)) = Thermal.realDiagonal r := by
  ext i j
  simp only [Thermal.marginalLeft, pureDensity, weightedCopy, Thermal.realDiagonal,
    Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst hij
      simp only [if_true]
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hr i)]
    · simp [hij, Ne.symm hij]
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The branch of a record of positive mass has marginal entropy `H(X | q(X) = y)`. -/
theorem entropy_branch (p : X → ℝ) (q : X → Y) (hp : ∀ x, 0 ≤ p x) (y : Y) :
    Thermal.entropy (Thermal.marginalLeft (pureDensity (weightedCopy (condLaw p q y)))) =
      shannon (condLaw p q y) := by
  rw [marginal_weightedCopy _ (condLaw_nonneg p q hp y), PurifiedFiber.entropy_realDiagonal]
  rfl

/-- **The expected branch entropy** is `H(X | q(X)) = H(p) - H(q(X))`. -/
theorem expected_branch_entropy (p : X → ℝ) (q : X → Y) (hp : ∀ x, 0 ≤ p x) :
    ∑ y, recordMass p q y *
        Thermal.entropy (Thermal.marginalLeft (pureDensity (weightedCopy (condLaw p q y)))) =
      condEntropy p q ∧
    condEntropy p q = shannon p - shannon (recordMass p q) := by
  refine ⟨?_, condEntropy_chain p q hp⟩
  unfold condEntropy
  exact Finset.sum_congr rfl fun y _ => by rw [entropy_branch p q hp y]

/-! ## A law constant on every fiber -/

theorem fiber_eq_filter (q : X → Y) (y : Y) :
    fiber q y = Finset.univ.filter (fun x => q x = y) := by
  ext x
  simp [mem_fiber]

/-- For a law constant on every fiber, the conditional law of an attained record is the uniform
law on its fiber. -/
theorem condLaw_of_fiberConstant (μ : X → ℝ) (q : X → Y)
    (hconst : ∀ x x', q x = q x' → μ x = μ x') (y : Y) (hm : 0 < recordMass μ q y) :
    condLaw μ q y = fiberWeight (fiber q y) := by
  funext x
  unfold condLaw fiberWeight
  by_cases hx : q x = y
  · rw [if_pos hx, if_pos ((mem_fiber q y x).2 hx)]
    have hsum : recordMass μ q y = (fiber q y).card * μ x := by
      unfold recordMass
      rw [← fiber_eq_filter, Finset.sum_congr rfl fun x' hx' =>
        hconst x' x (((mem_fiber q y x').1 hx').trans hx.symm), Finset.sum_const, nsmul_eq_mul]
    have hcard : (0 : ℝ) < (fiber q y).card := by
      have := Finset.card_pos.2 ⟨x, (mem_fiber q y x).2 hx⟩
      exact_mod_cast this
    have hμ : 0 < μ x := by
      rw [hsum] at hm
      exact pos_of_mul_pos_right hm hcard.le
    rw [hsum]
    field_simp
    ring
  · rw [if_neg hx, if_neg (fun h => hx ((mem_fiber q y x).1 h))]

theorem weightedCopy_fiberWeight (C : Finset X) :
    weightedCopy (fiberWeight C) = purifiedFiber C := by
  funext z
  rcases z with ⟨i, j⟩
  simp only [weightedCopy, purifiedFiber, fiberWeight]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ C <;> simp [hi]
  · simp [hij]

/-- **The fiber-constant record projection:** `(Π_y ⊗ I) ψ^μ = √μ(q⁻¹(y)) · ψ_{q⁻¹(y)}`, with
Born mass `μ(q⁻¹(y))` and branch entropy `log n_y`. -/
theorem recordProjection_fiberConstant (μ : X → ℝ) (q : X → Y) (hμ : ∀ x, 0 ≤ μ x)
    (hconst : ∀ x x', q x = q x' → μ x = μ x') (y : Y) (hm : 0 < recordMass μ q y) :
    recordProjector q y (weightedCopy μ) =
        (Real.sqrt (recordMass μ q y) : ℂ) • purifiedFiber (fiber q y) ∧
      bornMass (recordProjector q y (weightedCopy μ)) = recordMass μ q y ∧
      shannon (condLaw μ q y) = Real.log (fiber q y).card := by
  have hcond := condLaw_of_fiberConstant μ q hconst y hm
  refine ⟨?_, bornMass_recordProjection_weightedCopy μ q hμ y, ?_⟩
  · rw [recordProjection_weightedCopy μ q hμ y, hcond, weightedCopy_fiberWeight]
  · rw [hcond]
    unfold shannon
    rw [sum_negMulLog_fiberWeight]
    have hcard : (0 : ℝ) < (fiber q y).card := by
      by_contra hc
      push_neg at hc
      have h0 : (fiber q y).card = 0 := by exact_mod_cast le_antisymm hc (Nat.cast_nonneg _)
      have he : fiber q y = ∅ := Finset.card_eq_zero.1 h0
      have : recordMass μ q y = 0 := by
        unfold recordMass
        rw [← fiber_eq_filter, he, Finset.sum_empty]
      linarith
    rw [Real.negMulLog, Real.log_inv]
    field_simp

/-! ## The record-object state -/

/-- The record-object state `χ_p = ∑ₓ √p(x) |x⟩|q(x)⟩`. -/
noncomputable def recordObject (p : X → ℝ) (q : X → Y) : X × Y → ℂ :=
  fun z => if q z.1 = z.2 then (Real.sqrt (p z.1) : ℂ) else 0

/-- The Schmidt vector of the record `y`: `v_y(x) = √p(x | y)`. -/
noncomputable def schmidtVec (p : X → ℝ) (q : X → Y) (y : Y) : X → ℂ :=
  fun x => (Real.sqrt (condLaw p q y x) : ℂ)

/-- **The Schmidt form** `χ_p = ∑_y √P(q = y) · v_y ⊗ e_y`. -/
theorem recordObject_schmidt (p : X → ℝ) (q : X → Y) (hp : ∀ x, 0 ≤ p x) :
    recordObject p q = ∑ y, fun z : X × Y =>
      (Real.sqrt (recordMass p q y) : ℂ) * (schmidtVec p q y z.1 * if z.2 = y then 1 else 0) := by
  funext z
  rcases z with ⟨x, r⟩
  rw [Finset.sum_apply, Finset.sum_eq_single r]
  · simp only [recordObject, schmidtVec, if_true, mul_one]
    by_cases hx : q x = r
    · subst hx
      rw [if_pos rfl, ← Complex.ofReal_mul, sqrt_mass_mul_sqrt_cond p q hp x]
    · rw [if_neg hx]
      simp [condLaw, hx]
  · intro y _ hy
    simp [Ne.symm hy]
  · intro h
    exact absurd (Finset.mem_univ r) h

/-- **The Schmidt vectors of the attained records are orthonormal.** -/
theorem schmidtVec_orthonormal (p : X → ℝ) (q : X → Y) (hp : ∀ x, 0 ≤ p x) (y y' : Y)
    (hy : 0 < recordMass p q y) (hy' : 0 < recordMass p q y') :
    ∑ x, star (schmidtVec p q y x) * schmidtVec p q y' x = if y = y' then 1 else 0 := by
  by_cases h : y = y'
  · subst h
    rw [if_pos rfl]
    have hs := sum_condLaw p q y hy
    have : ∑ x, star (schmidtVec p q y x) * schmidtVec p q y x =
        ((∑ x, condLaw p q y x : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [schmidtVec, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (condLaw_nonneg p q hp y x)]
    rw [this, hs, Complex.ofReal_one]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun x _ => ?_
    simp only [schmidtVec, condLaw]
    by_cases hx : q x = y
    · have hx' : ¬ q x = y' := fun h' => h (hx.symm.trans h')
      simp [hx']
    · simp [hx]

/-- **The record marginal** of `χ_p` is the diagonal law of `q(X)`. -/
theorem marginal_recordObject (p : X → ℝ) (q : X → Y) (hp : ∀ x, 0 ≤ p x) :
    Thermal.marginalRight (pureDensity (recordObject p q)) =
      Thermal.realDiagonal (recordMass p q) := by
  ext r r'
  simp only [Thermal.marginalRight, pureDensity, recordObject, Thermal.realDiagonal,
    Matrix.diagonal_apply]
  by_cases h : r = r'
  · subst h
    simp only [if_true]
    unfold recordMass
    rw [Complex.ofReal_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : q x = r
    · rw [if_pos hx, if_pos hx, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hp x)]
    · rw [if_neg hx, if_neg hx, zero_mul]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : q x = r
    · have hx' : ¬ q x = r' := fun h' => h (hx.symm.trans h')
      simp [hx']
    · simp [hx]

/-- **The entanglement entropy** of `χ_p` is `H(q(X))`, and with the chain rule the remaining
`H(X | q(X)) = H(p) - H(q(X))` sits inside the fibers. -/
theorem entropy_recordObject (p : X → ℝ) (q : X → Y) (hp : ∀ x, 0 ≤ p x) :
    Thermal.entropy (Thermal.marginalRight (pureDensity (recordObject p q))) =
        shannon (recordMass p q) ∧
      shannon p = shannon (recordMass p q) + condEntropy p q := by
  refine ⟨?_, ?_⟩
  · rw [marginal_recordObject p q hp, PurifiedFiber.entropy_realDiagonal]
    rfl
  · rw [condEntropy_chain p q hp]
    ring

/-- The joint law of `(X, q(X))`. -/
noncomputable def jointLaw (p : X → ℝ) (q : X → Y) : X × Y → ℝ :=
  fun z => if q z.1 = z.2 then p z.1 else 0

/-- **`I(X; q(X)) = H(q(X))`**: the joint law of `X` and its record has the entropy of `X`. -/
theorem mutualInformation_record (p : X → ℝ) (q : X → Y) :
    shannon p + shannon (recordMass p q) - shannon (jointLaw p q) = shannon (recordMass p q) := by
  have hj : shannon (jointLaw p q) = shannon p := by
    unfold shannon
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single (q x)]
    · simp [jointLaw]
    · intro r _ hr
      simp [jointLaw, Ne.symm hr]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hj]
  ring

end OperatorKO7.Meta.BoundaryObserver.PurifiedFiberGeneralLaw
