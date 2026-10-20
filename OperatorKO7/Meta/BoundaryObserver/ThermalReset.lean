import OperatorKO7.Meta.BoundaryObserver.BoundarySingularityQuantum

set_option autoImplicit false

/-!
# The merge as a limit point: approximate reset by a swap with a finite bath

Graph: Audit/ledgers/operational-inexpressibility/THERMAL-RESET-PROOF-GRAPH.md, R1 to R5.
The swap of the system with a reservoir of the same dimension is a thermal operation of
BoundaryReconstruction.Thermal. Its output system state is the reservoir Gibbs state, its reservoir
holds the input, its heat is the mean reservoir energy of the input less the Gibbs mean energy, and
its balance β Q = S(ρ) − S(γ) + D(ρ‖γ) holds with the relative entropy as the exact Landauer deficit.
For a two-level reservoir of gap E the output entropy is h₂(1/(1 + e^{βE})), tending to zero as E
grows, so every state is reset below any positive entropy by a finite operation, while
no_exact_thermal_erasure keeps every such output above zero: the merge is a limit point and never
a point. Relation: finite matrices over the complex numbers. External trust: none.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ThermalReset

open Matrix
open BoundaryReconstruction.Thermal
open BoundarySingularity.Thermal
open Filter Topology
open scoped Kronecker ComplexOrder BigOperators

noncomputable section

/-! ## R1: the swap -/

section Swap
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The permutation matrix exchanging the system and reservoir coordinates. -/
def swapMatrix : Matrix (ι × ι) (ι × ι) ℂ := fun x z => if z = x.swap then 1 else 0

omit [Fintype ι] [DecidableEq ι] in
theorem swap_eq_iff (x y : ι × ι) : y = x.swap ↔ x = y.swap := by
  constructor
  · intro h
    rw [h, Prod.swap_swap]
  · intro h
    rw [h, Prod.swap_swap]

theorem swapMatrix_mul_apply (m : Matrix (ι × ι) (ι × ι) ℂ) (x y : ι × ι) :
    ((swapMatrix : Matrix (ι × ι) (ι × ι) ℂ) * m) x y = m x.swap y := by
  simp only [Matrix.mul_apply, swapMatrix, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem mul_swapMatrix_apply (m : Matrix (ι × ι) (ι × ι) ℂ) (x y : ι × ι) :
    (m * (swapMatrix : Matrix (ι × ι) (ι × ι) ℂ)) x y = m x y.swap := by
  simp only [Matrix.mul_apply, swapMatrix]
  have hs : ∀ z : ι × ι, (y = z.swap) ↔ (z = y.swap) := fun z => swap_eq_iff z y
  simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit [Fintype ι] in
theorem star_swapMatrix : star (swapMatrix : Matrix (ι × ι) (ι × ι) ℂ) = swapMatrix := by
  ext x y
  simp only [Matrix.star_apply, swapMatrix, swap_eq_iff x y]
  split_ifs <;> simp

theorem swapMatrix_mul_self : (swapMatrix : Matrix (ι × ι) (ι × ι) ℂ) * swapMatrix = 1 := by
  ext x y
  rw [swapMatrix_mul_apply, Matrix.one_apply]
  simp only [swapMatrix, Prod.swap_swap]
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

/-- The swap as a unitary on the joint space; both inverse equations are proved. -/
def swapUnitary : Matrix.unitaryGroup (ι × ι) ℂ := by
  refine ⟨swapMatrix, ?_, ?_⟩
  · rw [star_swapMatrix, swapMatrix_mul_self]
  · rw [star_swapMatrix, swapMatrix_mul_self]

theorem swapUnitary_coe :
    ((swapUnitary : Matrix.unitaryGroup (ι × ι) ℂ) : Matrix (ι × ι) (ι × ι) ℂ) = swapMatrix := rfl

/-- Conjugation by the swap exchanges the two tensor factors. -/
theorem rotate_swap_kronecker (a b : Matrix ι ι ℂ) :
    rotate swapUnitary (a ⊗ₖ b) = b ⊗ₖ a := by
  ext x y
  rw [rotate, swapUnitary_coe, star_swapMatrix, mul_swapMatrix_apply, swapMatrix_mul_apply]
  simp only [Matrix.kroneckerMap_apply, Prod.fst_swap, Prod.snd_swap]
  exact mul_comm _ _

end Swap

section Marginals
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- The system marginal of a tensor product is the system factor times the reservoir trace. -/
theorem marginalLeft_kronecker (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ) :
    marginalLeft (a ⊗ₖ b) = b.trace • a := by
  ext i j
  simp only [marginalLeft, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.trace, Matrix.diag]
  rw [← Finset.mul_sum]
  exact mul_comm _ _

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The reservoir marginal of a tensor product is the reservoir factor times the system trace. -/
theorem marginalRight_kronecker (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ) :
    marginalRight (a ⊗ₖ b) = a.trace • b := by
  ext r s
  simp only [marginalRight, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.trace, Matrix.diag]
  rw [← Finset.sum_mul]

end Marginals

/-! ## R2: the swap as a thermal operation -/

section SwapThermal
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem swap_joint (rho : Matrix ι ι ℂ) {h : Matrix ι ι ℂ} (hh : h.IsHermitian) (β : ℝ) :
    thermalJoint swapUnitary rho hh β = gibbsState hh β ⊗ₖ rho := by
  rw [thermalJoint, rotate_swap_kronecker]

/-- After the swap the system holds the Gibbs state of the reservoir. -/
theorem swap_output (rho : Matrix ι ι ℂ) (htr : rho.trace = 1) {h : Matrix ι ι ℂ}
    (hh : h.IsHermitian) (β : ℝ) :
    marginalLeft (thermalJoint swapUnitary rho hh β) = gibbsState hh β := by
  rw [swap_joint, marginalLeft_kronecker, htr, one_smul]

/-- After the swap the reservoir holds the input state. -/
theorem swap_reservoir (rho : Matrix ι ι ℂ) {h : Matrix ι ι ℂ} (hh : h.IsHermitian) (β : ℝ) :
    marginalRight (thermalJoint swapUnitary rho hh β) = rho := by
  rw [swap_joint, marginalRight_kronecker, gibbsState_trace, one_smul]

theorem swap_output_entropy (rho : Matrix ι ι ℂ) (htr : rho.trace = 1) {h : Matrix ι ι ℂ}
    (hh : h.IsHermitian) (β : ℝ) :
    entropy (marginalLeft (thermalJoint swapUnitary rho hh β)) = entropy (gibbsState hh β) := by
  rw [swap_output rho htr hh β]

/-- The heat of the swap is the reservoir energy of the input less the Gibbs mean energy. -/
theorem swap_heat (rho : Matrix ι ι ℂ) {h : Matrix ι ι ℂ} (hh : h.IsHermitian) (β : ℝ) :
    reservoirHeat swapUnitary rho hh β = meanEnergy h (rho - gibbsState hh β) := by
  rw [reservoirHeat, swap_reservoir]

/-- The exact balance of the swap: β Q = S(ρ) − S(γ) + D(ρ‖γ), with the relative entropy as the
whole Landauer deficit of this operation. -/
theorem swap_balance (rho : Matrix ι ι ℂ) (hrho : rho.PosSemidef) (htr : rho.trace = 1)
    {h : Matrix ι ι ℂ} (hh : h.IsHermitian) (β : ℝ) :
    β * reservoirHeat swapUnitary rho hh β =
        entropy rho - entropy (gibbsState hh β) + relativeEntropy rho (gibbsState hh β) ∧
      0 ≤ relativeEntropy rho (gibbsState hh β) := by
  rw [swap_heat]
  exact gibbs_bath_balance hh β hrho htr

end SwapThermal

/-! ## R3: the two-level reservoir and its vanishing Gibbs entropy -/

/-- The two-level reservoir Hamiltonian with ground energy zero and gap E, in joules. -/
def twoLevel (E : ℝ) : Matrix Bool Bool ℂ := realDiagonal (fun b => if b then E else 0)

theorem twoLevel_hermitian (E : ℝ) : (twoLevel E).IsHermitian := realDiagonal_hermitian _

/-- The Gibbs state of the two-level reservoir is diagonal with the Gibbs weights of its levels. -/
theorem twoLevel_gibbs (E β : ℝ) :
    gibbsState (twoLevel_hermitian E) β =
      realDiagonal (gibbsWeight β (fun b : Bool => if b then E else 0)) := by
  have hz : spectralLift (1 : Matrix.unitaryGroup Bool ℂ) (fun b : Bool => if b then E else 0) =
      twoLevel E := by
    simp [spectralLift, rotate, twoLevel]
  have hg := gibbsState_spectralLift (1 : Matrix.unitaryGroup Bool ℂ)
    (fun b : Bool => if b then E else 0) β
  rw [gibbsState_congr (twoLevel_hermitian E) (spectralLift_hermitian 1 _) hz.symm β, hg]
  simp [spectralLift, rotate]

/-- The excited-level weight of the two-level Gibbs state. -/
theorem twoLevel_weight_true (E β : ℝ) :
    gibbsWeight β (fun b : Bool => if b then E else 0) true = 1 / (1 + Real.exp (β * E)) := by
  unfold gibbsWeight partition
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, mul_zero, Real.exp_zero]
  have h1 : Real.exp (-β * E) * Real.exp (β * E) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [div_eq_div_iff (by positivity) (by positivity), mul_add, mul_one, h1, one_mul]

theorem twoLevel_weight_false (E β : ℝ) :
    gibbsWeight β (fun b : Bool => if b then E else 0) false = 1 - 1 / (1 + Real.exp (β * E)) := by
  have hs := gibbsWeight_sum β (fun b : Bool => if b then E else 0)
  rw [Fintype.sum_bool, twoLevel_weight_true] at hs
  linarith

/-- The two-level Gibbs entropy is the binary entropy of the excited weight, in nats. -/
theorem twoLevel_entropy (E β : ℝ) :
    entropy (gibbsState (twoLevel_hermitian E) β) =
      Real.binEntropy (1 / (1 + Real.exp (β * E))) := by
  rw [twoLevel_gibbs]
  have hl : realDiagonal (gibbsWeight β (fun b : Bool => if b then E else 0)) =
      spectralLift (1 : Matrix.unitaryGroup Bool ℂ)
        (gibbsWeight β (fun b : Bool => if b then E else 0)) := by
    simp [spectralLift, rotate]
  rw [hl, entropy_spectralLift, Fintype.sum_bool, twoLevel_weight_true, twoLevel_weight_false,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem twoLevel_weight_tendsto (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun E : ℝ => 1 / (1 + Real.exp (β * E))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun E : ℝ => β * E) atTop atTop := tendsto_id.const_mul_atTop hβ
  have h2 : Tendsto (fun E : ℝ => Real.exp (β * E)) atTop atTop := Real.tendsto_exp_atTop.comp h1
  have h3 : Tendsto (fun E : ℝ => 1 + Real.exp (β * E)) atTop atTop :=
    tendsto_const_nhds.add_atTop h2
  simpa only [one_div] using tendsto_inv_atTop_zero.comp h3

/-- As the gap grows at fixed positive β, the two-level Gibbs entropy tends to zero. -/
theorem twoLevel_entropy_tendsto (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun E : ℝ => entropy (gibbsState (twoLevel_hermitian E) β)) atTop (𝓝 0) := by
  simp only [twoLevel_entropy]
  have hc := (Real.binEntropy_continuous.tendsto 0).comp (twoLevel_weight_tendsto β hβ)
  simpa [Function.comp_def, Real.binEntropy_zero] using hc

/-! ## R4: the approximate reset with its heat -/

/-- Every density matrix is reset below any positive entropy by one swap with a two-level
reservoir of large enough gap. -/
theorem approximate_reset {rho : Matrix Bool Bool ℂ} (htr : rho.trace = 1) (β : ℝ) (hβ : 0 < β)
    (η : ℝ) (hη : 0 < η) :
    ∃ E : ℝ, entropy (marginalLeft (thermalJoint swapUnitary rho (twoLevel_hermitian E) β)) < η := by
  have ht := twoLevel_entropy_tendsto β hβ
  obtain ⟨E, hE⟩ := ((tendsto_order.1 ht).2 η hη).exists
  exact ⟨E, by rwa [swap_output rho htr]⟩

/-- The heat of the two-level swap is the gap times the excited population the system loses. -/
theorem twoLevel_swap_heat (rho : Matrix Bool Bool ℂ) (E β : ℝ) :
    reservoirHeat swapUnitary rho (twoLevel_hermitian E) β =
      E * ((rho true true).re - 1 / (1 + Real.exp (β * E))) := by
  rw [swap_heat, twoLevel_gibbs, meanEnergy]
  simp only [twoLevel, realDiagonal, Matrix.trace, Matrix.diag, Fintype.sum_bool,
    Matrix.diagonal_mul, Matrix.sub_apply, Matrix.diagonal_apply_eq, twoLevel_weight_true,
    if_true, Bool.false_eq_true, if_false, Complex.ofReal_zero, zero_mul,
    add_zero, Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re]

/-- The balance of the two-level swap, with the Gibbs entropy in closed form. -/
theorem twoLevel_swap_balance {rho : Matrix Bool Bool ℂ} (hrho : rho.PosSemidef)
    (htr : rho.trace = 1) (E β : ℝ) :
    β * reservoirHeat swapUnitary rho (twoLevel_hermitian E) β =
        entropy rho - Real.binEntropy (1 / (1 + Real.exp (β * E))) +
          relativeEntropy rho (gibbsState (twoLevel_hermitian E) β) ∧
      0 ≤ relativeEntropy rho (gibbsState (twoLevel_hermitian E) β) := by
  have h := swap_balance rho hrho htr (twoLevel_hermitian E) β
  rw [twoLevel_entropy] at h
  exact h

/-! ## R5: the merge is a limit point and never a point -/

/-- Every finite thermal operation leaves a full-rank state with positive entropy, and for every
positive η some finite operation leaves it below η. -/
theorem reset_boundary {rho : Matrix Bool Bool ℂ} (hrho : rho.PosDef) (htr : rho.trace = 1)
    (β : ℝ) (hβ : 0 < β) :
    (∀ {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ] (u : Matrix.unitaryGroup (Bool × κ) ℂ)
      {h : Matrix κ κ ℂ} (hh : h.IsHermitian),
      0 < entropy (marginalLeft (thermalJoint u rho hh β))) ∧
    (∀ η : ℝ, 0 < η → ∃ E : ℝ,
      entropy (marginalLeft (thermalJoint swapUnitary rho (twoLevel_hermitian E) β)) < η) := by
  constructor
  · intro κ _ _ _ u h hh
    exact no_exact_thermal_erasure u hrho htr hh β
  · exact fun η hη => approximate_reset htr β hβ η hη

/-- The fair pair is reset below any positive η by a finite operation, at a heat above
(log 2 − η)/β; its exact erasure needs the limit. -/
theorem fair_pair_reset (β : ℝ) (hβ : 0 < β) (η : ℝ) (hη : 0 < η) :
    ∃ E : ℝ,
      entropy (marginalLeft (thermalJoint swapUnitary fairPair (twoLevel_hermitian E) β)) < η ∧
      (Real.log 2 - η) / β < reservoirHeat swapUnitary fairPair (twoLevel_hermitian E) β := by
  obtain ⟨E, hE⟩ := approximate_reset fairPair_trace β hβ η hη
  refine ⟨E, hE, ?_⟩
  have hl := landauer_from_unitary swapUnitary fairPair_posDef.posSemidef fairPair_trace
    (twoLevel_hermitian E) β hβ
  rw [fairPair_entropy] at hl
  have hlt : (Real.log 2 - η) / β <
      (Real.log 2 - entropy (marginalLeft (thermalJoint swapUnitary fairPair
        (twoLevel_hermitian E) β))) / β := by
    apply div_lt_div_of_pos_right _ hβ
    linarith
  exact hlt.trans_le hl

end

end OperatorKO7.Meta.BoundaryObserver.ThermalReset
