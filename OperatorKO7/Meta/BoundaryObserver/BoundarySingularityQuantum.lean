import OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
import OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.BoundarySingularity

open scoped BigOperators

/-! ## S4: a full-rank state survives every finite thermal operation -/

namespace Thermal

open Matrix
open BoundaryReconstruction.Thermal
open scoped Kronecker ComplexOrder

noncomputable section

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A system vector placed in one reservoir coordinate. -/
def embedAt (r : κ) (v : ι → ℂ) : ι × κ → ℂ := fun x => if x.2 = r then v x.1 else 0

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem embedAt_ne_zero (r : κ) {v : ι → ℂ} (hv : v ≠ 0) : embedAt r v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hi := congrFun h (i, r)
  simpa [embedAt] using hi

omit [DecidableEq ι] in
/-- The system quadratic form is the sum of the joint quadratic forms over the embedded vectors. -/
theorem marginalLeft_quadratic (a : Matrix (ι × κ) (ι × κ) ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ (marginalLeft a *ᵥ v) = ∑ r, star (embedAt r v) ⬝ᵥ (a *ᵥ embedAt r v) := by
  have hst : ∀ (c : Prop) [Decidable c] (z : ℂ),
      star (if c then z else 0) = if c then star z else 0 := by
    intro c _ z
    split_ifs <;> simp
  calc star v ⬝ᵥ (marginalLeft a *ᵥ v)
      = ∑ i, ∑ j, ∑ r, star (v i) * (a (i, r) (j, r) * v j) := by
        simp only [dotProduct, Matrix.mulVec, marginalLeft, Pi.star_apply, Finset.sum_mul,
          Finset.mul_sum]
    _ = ∑ r, ∑ i, ∑ j, star (v i) * (a (i, r) (j, r) * v j) :=
        (Finset.sum_congr rfl (fun i _ => Finset.sum_comm)).trans Finset.sum_comm
    _ = ∑ r, star (embedAt r v) ⬝ᵥ (a *ᵥ embedAt r v) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        simp only [dotProduct, Matrix.mulVec, embedAt, Pi.star_apply, hst,
          Fintype.sum_prod_type, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel,
          Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]

omit [DecidableEq ι] in
/-- The system marginal of a positive definite joint matrix is positive definite. -/
theorem marginalLeft_posDef [Nonempty κ] {a : Matrix (ι × κ) (ι × κ) ℂ} (ha : a.PosDef) :
    (marginalLeft a).PosDef := by
  refine ⟨(marginalLeft_posSemidef ha.posSemidef).1, fun v hv => ?_⟩
  rw [marginalLeft_quadratic]
  have hr : ∀ r, 0 < star (embedAt r v) ⬝ᵥ (a *ᵥ embedAt r v) :=
    fun r => ha.2 (embedAt r v) (embedAt_ne_zero r hv)
  exact Finset.sum_pos (fun r _ => hr r) Finset.univ_nonempty

/-- A positive definite density matrix on at least two coordinates has positive entropy. -/
theorem entropy_pos_of_posDef [Nontrivial ι] {a : Matrix ι ι ℂ} (ha : a.PosDef)
    (hta : a.trace = 1) : 0 < entropy a := by
  rw [entropy_eq_eigenvalues ha.1]
  have hpos : ∀ i, 0 < ha.1.eigenvalues i := fun i => ha.eigenvalues_pos i
  have hsum : (∑ i, ha.1.eigenvalues i) = 1 := by
    rw [eigenvalues_sum_trace ha.1, hta]
    simp
  have hlt : ∀ i, ha.1.eigenvalues i < 1 := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne i
    have hle : ha.1.eigenvalues i + ha.1.eigenvalues j ≤ ∑ k, ha.1.eigenvalues k := by
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i, j} : Finset ι))
        (fun k _ _ => (hpos k).le)
      rwa [Finset.sum_pair (Ne.symm hj)] at hsub
    linarith [hpos j]
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro i _
  have h0 := hpos i
  have h1 := hlt i
  simp only [Real.negMulLog]
  exact mul_pos_of_neg_of_neg (by linarith) (Real.log_neg h0 h1)

/-- A spectral lift of a strictly positive spectrum is positive definite. -/
theorem spectralLift_posDef (u : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) (hp : ∀ i, 0 < p i) :
    (spectralLift u p).PosDef := by
  change ((u : Matrix ι ι ℂ) * realDiagonal p * (u : Matrix ι ι ℂ).conjTranspose).PosDef
  apply Matrix.PosDef.mul_mul_conjTranspose_same
  · apply Matrix.PosDef.diagonal
    intro i
    simpa using hp i
  · apply Matrix.vecMul_injective_of_isUnit
    exact (Group.isUnit u).map (Matrix.unitaryGroup ι ℂ).subtype

/-- The tensor product of two positive definite matrices is positive definite. -/
theorem tensor_posDef {a : Matrix ι ι ℂ} {b : Matrix κ κ ℂ}
    (ha : a.PosDef) (hb : b.PosDef) : (a ⊗ₖ b).PosDef := by
  have hab : a ⊗ₖ b = spectralLift (tensorUnitary ha.1.eigenvectorUnitary hb.1.eigenvectorUnitary)
      (fun x => ha.1.eigenvalues x.1 * hb.1.eigenvalues x.2) := by
    rw [← tensor_spectralLift, spectralLift_eigenvalues ha.1, spectralLift_eigenvalues hb.1]
  rw [hab]
  exact spectralLift_posDef _ _ (fun x => mul_pos (ha.eigenvalues_pos x.1) (hb.eigenvalues_pos x.2))

/-- The joint thermal state of a full-rank input is positive definite. -/
theorem thermalJoint_posDef [Nonempty κ] (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} (hrho : rho.PosDef) {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) :
    (thermalJoint u rho hh β).PosDef := by
  change ((u : Matrix (ι × κ) (ι × κ) ℂ) * (rho ⊗ₖ gibbsState hh β) *
    (u : Matrix (ι × κ) (ι × κ) ℂ).conjTranspose).PosDef
  apply Matrix.PosDef.mul_mul_conjTranspose_same (tensor_posDef hrho (gibbsState_posDef hh β))
  apply Matrix.vecMul_injective_of_isUnit
  exact (Group.isUnit u).map (Matrix.unitaryGroup (ι × κ) ℂ).subtype

/-- A full-rank system state is never erased exactly by one finite thermal operation: the
final system state keeps positive entropy, for every unitary, reservoir and temperature. -/
theorem no_exact_thermal_erasure [Nonempty κ] [Nontrivial ι] (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} (hrho : rho.PosDef) (htr : rho.trace = 1)
    {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) :
    0 < entropy (marginalLeft (thermalJoint u rho hh β)) := by
  have hpd := marginalLeft_posDef (thermalJoint_posDef u hrho hh β)
  have htr' : (marginalLeft (thermalJoint u rho hh β)).trace = 1 :=
    (marginalLeft_trace _).trans (thermalJoint_density u hrho.posSemidef htr hh β).2
  exact entropy_pos_of_posDef hpd htr'

/-- The fair merged pair as a density matrix. -/
def fairPair : Matrix Bool Bool ℂ := realDiagonal (fun _ : Bool => (1 : ℝ) / 2)

theorem fairPair_posDef : fairPair.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  simp

theorem fairPair_trace : fairPair.trace = 1 := by
  simp [fairPair, realDiagonal, Matrix.trace_diagonal]

/-- The fair pair carries log 2 nats of entropy. -/
theorem fairPair_entropy : entropy fairPair = Real.log 2 := by
  have hlift : spectralLift (1 : Matrix.unitaryGroup Bool ℂ) (fun _ : Bool => (1 : ℝ) / 2) =
      fairPair := by
    simp [spectralLift, rotate, fairPair]
  rw [← hlift, entropy_spectralLift]
  simp only [Fintype.sum_bool, Real.negMulLog, one_div, Real.log_inv]
  ring

/-- Erasing the fair pair in a finite bath leaves positive entropy, and the heat satisfies the
balance with that positive remainder: the Landauer value log 2 is approached and never reached. -/
theorem fair_pair_not_erased [Nonempty κ] (u : Matrix.unitaryGroup (Bool × κ) ℂ)
    {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) (hβ : 0 < β) :
    0 < entropy (marginalLeft (thermalJoint u fairPair hh β)) ∧
    (Real.log 2 - entropy (marginalLeft (thermalJoint u fairPair hh β))) / β ≤
      reservoirHeat u fairPair hh β ∧
    Real.log 2 - entropy (marginalLeft (thermalJoint u fairPair hh β)) < Real.log 2 := by
  have hpos := no_exact_thermal_erasure u fairPair_posDef fairPair_trace hh β
  refine ⟨hpos, ?_, by linarith⟩
  have hl := landauer_from_unitary u fairPair_posDef.posSemidef fairPair_trace hh β hβ
  rwa [fairPair_entropy] at hl

end

end Thermal

end OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
