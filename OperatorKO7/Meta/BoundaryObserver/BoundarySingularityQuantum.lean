import OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
import OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction

import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fintype

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.BoundarySingularity

open scoped BigOperators Classical

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

/-! ## Rank cannot decrease in a finite full-rank bath -/

/-- Unitary conjugation preserves the actual matrix rank. -/
theorem rank_rotate (u : Matrix.unitaryGroup ι ℂ) (a : Matrix ι ι ℂ) :
    (rotate u a).rank = a.rank := by
  have hle (v : Matrix.unitaryGroup ι ℂ) (b : Matrix ι ι ℂ) :
      (rotate v b).rank ≤ b.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  apply le_antisymm (hle u a)
  have hback : rotate (star u) (rotate u a) = a := by
    simp only [rotate, unitary.coe_star, star_star, mul_assoc,
      unitary.coe_star_mul_self, mul_one]
    rw [← mul_assoc, unitary.coe_star_mul_self, one_mul]
  simpa only [hback] using hle (star u) (rotate u a)

/-- The rank of an actual spectral lift counts its nonzero spectral entries. -/
theorem rank_spectralLift (u : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) :
    (spectralLift u p).rank = Fintype.card {i // p i ≠ 0} := by
  classical
  rw [spectralLift, rank_rotate, realDiagonal, Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by simp))

/-- Actual Kronecker rank multiplication for arbitrary Hermitian factors. -/
theorem rank_tensor {a : Matrix ι ι ℂ} {b : Matrix κ κ ℂ}
    (ha : a.IsHermitian) (hb : b.IsHermitian) :
    (a ⊗ₖ b).rank = a.rank * b.rank := by
  classical
  let p := ha.eigenvalues
  let q := hb.eigenvalues
  let e : {x : ι × κ // p x.1 * q x.2 ≠ 0} ≃
      {i // p i ≠ 0} × {r // q r ≠ 0} :=
    { toFun := fun x => ⟨⟨x.1.1, (mul_ne_zero_iff.mp x.2).1⟩,
        ⟨x.1.2, (mul_ne_zero_iff.mp x.2).2⟩⟩
      invFun := fun x => ⟨(x.1.1, x.2.1), mul_ne_zero x.1.2 x.2.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  calc
    (a ⊗ₖ b).rank =
        (spectralLift ha.eigenvectorUnitary p ⊗ₖ
          spectralLift hb.eigenvectorUnitary q).rank := by
            simp only [p, q, spectralLift_eigenvalues]
    _ = Fintype.card {x : ι × κ // p x.1 * q x.2 ≠ 0} := by
      rw [tensor_spectralLift, rank_spectralLift]
    _ = Fintype.card {i // p i ≠ 0} * Fintype.card {r // q r ≠ 0} :=
      (Fintype.card_congr e).trans (Fintype.card_prod _ _)
    _ = a.rank * b.rank := by
      rw [← rank_spectralLift ha.eigenvectorUnitary p,
        ← rank_spectralLift hb.eigenvectorUnitary q]
      simp only [p, q, spectralLift_eigenvalues]

/-- If all columns outside a predicate vanish, the matrix factors through the surviving columns. -/
theorem rank_le_card_of_columns (a : Matrix ι ι ℂ) (S : ι → Prop) [DecidablePred S]
    (hz : ∀ j, ¬ S j → ∀ i, a i j = 0) :
    a.rank ≤ Fintype.card {j // S j} := by
  classical
  let l : Matrix ι {j // S j} ℂ := fun i j => a i j.1
  let r : Matrix {j // S j} ι ℂ := fun j k => if j.1 = k then 1 else 0
  have heq : a = l * r := by
    ext i j
    symm
    by_cases hj : S j
    · rw [Matrix.mul_apply, Finset.sum_eq_single ⟨j, hj⟩]
      · simp [l, r]
      · intro k _ hkj
        have hk : k.1 ≠ j := fun h => hkj (Subtype.ext h)
        simp [r, hk]
      · simp
    · rw [Matrix.mul_apply, hz j hj i]
      apply Finset.sum_eq_zero
      intro k _
      have hk : k.1 ≠ j := fun h => hj (h ▸ k.2)
      simp [r, hk]
  rw [heq]
  exact (Matrix.rank_mul_le_left l r).trans (Matrix.rank_le_card_width l)

/-- A basis probability is the diagonal entry after the actual inverse basis rotation. -/
theorem diagonalLaw_eq_rotated_diagonal (a : Matrix ι ι ℂ)
    (u : Matrix.unitaryGroup ι ℂ) (j : ι) :
    diagonalLaw a u j = (rotate (star u) a j j).re := by
  let d := realDiagonal (fun i : ι => if i = j then 1 else 0)
  have ht : (a * ((u : Matrix ι ι ℂ) * d * star (u : Matrix ι ι ℂ))).trace =
      ((star (u : Matrix ι ι ℂ) * a * (u : Matrix ι ι ℂ)) * d).trace := by
    calc
      _ = (((a * (u : Matrix ι ι ℂ)) * d) * star (u : Matrix ι ι ℂ)).trace := by
        simp only [mul_assoc]
      _ = (star (u : Matrix ι ι ℂ) * ((a * (u : Matrix ι ι ℂ)) * d)).trace :=
        Matrix.trace_mul_comm _ _
      _ = _ := by simp only [mul_assoc]
  change (a * ((u : Matrix ι ι ℂ) * d * star (u : Matrix ι ι ℂ))).trace.re = _
  rw [ht]
  simp [d, realDiagonal, Matrix.trace, Matrix.diag, Matrix.mul_diagonal,
    rotate, unitary.coe_star]

/-- For every positive joint matrix, its rank is bounded by system marginal rank times
reservoir dimension. No normalization or nonempty-carrier premise is required. -/
theorem rank_le_marginalLeft_rank_mul {a : Matrix (ι × κ) (ι × κ) ℂ}
    (ha : a.PosSemidef) :
    a.rank ≤ (marginalLeft a).rank * Fintype.card κ := by
  classical
  have hm := marginalLeft_posSemidef ha
  let u := hm.1.eigenvectorUnitary
  let p := hm.1.eigenvalues
  let v := tensorUnitary u (1 : Matrix.unitaryGroup κ ℂ)
  let c := rotate (star v) a
  have hc : c.PosSemidef := rotate_posSemidef (star v) ha
  have hp (i : ι) : diagonalLaw (marginalLeft a) u i = p i := by
    rw [← spectralLift_eigenvalues hm.1, diagonalLaw_own_basis]
  have hz : ∀ j : ι × κ, ¬ p j.1 ≠ 0 → ∀ i, c i j = 0 := by
    intro j hj
    have hj0 : p j.1 = 0 := not_ne_iff.mp hj
    have hsum : (∑ r, diagonalLaw a v (j.1, r)) = 0 := by
      rw [diagonalLaw_marginalLeft, hp, hj0]
    have hjprob : diagonalLaw a v j = 0 := by
      have hle := Finset.single_le_sum
        (fun r _ => diagonalLaw_nonnegative ha v (j.1, r)) (Finset.mem_univ j.2)
      rw [hsum] at hle
      exact le_antisymm hle (diagonalLaw_nonnegative ha v j)
    have hre : (c j j).re = 0 := by
      rw [diagonalLaw_eq_rotated_diagonal] at hjprob
      exact hjprob
    have hnonneg := Complex.nonneg_iff.mp
      (BoundaryReconstruction.Operational.posSemidef_diag_nonneg hc j)
    have hjc : c j j = 0 := by
      apply Complex.ext
      · simpa using hre
      · simpa using hnonneg.2.symm
    exact psd_column_zero hc j hjc
  have hcard : Fintype.card {j : ι × κ // p j.1 ≠ 0} =
      Fintype.card {i // p i ≠ 0} * Fintype.card κ := by
    let e : {j : ι × κ // p j.1 ≠ 0} ≃ {i // p i ≠ 0} × κ :=
      { toFun := fun j => (⟨j.1.1, j.2⟩, j.1.2)
        invFun := fun j => ⟨(j.1.1, j.2), j.1.2⟩
        left_inv := by intro j; rfl
        right_inv := by intro j; rfl }
    exact (Fintype.card_congr e).trans (Fintype.card_prod _ _)
  calc
    a.rank = c.rank := (rank_rotate (star v) a).symm
    _ ≤ Fintype.card {j : ι × κ // p j.1 ≠ 0} :=
      rank_le_card_of_columns c (fun j => p j.1 ≠ 0) hz
    _ = Fintype.card {i // p i ≠ 0} * Fintype.card κ := hcard
    _ = (marginalLeft a).rank * Fintype.card κ := by
      rw [← rank_spectralLift u p]
      change (spectralLift hm.1.eigenvectorUnitary hm.1.eigenvalues).rank * _ = _
      rw [spectralLift_eigenvalues]

/-- Every finite unitary interaction obeys the exact input-support capacity bound. -/
theorem unitary_marginal_rank_capacity (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} {gamma : Matrix κ κ ℂ}
    (hrho : rho.PosSemidef) (hgamma : gamma.PosSemidef) :
    rho.rank * gamma.rank ≤
      (marginalLeft (rotate u (rho ⊗ₖ gamma))).rank * Fintype.card κ := by
  have h := rank_le_marginalLeft_rank_mul (rotate_posSemidef u (tensor_posSemidef hrho hgamma))
  rwa [rank_rotate, rank_tensor hrho.1 hgamma.1] at h

/-- A finite full-rank reservoir cannot lower the system rank. -/
theorem unitary_fullRank_bath_rank_nondecreasing [Nonempty κ]
    (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} {gamma : Matrix κ κ ℂ}
    (hrho : rho.PosSemidef) (hgamma : gamma.PosDef) :
    rho.rank ≤ (marginalLeft (rotate u (rho ⊗ₖ gamma))).rank := by
  have h := unitary_marginal_rank_capacity u hrho hgamma.posSemidef
  rw [Matrix.rank_of_isUnit gamma hgamma.isUnit] at h
  have hk : 0 < Fintype.card κ := Fintype.card_pos
  nlinarith

/-- The rank obstruction applies to every mixed input, including rank-deficient density matrices. -/
theorem thermal_rank_nondecreasing [Nonempty κ]
    (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef)
    {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) :
    rho.rank ≤ (marginalLeft (thermalJoint u rho hh β)).rank :=
  unitary_fullRank_bath_rank_nondecreasing u hrho (gibbsState_posDef hh β)

theorem no_exact_mixed_thermal_erasure [Nonempty κ]
    (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef) (hmixed : 1 < rho.rank)
    {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) :
    1 < (marginalLeft (thermalJoint u rho hh β)).rank :=
  hmixed.trans_le (thermal_rank_nondecreasing u hrho hh β)


/-- A normalized positive matrix of rank at least two has strictly positive spectral entropy. -/
theorem entropy_pos_of_rank_gt_one {a : Matrix ι ι ℂ}
    (ha : a.PosSemidef) (htr : a.trace = 1) (hrank : 1 < a.rank) :
    0 < entropy a := by
  classical
  let p := ha.1.eigenvalues
  have hp0 (i : ι) : 0 ≤ p i := ha.eigenvalues_nonneg i
  have hsum : (∑ i, p i) = 1 := by
    rw [eigenvalues_sum_trace ha.1, htr]
    simp
  have hp1 (i : ι) : p i ≤ 1 := by
    have h := Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
    rwa [hsum] at h
  have hcard : 1 < Fintype.card {i // p i ≠ 0} := by
    rw [← rank_spectralLift ha.1.eigenvectorUnitary p]
    simpa only [p, spectralLift_eigenvalues] using hrank
  have hc : 1 < (Finset.univ : Finset {i // p i ≠ 0}).card := by
    simpa only [Finset.card_univ] using hcard
  obtain ⟨i, _, j, _, hij⟩ := Finset.one_lt_card.mp hc
  have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
  have hi0 : 0 < p i.1 := lt_of_le_of_ne (hp0 i.1) (Ne.symm i.2)
  have hj0 : 0 < p j.1 := lt_of_le_of_ne (hp0 j.1) (Ne.symm j.2)
  have hpair : p i.1 + p j.1 ≤ 1 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i.1, j.1} : Finset ι)) (fun k _ _ => hp0 k)
    rwa [Finset.sum_pair hij', hsum] at h
  have hi1 : p i.1 < 1 := by linarith
  have hterm : 0 < Real.negMulLog (p i.1) := by
    simp only [Real.negMulLog]
    exact mul_pos_of_neg_of_neg (by linarith) (Real.log_neg hi0 hi1)
  have hle : Real.negMulLog (p i.1) ≤ ∑ k, Real.negMulLog (p k) :=
    Finset.single_le_sum (fun k _ => Real.negMulLog_nonneg (hp0 k) (hp1 k))
      (Finset.mem_univ i.1)
  rw [entropy_eq_eigenvalues ha.1]
  exact hterm.trans_le hle

/-- Every mixed density input keeps positive entropy after a finite full-rank thermal interaction,
including inputs that are not positive definite. -/
theorem no_exact_mixed_thermal_erasure_entropy [Nonempty κ]
    (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef) (htr : rho.trace = 1)
    (hmixed : 1 < rho.rank) {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) :
    0 < entropy (marginalLeft (thermalJoint u rho hh β)) := by
  have hd := thermalJoint_density u hrho htr hh β
  exact entropy_pos_of_rank_gt_one (marginalLeft_posSemidef hd.1)
    ((marginalLeft_trace _).trans hd.2) (no_exact_mixed_thermal_erasure u hrho hmixed hh β)

#check @entropy_pos_of_rank_gt_one
#print axioms entropy_pos_of_rank_gt_one
#check @no_exact_mixed_thermal_erasure_entropy
#print axioms no_exact_mixed_thermal_erasure_entropy

#check @rank_rotate
#print axioms rank_rotate
#check @rank_spectralLift
#print axioms rank_spectralLift
#check @rank_tensor
#print axioms rank_tensor
#check @rank_le_card_of_columns
#print axioms rank_le_card_of_columns
#check @diagonalLaw_eq_rotated_diagonal
#print axioms diagonalLaw_eq_rotated_diagonal
#check @rank_le_marginalLeft_rank_mul
#print axioms rank_le_marginalLeft_rank_mul
#check @unitary_marginal_rank_capacity
#print axioms unitary_marginal_rank_capacity
#check @unitary_fullRank_bath_rank_nondecreasing
#print axioms unitary_fullRank_bath_rank_nondecreasing
#check @thermal_rank_nondecreasing
#print axioms thermal_rank_nondecreasing
#check @no_exact_mixed_thermal_erasure
#print axioms no_exact_mixed_thermal_erasure

/-! ## Exact Gibbs equality and strict finite-reservoir heat

Equality is recovered from
the same unitary-overlap residual that proves the native entropy inequality.
-/

/-- The scalar Gibbs bound is tight exactly when the two supported masses coincide. -/
theorem gibbs_term_eq_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b = 0 → a = 0) :
    Real.negMulLog a + a * Real.log b = b - a ↔ a = b := by
  constructor
  · intro he
    by_cases ha0 : a = 0
    · subst a
      simpa [Real.negMulLog] using he
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb0 : b ≠ 0 := fun h => ha0 (hab h)
      have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      by_contra hne
      have hratio : b / a ≠ 1 := by
        intro h
        apply hne
        have h' := (div_eq_iff ha0).mp h
        simpa using h'.symm
      have hl := Real.log_lt_sub_one_of_pos (div_pos hbp hap) hratio
      have hm := mul_lt_mul_of_pos_left hl hap
      have hs : a * Real.log (b / a) = a * Real.log b - a * Real.log a := by
        rw [Real.log_div hb0 ha0]
        ring
      have hr : a * (b / a - 1) = b - a := by field_simp
      rw [hs, hr] at hm
      simp only [Real.negMulLog] at he
      linarith
  · rintro rfl
    simp [Real.negMulLog]

/-- One nonnegative term in the actual relative-eigenbasis residual. -/
def weightedGibbsResidual (t : Matrix.unitaryGroup ι ℂ) (p q : ι → ℝ)
    (i j : ι) : ℝ :=
  basisWeight (t : Matrix ι ι ℂ) i j *
    (q j - p i - (Real.negMulLog (p i) + p i * Real.log (q j)))

theorem weightedGibbsResidual_nonnegative (t : Matrix.unitaryGroup ι ℂ)
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hs : ∀ i j, q j = 0 → p i * basisWeight (t : Matrix ι ι ℂ) i j = 0)
    (i j : ι) : 0 ≤ weightedGibbsResidual t p q i j := by
  by_cases hw : basisWeight (t : Matrix ι ι ℂ) i j = 0
  · simp [weightedGibbsResidual, hw]
  · have hab : q j = 0 → p i = 0 :=
      fun h => (mul_eq_zero.mp (hs i j h)).resolve_right hw
    exact mul_nonneg (basisWeight_nonneg _ i j)
      (sub_nonneg.mpr (OperatorKO7.Meta.ReverseBridge.QMLaw_EntropyLaws.gibbs_term
        (p i) (q j) (hp i) (hq j) hab))

/-- The sum of the scalar residuals equals the native spectral entropy difference. -/
theorem weightedGibbsResidual_sum (t : Matrix.unitaryGroup ι ℂ) (p q : ι → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) :
    (∑ i, ∑ j, weightedGibbsResidual t p q i j) =
      -(∑ i, Real.negMulLog (p i)) -
        ∑ i, ∑ j, p i * Real.log (q j) * basisWeight (t : Matrix ι ι ℂ) i j := by
  have hpsum : (∑ i, ∑ j, basisWeight (t : Matrix ι ι ℂ) i j * p i) = 1 := by
    simp_rw [← Finset.sum_mul, basisWeight_row_sum, one_mul]
    exact hp
  have hqsum : (∑ i, ∑ j, basisWeight (t : Matrix ι ι ℂ) i j * q j) = 1 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, basisWeight_col_sum, one_mul]
    exact hq
  have hentropy :
      (∑ i, ∑ j, basisWeight (t : Matrix ι ι ℂ) i j * Real.negMulLog (p i)) =
        ∑ i, Real.negMulLog (p i) := by
    simp_rw [← Finset.sum_mul, basisWeight_row_sum, one_mul]
  have hcross :
      (∑ i, ∑ j, basisWeight (t : Matrix ι ι ℂ) i j * (p i * Real.log (q j))) =
        ∑ i, ∑ j, p i * Real.log (q j) * basisWeight (t : Matrix ι ι ℂ) i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  unfold weightedGibbsResidual
  simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hqsum, hpsum, hentropy, hcross]
  ring

/-- Zero total residual forces equal masses at every nonzero unitary overlap. -/
theorem weightedGibbsResidual_zero_match (t : Matrix.unitaryGroup ι ℂ)
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hs : ∀ i j, q j = 0 → p i * basisWeight (t : Matrix ι ι ℂ) i j = 0)
    (hz : ∑ i, ∑ j, weightedGibbsResidual t p q i j = 0)
    (i j : ι) (hw : basisWeight (t : Matrix ι ι ℂ) i j ≠ 0) : p i = q j := by
  have hn := weightedGibbsResidual_nonnegative t p q hp hq hs
  have hinner : weightedGibbsResidual t p q i j ≤
      ∑ k, weightedGibbsResidual t p q i k :=
    Finset.single_le_sum (fun k _ => hn i k) (Finset.mem_univ j)
  have houter : (∑ k, weightedGibbsResidual t p q i k) ≤
      ∑ l, ∑ k, weightedGibbsResidual t p q l k :=
    Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => hn l k))
      (Finset.mem_univ i)
  have hzero : weightedGibbsResidual t p q i j = 0 :=
    le_antisymm ((hinner.trans houter).trans_eq hz) (hn i j)
  have hterm := (mul_eq_zero.mp hzero).resolve_left hw
  have hab : q j = 0 → p i = 0 :=
    fun h => (mul_eq_zero.mp (hs i j h)).resolve_right hw
  exact (gibbs_term_eq_iff (p i) (q j) (hp i) (hq j) hab).mp
    (sub_eq_zero.mp hterm).symm

omit [Fintype ι] [DecidableEq ι] in
theorem basisWeight_eq_zero_iff (t : Matrix ι ι ℂ) (i j : ι) :
    basisWeight t i j = 0 ↔ t i j = 0 := by
  simp [basisWeight, Complex.mul_conj]

/-- Overlap equality intertwines the actual spectral matrices, not only their spectra. -/
theorem spectralLift_eq_of_overlap (u v : Matrix.unitaryGroup ι ℂ) (p q : ι → ℝ)
    (hmatch : ∀ i j,
      basisWeight (star (u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)) i j ≠ 0 →
        p i = q j) : spectralLift u p = spectralLift v q := by
  let t : Matrix ι ι ℂ := star (u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)
  have hi : realDiagonal p * t = t * realDiagonal q := by
    ext i j
    simp only [realDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases ht : t i j = 0
    · simp [ht]
    · have hw : basisWeight t i j ≠ 0 :=
        fun h => ht ((basisWeight_eq_zero_iff t i j).mp h)
      rw [hmatch i j hw]
      ring
  have hu : (u : Matrix ι ι ℂ) * star (u : Matrix ι ι ℂ) = 1 := u.property.2
  have hv : (v : Matrix ι ι ℂ) * star (v : Matrix ι ι ℂ) = 1 := v.property.2
  have hl : (u : Matrix ι ι ℂ) * (realDiagonal p * t) * star (v : Matrix ι ι ℂ) =
      spectralLift u p := by
    simp only [t, spectralLift, rotate, mul_assoc, hv, mul_one]
  have hr : (u : Matrix ι ι ℂ) * (t * realDiagonal q) * star (v : Matrix ι ι ℂ) =
      spectralLift v q := by
    simp only [t, spectralLift, rotate, ← mul_assoc, hu, one_mul]
  exact hl.symm.trans ((congrArg
    (fun a => (u : Matrix ι ι ℂ) * a * star (v : Matrix ι ι ℂ)) hi).trans hr)

/-- Quantum relative entropy vanishes exactly at equality of supported density matrices. -/
theorem relativeEntropy_eq_zero_iff {a b : Matrix ι ι ℂ}
    (ha : a.PosSemidef) (hb : b.PosSemidef) (hta : a.trace = 1) (htb : b.trace = 1)
    (hker : SupportLE a b) : relativeEntropy a b = 0 ↔ a = b := by
  constructor
  · intro hzero
    let u := ha.1.eigenvectorUnitary
    let v := hb.1.eigenvectorUnitary
    let p := ha.1.eigenvalues
    let q := hb.1.eigenvalues
    have hpa : spectralLift u p = a := spectralLift_eigenvalues ha.1
    have hqb : spectralLift v q = b := spectralLift_eigenvalues hb.1
    have hp1 : (∑ i, p i) = 1 :=
      (eigenvalues_sum_trace ha.1).trans (congrArg Complex.re hta)
    have hq1 : (∑ i, q i) = 1 :=
      (eigenvalues_sum_trace hb.1).trans (congrArg Complex.re htb)
    have hk : SupportLE (spectralLift u p) (spectralLift v q) := by
      simpa only [hpa, hqb] using hker
    have hs : ∀ i j, q j = 0 →
        p i * basisWeight ((star u * v : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) i j = 0 :=
      fun i j h => support_spectral_weights u v p q hk i j h
    have hz : ∑ i, ∑ j, weightedGibbsResidual (star u * v) p q i j = 0 := by
      rw [weightedGibbsResidual_sum _ _ _ hp1 hq1]
      change -(∑ i, Real.negMulLog (p i)) -
        (∑ i, ∑ j, p i * Real.log (q j) *
          basisWeight (star (u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)) i j) = 0
      rw [← relativeEntropy_spectralLift u v p q, hpa, hqb]
      exact hzero
    have hm := weightedGibbsResidual_zero_match (star u * v) p q
      (fun i => ha.eigenvalues_nonneg i) (fun i => hb.eigenvalues_nonneg i) hs hz
    exact hpa.symm.trans ((spectralLift_eq_of_overlap u v p q hm).trans hqb)
  · rintro rfl
    simp [relativeEntropy]

/-- Heat reaches the Landauer lower bound exactly when both actual remainders vanish. -/
theorem thermal_heat_eq_iff_remainders [Nonempty κ] (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef) (htr : rho.trace = 1)
    {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) (hβ : 0 < β) :
    reservoirHeat u rho hh β =
      (entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) / β ↔
    mutualInfo (thermalJoint u rho hh β) = 0 ∧
      relativeEntropy (marginalRight (thermalJoint u rho hh β)) (gibbsState hh β) = 0 := by
  obtain ⟨hb, hi, hd⟩ := thermal_information_balance u hrho htr hh β
  constructor
  · intro he
    have he' := (eq_div_iff hβ.ne').mp he
    constructor <;> nlinarith
  · rintro ⟨hi0, hd0⟩
    apply (eq_div_iff hβ.ne').mpr
    rw [hi0, hd0] at hb
    nlinarith

/-- The finite-bath equality case has unchanged reservoir state and zero entropy decrease. -/
theorem thermal_heat_eq_iff_unchanged [Nonempty κ] (u : Matrix.unitaryGroup (ι × κ) ℂ)
    {rho : Matrix ι ι ℂ} (hrho : rho.PosSemidef) (htr : rho.trace = 1)
    {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) (hβ : 0 < β) :
    reservoirHeat u rho hh β =
      (entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) / β ↔
    marginalRight (thermalJoint u rho hh β) = gibbsState hh β ∧
      entropy rho - entropy (marginalLeft (thermalJoint u rho hh β)) = 0 := by
  have hdensity := thermalJoint_density u hrho htr hh β
  have heq := relativeEntropy_eq_zero_iff (marginalRight_posSemidef hdensity.1)
    (gibbsState_posDef hh β).posSemidef
    ((marginalRight_trace _).trans hdensity.2) (gibbsState_trace hh β)
    (support_gibbsState hh β _)
  constructor
  · intro hheat
    have hz := (thermal_heat_eq_iff_remainders u hrho htr hh β hβ).mp hheat
    have hres := heq.mp hz.2
    refine ⟨hres, ?_⟩
    have hQ : reservoirHeat u rho hh β = 0 := by
      simp [reservoirHeat, hres, meanEnergy]
    have hp := (eq_div_iff hβ.ne').mp hheat
    rw [hQ, zero_mul] at hp
    exact hp.symm
  · rintro ⟨hres, hs⟩
    simp [reservoirHeat, hres, meanEnergy, hs]

/-- Every positive entropy decrease has strictly greater finite Gibbs-bath heat cost. -/
theorem thermal_heat_strict_of_entropy_decrease [Nonempty κ]
    (u : Matrix.unitaryGroup (ι × κ) ℂ) {rho : Matrix ι ι ℂ}
    (hrho : rho.PosSemidef) (htr : rho.trace = 1)
    {h : Matrix κ κ ℂ} (hh : h.IsHermitian) (β : ℝ) (hβ : 0 < β)
    (hdrop : 0 < entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) :
    (entropy rho - entropy (marginalLeft (thermalJoint u rho hh β))) / β <
      reservoirHeat u rho hh β := by
  have hle := landauer_from_unitary u hrho htr hh β hβ
  apply lt_of_le_of_ne hle
  intro he
  have hz := (thermal_heat_eq_iff_unchanged u hrho htr hh β hβ).mp he.symm
  linarith [hz.2]

#check @gibbs_term_eq_iff
#print axioms gibbs_term_eq_iff
#check @weightedGibbsResidual
#print axioms weightedGibbsResidual
#check @weightedGibbsResidual_nonnegative
#print axioms weightedGibbsResidual_nonnegative
#check @weightedGibbsResidual_sum
#print axioms weightedGibbsResidual_sum
#check @weightedGibbsResidual_zero_match
#print axioms weightedGibbsResidual_zero_match
#check @basisWeight_eq_zero_iff
#print axioms basisWeight_eq_zero_iff
#check @spectralLift_eq_of_overlap
#print axioms spectralLift_eq_of_overlap
#check @relativeEntropy_eq_zero_iff
#print axioms relativeEntropy_eq_zero_iff
#check @thermal_heat_eq_iff_remainders
#print axioms thermal_heat_eq_iff_remainders
#check @thermal_heat_eq_iff_unchanged
#print axioms thermal_heat_eq_iff_unchanged
#check @thermal_heat_strict_of_entropy_decrease
#print axioms thermal_heat_strict_of_entropy_decrease


/-! ## Exact finite-reservoir reset capacity

The unitary below is constructed
from the actual spectral support. No energy-conservation or bath-return
constraint is imposed.
-/

/-- A pure coordinate density matrix. -/
def resetBasis (i₀ : ι) : Matrix ι ι ℂ :=
  realDiagonal (fun i => if i = i₀ then 1 else 0)

theorem resetBasis_posSemidef (i₀ : ι) : (resetBasis i₀).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  apply Complex.zero_le_real.mpr
  by_cases hi : i = i₀ <;> simp [hi]

theorem resetBasis_trace (i₀ : ι) : (resetBasis i₀).trace = 1 := by
  rw [resetBasis, realDiagonal, Matrix.trace_diagonal]
  simp [apply_ite]

theorem resetBasis_rank (i₀ : ι) : (resetBasis i₀).rank = 1 := by
  simp [resetBasis, realDiagonal, Matrix.rank_diagonal]

/-- The native row-permutation matrix, with both unitary equations proved. -/
def resetPermutationUnitary (σ : Equiv.Perm ι) : Matrix.unitaryGroup ι ℂ := by
  refine ⟨σ.permMatrix ℂ, ?_, ?_⟩
  · change (σ.permMatrix ℂ).conjTranspose * σ.permMatrix ℂ = 1
    rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [Matrix.submatrix, Matrix.one_apply]
  · change σ.permMatrix ℂ * (σ.permMatrix ℂ).conjTranspose = 1
    rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [Matrix.submatrix, Matrix.one_apply]

theorem resetPermutation_rotate (σ : Equiv.Perm ι) (a : Matrix ι ι ℂ) :
    rotate (resetPermutationUnitary σ) a = a.submatrix σ σ := by
  change σ.permMatrix ℂ * a * (σ.permMatrix ℂ).conjTranspose = _
  rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem resetPermutation_spectrum (σ : Equiv.Perm ι) (p : ι → ℝ) :
    rotate (resetPermutationUnitary σ) (realDiagonal p) =
      realDiagonal (p ∘ σ) := by
  rw [resetPermutation_rotate]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [realDiagonal]
  · have hσ : σ i ≠ σ j := fun h => hij (σ.injective h)
    simp [realDiagonal, hij, hσ]

/-- Actual unitary composition on every matrix. -/
theorem reset_rotate_mul (u v : Matrix.unitaryGroup ι ℂ) (a : Matrix ι ι ℂ) :
    rotate (u * v) a = rotate u (rotate v a) := by
  change ((u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)) * a *
    star ((u : Matrix ι ι ℂ) * (v : Matrix ι ι ℂ)) =
      (u : Matrix ι ι ℂ) * ((v : Matrix ι ι ℂ) * a * star (v : Matrix ι ι ℂ)) *
        star (u : Matrix ι ι ℂ)
  rw [Matrix.star_mul]
  noncomm_ring

theorem reset_rotate_inverse (u : Matrix.unitaryGroup ι ℂ) (a : Matrix ι ι ℂ) :
    rotate (star u) (rotate u a) = a := by
  have hu : star (u : Matrix ι ι ℂ) * (u : Matrix ι ι ℂ) = 1 := u.property.1
  change star (u : Matrix ι ι ℂ) *
    ((u : Matrix ι ι ℂ) * a * star (u : Matrix ι ι ℂ)) *
      star (star (u : Matrix ι ι ℂ)) = a
  rw [star_star]
  calc
    _ = (star (u : Matrix ι ι ℂ) * (u : Matrix ι ι ℂ)) * a *
      (star (u : Matrix ι ι ℂ) * (u : Matrix ι ι ℂ)) := by noncomm_ring
    _ = a := by rw [hu, one_mul, mul_one]

/-- T7: the support cardinal comes from the matrix's own spectral theorem. -/
theorem spectralSupport_card {a : Matrix ι ι ℂ} (ha : a.IsHermitian) :
    Fintype.card {i // ha.eigenvalues i ≠ 0} = a.rank := by
  rw [← rank_spectralLift ha.eigenvectorUnitary ha.eigenvalues,
    spectralLift_eigenvalues]

/-- T8: fitting spectral support can be moved into one fixed system sector. -/
theorem reset_support_permutation (p : ι × κ → ℝ) (i₀ : ι)
    (hcap : Fintype.card {x // p x ≠ 0} ≤ Fintype.card κ) :
    ∃ σ : Equiv.Perm (ι × κ), ∀ x, p x ≠ 0 → (σ x).1 = i₀ := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcap
  let j : {x // p x ≠ 0} ↪ ι × κ :=
    { toFun := fun x => (i₀, f x)
      inj' := by
        intro x y h
        exact f.injective (congrArg Prod.snd h) }
  let e := Equiv.ofInjective j j.injective
  refine ⟨e.extendSubtype, ?_⟩
  intro x hx
  rw [Equiv.extendSubtype_apply_of_mem e x hx]
  rfl

/-- A diagonal state supported in one sector has that pure marginal. -/
theorem marginalLeft_sector_diagonal (p : ι × κ → ℝ) (i₀ : ι)
    (hz : ∀ i, i ≠ i₀ → ∀ r, p (i, r) = 0)
    (htr : (realDiagonal p).trace = 1) :
    marginalLeft (realDiagonal p) = resetBasis i₀ := by
  have hsum : (∑ i, ∑ r, (p (i, r) : ℂ)) = 1 := by
    simpa only [realDiagonal, Matrix.trace_diagonal, Fintype.sum_prod_type] using htr
  have hsector : (∑ r, (p (i₀, r) : ℂ)) = 1 := by
    rw [Finset.sum_eq_single i₀] at hsum
    · exact hsum
    · intro i _ hi
      simp [hz i hi]
    · simp
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = i₀
    · subst i
      simpa only [marginalLeft, realDiagonal, Matrix.diagonal_apply_eq,
        resetBasis, if_pos rfl] using hsector
    · simp [marginalLeft, realDiagonal, resetBasis, hi, hz i hi]
  · have hpair (r : κ) : (i, r) ≠ (j, r) := fun h => hij (congrArg Prod.fst h)
    simp [marginalLeft, realDiagonal, resetBasis, hij, hpair]

/-- T9: an actual joint unitary resets the marginal whenever the rank fits. -/
theorem exists_basis_reset_of_rank {a : Matrix (ι × κ) (ι × κ) ℂ}
    (ha : a.IsHermitian) (htr : a.trace = 1) (i₀ : ι)
    (hcap : a.rank ≤ Fintype.card κ) :
    ∃ u : Matrix.unitaryGroup (ι × κ) ℂ,
      marginalLeft (rotate u a) = resetBasis i₀ := by
  classical
  let p := ha.eigenvalues
  have hc : Fintype.card {x // p x ≠ 0} ≤ Fintype.card κ :=
    (spectralSupport_card ha).trans_le hcap
  obtain ⟨σ, hσ⟩ := reset_support_permutation p i₀ hc
  let u := resetPermutationUnitary σ.symm * star ha.eigenvectorUnitary
  have hdiag : rotate u a = realDiagonal (p ∘ σ.symm) := by
    rw [show a = spectralLift ha.eigenvectorUnitary p from
      (spectralLift_eigenvalues ha).symm]
    change rotate (resetPermutationUnitary σ.symm * star ha.eigenvectorUnitary)
      (rotate ha.eigenvectorUnitary (realDiagonal p)) = _
    rw [reset_rotate_mul, reset_rotate_inverse, resetPermutation_spectrum]
  refine ⟨u, ?_⟩
  rw [hdiag]
  apply marginalLeft_sector_diagonal (p ∘ σ.symm) i₀
  · intro i hi r
    by_contra hp
    have h := hσ (σ.symm (i, r)) hp
    exact hi (by simpa using h)
  · rw [← hdiag, rotate_trace, htr]

omit [DecidableEq ι] in
theorem marginalLeft_mul_local_left (u : Matrix ι ι ℂ)
    (a : Matrix (ι × κ) (ι × κ) ℂ) :
    marginalLeft ((u ⊗ₖ (1 : Matrix κ κ ℂ)) * a) = u * marginalLeft a := by
  ext i j
  simp only [marginalLeft, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.mul_sum]
  exact Finset.sum_comm

omit [DecidableEq ι] in
theorem marginalLeft_mul_local_right (a : Matrix (ι × κ) (ι × κ) ℂ)
    (u : Matrix ι ι ℂ) :
    marginalLeft (a * (u ⊗ₖ (1 : Matrix κ κ ℂ))) = marginalLeft a * u := by
  ext i j
  simp only [marginalLeft, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
  exact Finset.sum_comm

/-- T10: native partial trace commutes with local system-unitary conjugation. -/
theorem marginalLeft_local_rotate (u : Matrix.unitaryGroup ι ℂ)
    (a : Matrix (ι × κ) (ι × κ) ℂ) :
    marginalLeft (rotate (tensorUnitary u (1 : Matrix.unitaryGroup κ ℂ)) a) =
      rotate u (marginalLeft a) := by
  change marginalLeft (((u : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix κ κ ℂ)) * a *
    star ((u : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix κ κ ℂ))) = _
  rw [star_tensor, star_one, marginalLeft_mul_local_right, marginalLeft_mul_local_left]
  rfl

/-- Every normalized rank-one positive state is an actual rotated coordinate state. -/
theorem rank_one_density_representation {a : Matrix ι ι ℂ}
    (ha : a.PosSemidef) (htr : a.trace = 1) (hrank : a.rank = 1) :
    ∃ i₀ : ι, rotate ha.1.eigenvectorUnitary (resetBasis i₀) = a := by
  classical
  let p := ha.1.eigenvalues
  have hs : (∑ i, p i) = 1 := by
    rw [eigenvalues_sum_trace ha.1, htr]
    simp
  have hc : Fintype.card {i // p i ≠ 0} ≤ 1 := by
    rw [spectralSupport_card ha.1, hrank]
  have he : ∃ i, p i ≠ 0 := by
    by_contra! h
    have hz : (∑ i, p i) = 0 := by simp [h]
    linarith
  obtain ⟨i₀, hi₀⟩ := he
  have hz (i : ι) (hi : i ≠ i₀) : p i = 0 := by
    by_contra hp
    have heq : (⟨i, hp⟩ : {i // p i ≠ 0}) = ⟨i₀, hi₀⟩ :=
      (Fintype.card_le_one_iff.mp hc) _ _
    exact hi (congrArg Subtype.val heq)
  have hone : p i₀ = 1 := by
    rw [Finset.sum_eq_single i₀] at hs
    · exact hs
    · intro i _ hi
      exact hz i hi
    · simp
  have hp : p = fun i => if i = i₀ then 1 else 0 := by
    funext i
    by_cases hi : i = i₀
    · subst i
      simp [hone]
    · simp [hi, hz i hi]
  refine ⟨i₀, ?_⟩
  change spectralLift ha.1.eigenvectorUnitary (fun i => if i = i₀ then 1 else 0) = a
  rw [← hp]
  exact spectralLift_eigenvalues ha.1

/-- T10 sufficiency for every specified pure target, with no choice of basis in the statement. -/
theorem exists_pure_reset_of_rank {a : Matrix (ι × κ) (ι × κ) ℂ}
    (ha : a.IsHermitian) (htr : a.trace = 1)
    {target : Matrix ι ι ℂ} (htarget : target.PosSemidef)
    (htrace : target.trace = 1) (hrank : target.rank = 1)
    (hcap : a.rank ≤ Fintype.card κ) :
    ∃ u : Matrix.unitaryGroup (ι × κ) ℂ,
      marginalLeft (rotate u a) = target := by
  obtain ⟨i₀, hi₀⟩ := rank_one_density_representation htarget htrace hrank
  obtain ⟨v, hv⟩ := exists_basis_reset_of_rank ha htr i₀ hcap
  refine ⟨tensorUnitary htarget.1.eigenvectorUnitary 1 * v, ?_⟩
  rw [reset_rotate_mul, marginalLeft_local_rotate, hv, hi₀]

/-- T11: exact reset of a finite product density is equivalent to support capacity. -/
theorem exact_reset_iff_rank_capacity {rho : Matrix ι ι ℂ} {gamma : Matrix κ κ ℂ}
    (hrho : rho.PosSemidef) (hgamma : gamma.PosSemidef)
    (htrho : rho.trace = 1) (htgamma : gamma.trace = 1)
    {target : Matrix ι ι ℂ} (htarget : target.PosSemidef)
    (htarget_trace : target.trace = 1) (htarget_rank : target.rank = 1) :
    (∃ u : Matrix.unitaryGroup (ι × κ) ℂ,
      marginalLeft (rotate u (rho ⊗ₖ gamma)) = target) ↔
        rho.rank * gamma.rank ≤ Fintype.card κ := by
  constructor
  · rintro ⟨u, hu⟩
    have h := unitary_marginal_rank_capacity u hrho hgamma
    rwa [hu, htarget_rank, one_mul] at h
  · intro hcap
    have ht : (rho ⊗ₖ gamma).trace = 1 := by
      rw [Matrix.trace_kronecker, htrho, htgamma, mul_one]
    have hr : (rho ⊗ₖ gamma).rank ≤ Fintype.card κ := by
      rwa [rank_tensor hrho.1 hgamma.1]
    exact exists_pure_reset_of_rank (tensor_posSemidef hrho hgamma).1
      ht htarget htarget_trace htarget_rank hr


#check @resetBasis
#print axioms resetBasis
#check @resetBasis_posSemidef
#print axioms resetBasis_posSemidef
#check @resetBasis_trace
#print axioms resetBasis_trace
#check @resetBasis_rank
#print axioms resetBasis_rank
#check @resetPermutationUnitary
#print axioms resetPermutationUnitary
#check @resetPermutation_rotate
#print axioms resetPermutation_rotate
#check @resetPermutation_spectrum
#print axioms resetPermutation_spectrum
#check @reset_rotate_mul
#print axioms reset_rotate_mul
#check @reset_rotate_inverse
#print axioms reset_rotate_inverse
#check @spectralSupport_card
#print axioms spectralSupport_card
#check @reset_support_permutation
#print axioms reset_support_permutation
#check @marginalLeft_sector_diagonal
#print axioms marginalLeft_sector_diagonal
#check @exists_basis_reset_of_rank
#print axioms exists_basis_reset_of_rank
#check @marginalLeft_mul_local_left
#print axioms marginalLeft_mul_local_left
#check @marginalLeft_mul_local_right
#print axioms marginalLeft_mul_local_right
#check @marginalLeft_local_rotate
#print axioms marginalLeft_local_rotate
#check @rank_one_density_representation
#print axioms rank_one_density_representation
#check @exists_pure_reset_of_rank
#print axioms exists_pure_reset_of_rank
#check @exact_reset_iff_rank_capacity
#print axioms exact_reset_iff_rank_capacity

end

end Thermal

end OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
